"""Exact CP-SAT solver for the problem in docs/problem.md.

Objective (lexicographic): (1) total excess length, (2) number of track tiles.

Model, per (port, candidate city) pair:
  * A unit flow from port to city over a *corridor*: cells u with
    d_p(u) + d_c(u) <= d(p, c) + slack. Its arc count is the pair's path length.
    (Interior cells must be free; other terminals are never entered.)
  * Flow conservation with in-flow <= 1 per cell. Stray cycles are allowed by the
    constraints but only ever add length and tiles, so no optimum contains one; the
    verifier measures real network distances anyway.

Exactness: `solve` starts with a small slack and doubles it until the phase-1 optimum
X satisfies X <= slack. Any solution at least as good has every pair's excess <= X
<= slack, so it lies inside the corridors, and the corridor optimum is the global one.

Phase 1 minimises excess; phase 2 fixes that excess and minimises tiles.
"""
from __future__ import annotations

import collections
import time

from ortools.sat.python import cp_model

from network_solver.distances import PortRequirement, bfs, requirements
from network_solver.instance import Cell, Instance, Solution


def _corridor_arcs(instance: Instance, pcell: Cell, ccell: Cell, d: int, slack: int,
                   dist_from_port: dict[Cell, int]) -> list[tuple[Cell, Cell]]:
    dist_from_city = bfs(instance, ccell)
    budget = d + slack

    def inside(u: Cell) -> bool:
        if u not in (pcell, ccell) and not instance.is_free(u):
            return False
        return dist_from_port.get(u, budget + 1) + dist_from_city.get(u, budget + 1) <= budget

    arcs = []
    for u in dist_from_port:
        if u == ccell or not inside(u):
            continue
        for v in instance.neighbours(u):
            if v != pcell and inside(v):
                arcs.append((u, v))
    return arcs


def _build(instance: Instance, reqs: dict[str, PortRequirement], slack: int):
    model = cp_model.CpModel()
    select: dict[tuple[str, str], cp_model.IntVar] = {}
    excess_terms = []
    detours = []
    arcs_on_edge: dict[frozenset, list] = collections.defaultdict(list)

    for port, req in reqs.items():
        pcell = instance.ports[port]
        dist_from_port = bfs(instance, pcell)
        for city in req.candidates:
            ccell = instance.cities[city]
            d = req.distance[city]
            s = model.new_bool_var(f"sel[{port},{city}]")
            select[(port, city)] = s
            if city in req.required:
                model.add(s == 1)
            arcs = _corridor_arcs(instance, pcell, ccell, d, slack, dist_from_port)
            dag = set(_corridor_arcs(instance, pcell, ccell, d, 0, dist_from_port))
            dag = {(u, v) for u, v in dag
                   if dist_from_port[v] == dist_from_port[u] + 1}
            x = {a: model.new_bool_var("") for a in arcs}
            # Any arc off the shortest-path DAG makes the path strictly longer, and on a
            # grid (bipartite) by at least 2. This lets the solver pin most pairs to
            # their DAG once the total excess is known.
            detour = model.new_bool_var("")
            detours.append(detour)
            for a, var in x.items():
                if a not in dag:
                    model.add_implication(var, detour)
            out_arcs, in_arcs = collections.defaultdict(list), collections.defaultdict(list)
            for (u, v), var in x.items():
                out_arcs[u].append(var)
                in_arcs[v].append(var)
                arcs_on_edge[frozenset((u, v))].append(var)
            model.add(sum(out_arcs[pcell]) == s)
            model.add(sum(in_arcs[ccell]) == s)
            for node in set(out_arcs) | set(in_arcs):
                if node not in (pcell, ccell):
                    model.add(sum(in_arcs[node]) == sum(out_arcs[node]))
                    model.add(sum(in_arcs[node]) <= 1)
            # excess = length - d when selected, else 0.
            pair_excess = sum(x.values()) - d * s
            model.add(pair_excess >= 2 * detour)
            excess_terms.append(pair_excess)
        model.add(sum(select[(port, c)] for c in req.tied) == req.choose)

    edge_vars: dict[frozenset, cp_model.IntVar] = {}
    for edge, arc_vars in arcs_on_edge.items():
        y = model.new_bool_var("")
        edge_vars[edge] = y
        for var in arc_vars:
            model.add_implication(var, y)
        model.add_bool_or(arc_vars).only_enforce_if(y)

    incident = collections.defaultdict(list)
    for edge, y in edge_vars.items():
        for c in edge:
            incident[c].append(y)
    tile_vars = []
    for cell, ys in incident.items():
        if not instance.is_free(cell):
            continue
        z = model.new_bool_var("")
        tile_vars.append(z)
        model.add(sum(ys) <= 3)
        for y in ys:
            model.add_implication(y, z)
        model.add_bool_or(ys).only_enforce_if(z)
    return model, select, edge_vars, sum(excess_terms), sum(tile_vars), sum(detours)


def _run(model: cp_model.CpModel, time_limit: float, workers: int, log: bool):
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    solver.parameters.log_search_progress = log
    status = solver.solve(model)
    return solver, status


def solve(instance: Instance, time_limit: float = 600.0, workers: int = 8,
          log: bool = False, slack: int = 2) -> tuple[Solution | None, dict]:
    """Returns (solution, stats). stats['optimal'] is True only if both phases proved
    optimality and the slack certificate (excess <= slack) holds."""
    reqs = requirements(instance)
    start = time.perf_counter()
    good = (cp_model.OPTIMAL, cp_model.FEASIBLE)
    while True:
        model, select, edge_vars, excess, tiles, detours = _build(instance, reqs, slack)
        model.minimize(excess)
        remaining = time_limit - (time.perf_counter() - start)
        solver, status = _run(model, remaining, workers, log)
        if status == cp_model.INFEASIBLE:
            if slack >= instance.width * instance.height:
                return None, {"status": "INFEASIBLE", "slack": slack,
                              "seconds": round(time.perf_counter() - start, 2)}
            slack *= 2
            continue  # corridors too narrow for any feasible network
        if status not in good:
            return None, {"status": solver.status_name(status), "slack": slack,
                          "seconds": round(time.perf_counter() - start, 2)}
        best_excess = int(solver.objective_value)
        if status == cp_model.OPTIMAL and best_excess > slack:
            slack = best_excess  # widen so the certificate holds, then re-solve
            continue
        break
    phase1_optimal = status == cp_model.OPTIMAL

    model.clear_objective()
    model.add(excess == best_excess)
    model.add(2 * detours <= best_excess)
    model.minimize(tiles)
    # hint phase 2 with the phase-1 solution
    for var in list(select.values()) + list(edge_vars.values()):
        model.add_hint(var, solver.value(var))
    remaining = max(1.0, time_limit - (time.perf_counter() - start))
    solver, status = _run(model, remaining, workers, log)
    stats = {
        "status": solver.status_name(status),
        "optimal": phase1_optimal and status == cp_model.OPTIMAL,
        "excess": best_excess,
        "tiles": int(solver.objective_value) if status in good else None,
        "tiles_bound": int(solver.best_objective_bound) if status in good else None,
        "slack": slack,
        "seconds": round(time.perf_counter() - start, 2),
    }
    if status not in good:
        return None, stats
    edges = {e for e, y in edge_vars.items() if solver.value(y)}
    pairs = {p: [c for c in reqs[p].candidates if solver.value(select[(p, c)])] for p in reqs}
    return Solution(edges=edges, pairs=pairs), stats
