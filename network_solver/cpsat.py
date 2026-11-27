"""CP-SAT model for the problem in docs/problem.md.

Differences from the original circuit-per-pair model (PR #1), which made it slow:
  * Each (port, candidate city) gets a path model only over its *shortest-path DAG*:
    arcs u->v with d_p(u) + 1 + d_c(v) == d(p, c). Every unit flow in that DAG is a
    shortest path, so there is no circuit constraint, no bounding-box guess, and no
    length term in the objective - path length is fixed by construction.
  * Distances are true BFS distances around clouds and other terminals.
  * Tie choices at the k-th place are decision variables.
  * The objective is exactly the number of track tiles (free cells used).
"""
from __future__ import annotations

import collections
import time

from ortools.sat.python import cp_model

from network_solver.distances import PortRequirement, bfs, requirements
from network_solver.instance import Cell, Instance, Solution


def _dag_arcs(instance: Instance, port_cell: Cell, city_cell: Cell, d: int,
              dist_from_port: dict[Cell, int]) -> list[tuple[Cell, Cell]]:
    dist_from_city = bfs(instance, city_cell)
    arcs = []
    for u, du in dist_from_port.items():
        if du >= d:
            continue
        if u != port_cell and not instance.is_free(u):
            continue  # interior may only use free cells
        if du + dist_from_city.get(u, d + 1) != d:
            continue
        for v in instance.neighbours(u):
            if v != city_cell and not instance.is_free(v):
                continue
            if dist_from_port.get(v) == du + 1 and du + 1 + dist_from_city.get(v, d + 1) == d:
                arcs.append((u, v))
    return arcs


def solve(instance: Instance, time_limit: float = 600.0, workers: int = 8,
          log: bool = False) -> tuple[Solution | None, dict]:
    reqs: dict[str, PortRequirement] = requirements(instance)
    model = cp_model.CpModel()

    edge_vars: dict[frozenset, cp_model.IntVar] = {}
    arcs_on_edge: dict[frozenset, list] = collections.defaultdict(list)
    select: dict[tuple[str, str], cp_model.IntVar] = {}

    for port, req in reqs.items():
        pcell = instance.ports[port]
        dist_from_port = bfs(instance, pcell)
        for city in req.candidates:
            ccell = instance.cities[city]
            s = model.new_bool_var(f"sel[{port},{city}]")
            select[(port, city)] = s
            if city in req.required:
                model.add(s == 1)
            arcs = _dag_arcs(instance, pcell, ccell, req.distance[city], dist_from_port)
            x = {a: model.new_bool_var(f"x[{port},{city},{a}]") for a in arcs}
            out_arcs = collections.defaultdict(list)
            in_arcs = collections.defaultdict(list)
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
        model.add(sum(select[(port, c)] for c in req.tied) == req.choose)

    for edge, arc_vars in arcs_on_edge.items():
        y = model.new_bool_var(f"y[{sorted(edge)}]")
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
        z = model.new_bool_var(f"z[{cell}]")
        tile_vars.append(z)
        model.add(sum(ys) <= 3)
        for y in ys:
            model.add_implication(y, z)
        model.add_bool_or(ys).only_enforce_if(z)
    model.minimize(sum(tile_vars))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    solver.parameters.log_search_progress = log
    start = time.perf_counter()
    status = solver.solve(model)
    stats = {
        "status": solver.status_name(status),
        "seconds": round(time.perf_counter() - start, 2),
        "objective": solver.objective_value if status in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None,
        "bound": solver.best_objective_bound,
        "variables": len(model.proto.variables),
    }
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None, stats
    edges = {e for e, y in edge_vars.items() if solver.value(y)}
    pairs = {p: [c for c in reqs[p].candidates if solver.value(select[(p, c)])] for p in reqs}
    return Solution(edges=edges, pairs=pairs), stats
