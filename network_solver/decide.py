"""The decision version of docs/problem.md, answered three ways.

* `decide_cpsat`: the CP-SAT oracle (`network_solver.cpsat`), asked the decision
  question directly: "is there a feasible network with excess <= X and <= K tiles?".
* `decide_sat`: the reduction to CNF-SAT (`network_solver.sat.to_sat`) followed by a
  SAT solver.
* `decode`: turns a satisfying assignment of `to_sat(inst, X, K)` back into a
  `Solution`, so that `network_solver.verify` can check it independently.
"""
from __future__ import annotations

from ortools.sat.python import cp_model

from network_solver import cpsat, sat
from network_solver.distances import requirements
from network_solver.instance import Instance, Solution


def decide_cpsat(inst: Instance, X: int, K: int, time_limit: float = 120.0,
                 workers: int = 8) -> bool:
    """Oracle. Any solution with total excess <= X has every pair's excess <= X, so it
    lies inside the corridors of slack X and the corridor model is exact."""
    try:
        reqs = requirements(inst)
    except ValueError:
        return False  # some port reaches fewer than k cities
    model, _select, _edges, excess, tiles, _detours = cpsat._build(inst, reqs, slack=X)
    model.add(excess <= X)
    model.add(tiles <= K)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    status = solver.solve(model)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return True
    if status == cp_model.INFEASIBLE:
        return False
    raise RuntimeError(f"oracle stopped with status {solver.status_name(status)}")


def decode(inst: Instance, assignment: dict[int, bool]) -> Solution:
    """The network and choices encoded by a satisfying assignment."""
    edges = set()
    for x in range(inst.width):
        for y in range(inst.height):
            for u in ((x + 1, y), (x, y + 1)):
                if assignment.get(sat.v_edge((x, y), u), False):
                    edges.add(frozenset(((x, y), u)))
    pairs = {
        pn: [cn for cn, c in inst.cities.items() if assignment.get(sat.v_sel(p, c), False)]
        for pn, p in inst.ports.items()
    }
    return Solution(edges=edges, pairs=pairs)


def decide_sat(inst: Instance, X: int, K: int, time_limit: float = 600.0,
               workers: int = 8) -> tuple[bool, Solution | None]:
    """Decides via the reduction. Returns (answer, decoded witness or None)."""
    assignment = sat.satisfiable(sat.to_sat(inst, X, K), time_limit, workers)
    if assignment is None:
        return False, None
    return True, decode(inst, assignment)
