"""Deliberately naive exact solver: try every network and every tie choice.

This mirrors the Lean-verified algorithm (`lean/TrainNetwork/Search.lean`: `allCands`
searched by `solveFrom`): a *candidate* is a subset of the grid edges (edges between
adjacent, non-blocked, in-bounds cells) together with one valid tie choice per port.
Every candidate is handed to the independent checker `verify.check`; the first
lexicographically cheapest feasible one, by (total excess, track tiles), is returned.

There are 2^|edges| * (number of tie choices) candidates, so this is only usable on
tiny grids. `solve` refuses grids with more than `max_edges` edges.

  python -m network_solver.exhaustive INSTANCE.json [--max-edges N] [--out SOLUTION]
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time

from network_solver import verify
from network_solver.distances import PortRequirement, requirements
from network_solver.instance import Edge, Instance, Solution


def grid_edges(instance: Instance) -> list[Edge]:
    """Every edge a network may contain, in a fixed order."""
    edges = []
    for y in range(instance.height):
        for x in range(instance.width):
            if (x, y) in instance.blocked:
                continue
            for other in ((x + 1, y), (x, y + 1)):
                if instance.in_bounds(other) and other not in instance.blocked:
                    edges.append(frozenset(((x, y), other)))
    return edges


def tie_choices(reqs: dict[str, PortRequirement]) -> list[dict[str, list[str]]]:
    """Every valid selection: per port, the required cities plus `choose` tied ones."""
    per_port = [
        [list(req.required) + list(extra)
         for extra in itertools.combinations(req.tied, req.choose)]
        for req in reqs.values()
    ]
    return [dict(zip(reqs, combo)) for combo in itertools.product(*per_port)]


def solve(instance: Instance, max_edges: int = 22) -> tuple[Solution | None, dict]:
    """Returns (optimal solution, stats), or (None, stats) with stats["status"] ==
    "INFEASIBLE" when no feasible network exists (including the case where some port
    reaches fewer than k cities).

    Raises ValueError when the grid has more than `max_edges` edges.
    """
    start = time.perf_counter()
    edges = grid_edges(instance)
    if len(edges) > max_edges:
        raise ValueError(
            f"The grid has {len(edges)} edges; exhaustive search is limited to "
            f"max_edges={max_edges} (2^{len(edges)} networks per tie choice)."
        )
    try:
        choices = tie_choices(requirements(instance))
    except ValueError:  # a port reaches fewer than k cities
        choices = []

    best: Solution | None = None
    best_cost: tuple[int, int] | None = None
    candidates = 0
    if choices:
        for mask in range(1 << len(edges)):
            network = {edge for bit, edge in enumerate(edges) if mask >> bit & 1}
            for pairs in choices:
                candidates += 1
                candidate = Solution(edges=network, pairs=pairs)
                report = verify.check(instance, candidate)
                if report.ok and (best_cost is None or report.cost < best_cost):
                    best, best_cost = candidate, report.cost

    stats = {
        "status": "INFEASIBLE" if best is None else "OPTIMAL",
        "edges": len(edges),
        "candidates": candidates,
        "seconds": round(time.perf_counter() - start, 3),
    }
    if best is None:
        return None, stats
    stats.update(optimal=True, excess=best_cost[0], tiles=best_cost[1])
    return Solution(edges=set(best.edges), pairs={p: list(cs) for p, cs in best.pairs.items()}), stats


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m network_solver.exhaustive",
                                     description="Exhaustive exact solver (tiny grids only).")
    parser.add_argument("instance")
    parser.add_argument("--max-edges", type=int, default=22)
    parser.add_argument("--out", help="write the solution JSON here")
    args = parser.parse_args(argv)

    instance = Instance.load(args.instance)
    try:
        solution, stats = solve(instance, max_edges=args.max_edges)
    except ValueError as error:
        print(json.dumps({"status": "REFUSED", "reason": str(error)}))
        return 2
    print(json.dumps(stats))
    if solution is None:
        return 1
    report = verify.check(instance, solution)
    ok = report.ok and report.cost == (stats["excess"], stats["tiles"])
    print("verify:", f"OK excess={report.excess} tiles={report.tiles}" if ok
          else report.errors or f"cost mismatch: verifier says {report.cost}")
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(solution.to_json(instance), f, indent=1)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
