"""Independent checker for a Solution. Shares only `requirements` with the solver.

A solution is feasible iff (docs/problem.md, "Feasibility"):
  1. every edge joins two orthogonally adjacent, in-bounds, non-blocked cells;
  2. every free (track) cell has at most 3 incident edges (terminals may have 4);
  3. for every port, the chosen cities are the required ones plus exactly `choose`
     of the tied ones;
  4. every chosen (port, city) is connected in the network by a path whose interior
     uses only free cells.
Its cost is the pair (total excess, track tiles), compared lexicographically, where a
pair's excess is its network distance minus d(port, city).
"""
from __future__ import annotations

import collections
import dataclasses

from network_solver.distances import requirements
from network_solver.instance import Cell, Instance, Solution


@dataclasses.dataclass
class Report:
    errors: list[str]
    excess: int | None
    tiles: int

    @property
    def ok(self) -> bool:
        return not self.errors

    @property
    def cost(self) -> tuple[int, int] | None:
        return (self.excess, self.tiles) if self.ok else None


def network_distances(instance: Instance, adj: dict[Cell, set[Cell]], source: Cell) -> dict[Cell, int]:
    dist = {source: 0}
    queue = collections.deque([source])
    while queue:
        cell = queue.popleft()
        if cell != source and not instance.is_free(cell):
            continue  # terminals are endpoints only
        for nxt in adj[cell]:
            if nxt not in dist:
                dist[nxt] = dist[cell] + 1
                queue.append(nxt)
    return dist


def check(instance: Instance, solution: Solution) -> Report:
    errors: list[str] = []
    adj: dict[Cell, set[Cell]] = collections.defaultdict(set)
    for edge in solution.edges:
        cells = tuple(edge)
        if len(cells) != 2:
            errors.append(f"degenerate edge {cells}")
            continue
        a, b = cells
        if abs(a[0] - b[0]) + abs(a[1] - b[1]) != 1:
            errors.append(f"edge {a}-{b} is not between adjacent cells")
        for c in (a, b):
            if not instance.in_bounds(c) or c in instance.blocked:
                errors.append(f"edge {a}-{b} touches blocked/out-of-bounds cell {c}")
        adj[a].add(b)
        adj[b].add(a)

    for cell, nbrs in adj.items():
        if instance.is_free(cell) and len(nbrs) > 3:
            errors.append(f"track cell {cell} has degree {len(nbrs)} > 3")

    reqs = requirements(instance)
    if set(solution.pairs) != set(instance.ports):
        errors.append("pairs must list every port exactly once")
    excess = 0
    for port, req in reqs.items():
        chosen = set(solution.pairs.get(port, []))
        if not set(req.required) <= chosen:
            errors.append(f"{port}: missing required {set(req.required) - chosen}")
        extra = chosen - set(req.required)
        if not extra <= set(req.tied) or len(extra) != req.choose:
            errors.append(f"{port}: must choose {req.choose} of tied {req.tied}, chose {extra}")
        dist = network_distances(instance, adj, instance.ports[port])
        for city in sorted(chosen & set(req.distance)):
            got = dist.get(instance.cities[city])
            if got is None:
                errors.append(f"{port}->{city}: not connected")
            else:
                excess += got - req.distance[city]
    return Report(errors=errors, excess=excess, tiles=solution.cost(instance))
