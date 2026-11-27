"""Exhaustive solver: the Python mirror of `lean/TrainNetwork/Brute/Solve.lean`.

It follows the *Lean* definitions (`lean/TrainNetwork/Problem.lean`) directly and does
not use `network_solver.distances.requirements`:

* candidates are all subsets of the grid edges, times all assignments port -> set of
  cities;
* a set S is a valid choice for port p iff it is an `IsNearestChoice`: S is a set of k
  cities, all at finite grid distance, none farther than any unchosen city;
* feasibility and cost are the ones of `Solution.Feasible` and `Solution.cost`.

The only liberty taken is to minimise over the choice of each port separately (the
excess is a sum over ports), instead of enumerating whole assignments.

Running time: 2^(number of grid edges) networks. Usable up to about 13 grid edges. This
is the algorithm whose correctness is machine-checked in Lean; it is not polynomial.
"""
from __future__ import annotations

import collections
import itertools

from network_solver.instance import Cell, Instance, Solution

INF = float("inf")


def all_edges(instance: Instance) -> list[tuple[Cell, Cell]]:
    """Grid edges between open cells, each once, oriented right / down (`allEdges`)."""
    out = []
    for x in range(instance.width):
        for y in range(instance.height):
            a = (x, y)
            if a in instance.blocked:
                continue
            for b in ((x + 1, y), (x, y + 1)):
                if instance.in_bounds(b) and b not in instance.blocked:
                    out.append((a, b))
    return out


def walk_dist(instance: Instance, adj: dict[Cell, list[Cell]], source: Cell) -> dict[Cell, int]:
    """`walkDist`: shortest walks from `source` whose intermediate cells are all free."""
    dist = {source: 0}
    queue = collections.deque([source])
    while queue:
        u = queue.popleft()
        if u != source and not instance.is_free(u):
            continue
        for v in adj.get(u, ()):
            if v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist


def nearest_choices(instance: Instance, grid: dict[Cell, int]) -> list[tuple[str, ...]]:
    """All `IsNearestChoice` sets of one port, given its grid distances."""
    names = sorted(instance.cities)
    d = {c: grid.get(instance.cities[c], INF) for c in names}
    out = []
    for chosen in itertools.combinations(names, instance.k):
        if any(d[c] == INF for c in chosen):
            continue
        rest = [c for c in names if c not in chosen]
        if all(d[c] <= d[o] for c in chosen for o in rest):
            out.append(chosen)
    return out


def solve(instance: Instance, max_edges: int = 16) -> tuple[Solution | None, dict]:
    edges = all_edges(instance)
    if len(edges) > max_edges:
        raise ValueError(f"{len(edges)} grid edges: too many for exhaustive search")
    grid_adj: dict[Cell, list[Cell]] = collections.defaultdict(list)
    for a, b in edges:
        grid_adj[a].append(b)
        grid_adj[b].append(a)
    ports = sorted(instance.ports)
    grid = {p: walk_dist(instance, grid_adj, instance.ports[p]) for p in ports}
    choices = {p: nearest_choices(instance, grid[p]) for p in ports}
    stats = {"networks": 1 << len(edges), "status": "INFEASIBLE"}
    if any(not choices[p] for p in ports):
        return None, stats

    best = None  # (excess, tiles, edge subset, pairs)
    for mask in range(1 << len(edges)):
        subset = [e for i, e in enumerate(edges) if mask >> i & 1]
        adj: dict[Cell, list[Cell]] = collections.defaultdict(list)
        for a, b in subset:
            adj[a].append(b)
            adj[b].append(a)
        if any(len(nbrs) > 3 and instance.is_free(c) for c, nbrs in adj.items()):
            continue
        excess = 0
        pairs = {}
        for p in ports:
            net = walk_dist(instance, adj, instance.ports[p])
            best_p = None
            for chosen in choices[p]:
                cells = [instance.cities[c] for c in chosen]
                if any(c not in net for c in cells):
                    continue
                value = sum(net[c] - grid[p][c] for c in cells)
                if best_p is None or value < best_p[0]:
                    best_p = (value, chosen)
            if best_p is None:
                break
            excess += best_p[0]
            pairs[p] = list(best_p[1])
        else:
            tiles = sum(1 for c in adj if instance.is_free(c))
            if best is None or (excess, tiles) < best[:2]:
                best = (excess, tiles, subset, pairs)
    if best is None:
        return None, stats
    stats.update(status="OPTIMAL", excess=best[0], tiles=best[1])
    return Solution(edges={frozenset(e) for e in best[2]}, pairs=best[3]), stats
