"""Exact combinatorial solver for docs/problem.md that does not use CP-SAT.

This is the *search* half of the partial result described in docs/result.md. It is exact
on every instance, but its worst-case running time is exponential: it is NOT the
polynomial-time algorithm the goal asks for (we do not have one).

What it relies on (docs/result.md, section 3):

* Lemma A (path systems). The optimum equals the minimum, over all families of simple
  port-to-city paths (one per chosen pair, interior cells free) whose union has at most
  3 edges at every free cell, of the *nominal* cost
  (sum of path lengths minus sum of d(p, c), number of free cells in the union).
* Lemma B (canonical systems). Some optimal family is *canonical*: any two of its paths
  meet in one common contiguous sub-path (possibly empty). So the search may reject a
  new path as soon as it re-touches an earlier path it has already left, or joins two
  cells of an earlier path by an edge that path does not use.
* Lemma C (T-orientations). A network is feasible iff it avoids at least one of the four
  edges at every free cell with four open neighbours ("crossroads"). Hence branching on
  the edge to delete at a crossroads that the current tree union uses with degree 4 is a
  complete search for feasibility.

Algorithm:
  0. `requirements` (k nearest cities, tie group). No solution if a port reaches < k.
  1. Feasibility by T-orientation branching (Lemma C). Gives an upper bound E0 on the
     optimal excess, or proves that no feasible network exists.
  2. For X = 0, 2, 4, ... <= E0 (excess is always even on a grid): depth-first search
     over canonical path systems of nominal excess <= X, with branch and bound on the
     tile count. The first X that admits a system is the optimal excess, and the best
     system found at that level has the optimal tile count.
"""
from __future__ import annotations

import collections
import itertools
import sys
import time

from network_solver.distances import requirements
from network_solver.instance import Instance, Solution

INF = float("inf")


class _Timeout(Exception):
    pass


class _Solver:
    def __init__(self, instance: Instance, time_limit: float | None):
        self.inst = instance
        self.deadline = None if time_limit is None else time.perf_counter() + time_limit
        self.cells = [(x, y) for x in range(instance.width) for y in range(instance.height)
                      if (x, y) not in instance.blocked]
        self.index = {c: i for i, c in enumerate(self.cells)}
        n = len(self.cells)
        self.n = n
        self.free = [instance.is_free(c) for c in self.cells]
        self.adj = [[self.index[v] for v in instance.neighbours(c)] for c in self.cells]
        self.nodes = 0

    # ------------------------------------------------------------------ utilities
    def _tick(self) -> None:
        self.nodes += 1
        if self.deadline is not None and self.nodes % 2048 == 0 \
                and time.perf_counter() > self.deadline:
            raise _Timeout

    def _bfs(self, source: int, deleted: frozenset = frozenset()) -> tuple[list, list]:
        """Distances and BFS parents from `source`; other terminals are not expanded."""
        dist = [INF] * self.n
        parent = [-1] * self.n
        dist[source] = 0
        queue = collections.deque([source])
        while queue:
            u = queue.popleft()
            if u != source and not self.free[u]:
                continue
            for v in self.adj[u]:
                if dist[v] is INF and (min(u, v), max(u, v)) not in deleted:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    queue.append(v)
        return dist, parent

    # ------------------------------------------------- step 1: T-orientation search
    def _tree_union(self, reqs, deleted: frozenset):
        """Union of one BFS tree per port in the grid minus `deleted`.

        Returns None if some port cannot reach enough cities, otherwise
        (edges, pairs, excess, crossroads used with degree 4)."""
        inst = self.inst
        edges: set = set()
        pairs: dict = {}
        excess = 0
        for port, req in reqs.items():
            dist, parent = self._bfs(self.index[inst.ports[port]], deleted)
            chosen = list(req.required)
            if any(dist[self.index[inst.cities[c]]] is INF for c in chosen):
                return None
            tied = sorted((dist[self.index[inst.cities[c]]], c) for c in req.tied)
            tied = [c for dv, c in tied if dv is not INF][: req.choose]
            if len(tied) < req.choose:
                return None
            chosen += tied
            pairs[port] = chosen
            for c in chosen:
                v = self.index[inst.cities[c]]
                excess += dist[v] - req.distance[c]
                while parent[v] != -1:
                    edges.add((min(v, parent[v]), max(v, parent[v])))
                    v = parent[v]
        degree = collections.Counter()
        for a, b in edges:
            degree[a] += 1
            degree[b] += 1
        bad = [x for x, dg in degree.items() if dg == 4 and self.free[x]]
        return edges, pairs, excess, bad

    def orientation_search(self, reqs):
        """Complete feasibility search (Lemma C). Returns (edges, pairs, excess) of some
        feasible network, or None if there is none."""
        seen: set = set()
        stack = [frozenset()]
        while stack:
            deleted = stack.pop()
            if deleted in seen:
                continue
            seen.add(deleted)
            self._tick()
            res = self._tree_union(reqs, deleted)
            if res is None:
                continue
            edges, pairs, excess, bad = res
            if not bad:
                return edges, pairs, excess
            x = bad[0]
            for y in self.adj[x]:
                stack.append(deleted | {(min(x, y), max(x, y))})
        return None

    # ---------------------------------------- step 2: canonical path-system search
    def path_search(self, pairs: list, cap: int, best_tiles: float):
        """Minimum tile count over canonical path systems for `pairs` (a list of
        (port index, city index, d)) with nominal excess <= cap and fewer than
        `best_tiles` tiles. Returns (tiles, edge set) or None."""
        n, adj, free = self.n, self.adj, self.free
        to_city = {c: self._bfs(c)[0] for c in {c for _, c, _ in pairs}}
        deg = [0] * n            # distinct union edges at each cell
        edge_use: dict = {}      # edge -> number of placed paths using it
        cell_use = [0] * n       # number of placed/current paths through each cell
        cell_paths: list = [[] for _ in range(n)]  # indices of *placed* paths per cell
        path_edges: list = [set() for _ in pairs]
        best = [best_tiles, None]

        def place(i: int, used: int, tiles: int) -> None:
            if i == len(pairs):
                best[0] = tiles          # tiles < best[0] is guaranteed by pruning
                best[1] = set(edge_use)
                return
            p, c, d = pairs[i]
            dc = to_city[c]
            budget = d + cap - used
            if dc[p] > budget:
                return
            status = {j: 1 for j in cell_paths[p]}
            on_path = {p}
            trail = [p]
            my_edges = path_edges[i]
            cell_use[p] += 1

            def extend(u: int, length: int, tiles: int) -> None:
                self._tick()
                if u == c:
                    for v in trail:
                        cell_paths[v].append(i)
                    place(i + 1, used + length - d, tiles)
                    for v in trail:
                        cell_paths[v].pop()
                    return
                options = []
                for v in adj[u]:
                    if v in on_path or (v != c and not free[v]):
                        continue
                    if length + 1 + dc[v] > budget:
                        continue
                    e = (u, v) if u < v else (v, u)
                    options.append((e not in edge_use, dc[v], v, e))
                options.sort()
                for new_edge, _, v, e in options:
                    # Lemma B: the intersection with every placed path is one sub-path.
                    changes = []
                    ok = True
                    here = cell_paths[v]
                    for j in here:
                        s = status.get(j, 0)
                        if s == 2 or (s == 1 and e not in path_edges[j]):
                            ok = False
                            break
                        if s == 0:
                            status[j] = 1
                            changes.append((j, 0))
                    if ok:
                        for j in cell_paths[u]:
                            if status.get(j) == 1 and j not in here:
                                status[j] = 2
                                changes.append((j, 1))
                        if new_edge:
                            if (free[u] and deg[u] >= 3) or (free[v] and deg[v] >= 3):
                                ok = False
                    if ok:
                        new_tiles = tiles + (1 if free[v] and cell_use[v] == 0 else 0)
                        if new_tiles < best[0]:
                            if new_edge:
                                deg[u] += 1
                                deg[v] += 1
                            edge_use[e] = edge_use.get(e, 0) + 1
                            my_edges.add(e)
                            cell_use[v] += 1
                            on_path.add(v)
                            trail.append(v)
                            extend(v, length + 1, new_tiles)
                            trail.pop()
                            on_path.discard(v)
                            cell_use[v] -= 1
                            my_edges.discard(e)
                            if edge_use[e] == 1:
                                del edge_use[e]
                                deg[u] -= 1
                                deg[v] -= 1
                            else:
                                edge_use[e] -= 1
                    for j, old in reversed(changes):
                        if old == 0:
                            del status[j]
                        else:
                            status[j] = old

            extend(p, 0, tiles)
            cell_use[p] -= 1

        place(0, 0, 0)
        return None if best[1] is None else (best[0], best[1])


def solve(instance: Instance, time_limit: float | None = None) -> tuple[Solution | None, dict]:
    """Returns (solution, stats). `stats["optimal"]` is True iff the search completed, in
    which case `solution` is optimal (or None because the instance is infeasible)."""
    start = time.perf_counter()
    stats: dict = {"status": "UNKNOWN", "optimal": False}

    def done(solution):
        stats["seconds"] = round(time.perf_counter() - start, 3)
        return solution, stats

    try:
        reqs = requirements(instance)
    except ValueError:
        stats.update(status="INFEASIBLE", optimal=True, reason="a port reaches fewer than k cities")
        return done(None)

    solver = _Solver(instance, time_limit)
    old_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old_limit, 20 * solver.n + 10_000))
    incumbent = None
    try:
        found = solver.orientation_search(reqs)
        if found is None:
            stats.update(status="INFEASIBLE", optimal=True, reason="no degree-3 network connects the pairs",
                         nodes=solver.nodes)
            return done(None)
        edges, pairs, upper = found
        incumbent = (edges, pairs)
        stats["excess_upper_bound"] = upper

        ports = list(reqs)
        selections = [
            [list(reqs[p].required) + list(extra)
             for extra in itertools.combinations(reqs[p].tied, reqs[p].choose)]
            for p in ports
        ]
        cap = 0
        while True:
            best = None
            for combo in itertools.product(*selections):
                todo = []
                for port, chosen in zip(ports, combo):
                    for city in chosen:
                        todo.append((solver.index[instance.ports[port]],
                                     solver.index[instance.cities[city]],
                                     reqs[port].distance[city]))
                # long (rigid) pairs first, grouped by port
                todo.sort(key=lambda t: (t[0], -t[2], t[1]))
                res = solver.path_search(todo, cap, INF if best is None else best[0])
                if res is not None:
                    best = (res[0], res[1], dict(zip(ports, combo)))
            if best is not None:
                break
            cap += 2
            if cap > upper:  # cannot happen (Lemma A/B); kept as a safety net
                raise AssertionError("path search missed the orientation-search solution")
        tiles, edge_idx, chosen = best
        solution = Solution(
            edges={frozenset((solver.cells[a], solver.cells[b])) for a, b in edge_idx},
            pairs={p: list(cs) for p, cs in chosen.items()},
        )
        stats.update(status="OPTIMAL", optimal=True, excess=cap, tiles=tiles, nodes=solver.nodes)
        return done(solution)
    except _Timeout:
        stats.update(status="TIMEOUT", nodes=solver.nodes)
        if incumbent is not None:
            edges, pairs = incumbent
            return done(Solution(
                edges={frozenset((solver.cells[a], solver.cells[b])) for a, b in edges},
                pairs={p: list(cs) for p, cs in pairs.items()},
            ))
        return done(None)
    finally:
        sys.setrecursionlimit(old_limit)
