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
  1. Feasibility by depth-first T-orientation branching (Lemma C). Gives a feasible
     network, or proves that none exists.
  2. Optimal excess by best-first branch and bound over the same T-orientations. The
     bound of a set D of deleted edges is the excess of the breadth-first trees in the
     grid minus D, which no network inside it can beat. The first node whose trees obey
     the degree rule is optimal for the first objective.
  3. Optimal tile count at that excess X: depth-first search over canonical path systems
     of nominal excess <= X (Lemmas A and B), with branch and bound on the tile count,
     starting from the network of step 2.
"""
from __future__ import annotations

import collections
import heapq
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
    def _tick(self, every: int = 2048) -> None:
        self.nodes += 1
        if self.deadline is not None and self.nodes % every == 0 \
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

    # --------------------------------- step 2: optimal excess, best-first over D
    def excess_search(self, reqs, strong: int = 12):
        """Minimum excess over all feasible networks, by best-first branch and bound over
        sets D of deleted edges (Lemma C). Returns (edges, pairs, excess) of a network
        attaining it, or None if the instance is infeasible.

        The key of a node D is the excess of its tree union, a lower bound for every
        network inside the grid minus D. The crossroads to branch on is chosen among
        the first `strong` violated ones as the one whose four children have the
        largest minimum bound (strong branching); any choice is correct."""
        root = frozenset()
        res = self._tree_union(reqs, root)
        if res is None:
            return None
        heap = [(res[2], len(res[3]), 0, root, res)]
        seen = {root}
        counter = 1
        while heap:
            _, _, _, deleted, (edges, pairs, excess, bad) = heapq.heappop(heap)
            self._tick(every=1)
            if not bad:
                return edges, pairs, excess
            best = None
            for x in bad[:strong]:
                children = []
                for y in self.adj[x]:
                    child = deleted | {(min(x, y), max(x, y))}
                    children.append((child, self._tree_union(reqs, child)))
                bounds = [INF if r is None else r[2] for _, r in children]
                score = (min(bounds), sum(b for b in bounds if b is not INF), -len(children))
                if best is None or score > best[0]:
                    best = (score, children)
                if min(bounds) is INF:
                    break  # this crossroads cannot be repaired at all: the node is dead
            for child, r in best[1]:
                if r is None or child in seen:
                    continue
                seen.add(child)
                heapq.heappush(heap, (r[2], len(r[3]), counter, child, r))
                counter += 1
        return None

    # ------------------------------ heuristic: fewer tiles at the same excess
    def improve_tiles(self, reqs, pairs: dict, edges: set) -> set:
        """Local search that re-routes one pair at a time along another shortest valid
        path that adds fewer new tiles. Heuristic only: it returns a network with the
        same selection, the same excess and at most as many tiles, which the exact
        search of step 3 then uses as its first incumbent."""
        inst, n, adj, free = self.inst, self.n, self.adj, self.free
        net_adj: list = [[] for _ in range(n)]
        for a, b in edges:
            net_adj[a].append(b)
            net_adj[b].append(a)
        paths = []  # (port cell, city cell, cells of the path, grid distance)
        for port, chosen in pairs.items():
            p = self.index[inst.ports[port]]
            dist, parent = [INF] * n, [-1] * n
            dist[p] = 0
            queue = collections.deque([p])
            while queue:
                u = queue.popleft()
                if u != p and not free[u]:
                    continue
                for v in net_adj[u]:
                    if dist[v] is INF:
                        dist[v], parent[v] = dist[u] + 1, u
                        queue.append(v)
            for city in chosen:
                v = c = self.index[inst.cities[city]]
                cells = [v]
                while parent[v] != -1:
                    v = parent[v]
                    cells.append(v)
                paths.append([p, c, cells[::-1], reqs[port].distance[city]])
        edge_use: collections.Counter = collections.Counter()
        cell_use: collections.Counter = collections.Counter()
        deg = [0] * n

        def add(cells, sign):
            for a, b in zip(cells, cells[1:]):
                e = (a, b) if a < b else (b, a)
                before = edge_use[e]
                edge_use[e] += sign
                if (before == 0) != (edge_use[e] == 0):
                    deg[a] += sign
                    deg[b] += sign
            for v in cells:
                cell_use[v] += sign

        for _, _, cells, _ in paths:
            add(cells, 1)
        from_port = {p: self._bfs(p)[0] for p in {q[0] for q in paths}}
        to_city = {c: self._bfs(c)[0] for c in {q[1] for q in paths}}
        improved = True
        while improved:
            improved = False
            for path in paths:
                p, c, cells, d = path
                if len(cells) - 1 != d:
                    continue  # a detour: keep it
                self._tick(every=1)
                add(cells, -1)
                old_cost = sum(1 for v in cells if free[v] and cell_use[v] == 0)
                dp, dc = from_port[p], to_city[c]
                cost, back = {p: 0}, {}
                layer = [p]
                for _ in range(d):
                    nxt: dict = {}
                    for u in layer:
                        for v in adj[u]:
                            if dp[v] != dp[u] + 1 or dp[v] + dc[v] != d or (v != c and not free[v]):
                                continue
                            e = (u, v) if u < v else (v, u)
                            if edge_use[e] == 0 and ((free[u] and deg[u] >= 3) or (free[v] and deg[v] >= 3)):
                                continue
                            value = cost[u] + (1 if free[v] and cell_use[v] == 0 else 0)
                            if v not in nxt or value < nxt[v]:
                                nxt[v] = value
                                back[v] = u
                    cost.update(nxt)
                    layer = list(nxt)
                candidate = None
                if c in cost and cost[c] < old_cost:
                    candidate = [c]
                    while candidate[-1] != p:
                        candidate.append(back[candidate[-1]])
                    candidate.reverse()
                    add(candidate, 1)
                    if any(free[v] and deg[v] > 3 for v in candidate):
                        add(candidate, -1)
                        candidate = None
                if candidate is None:
                    add(cells, 1)
                else:
                    path[2] = candidate
                    improved = True
        return {e for e, count in edge_use.items() if count > 0}

    # ---------------------------------------- step 3: canonical path-system search
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

        edges, pairs, excess = solver.excess_search(reqs)
        incumbent = (edges, pairs)
        stats.update(excess=excess, excess_optimal=True, nodes_excess=solver.nodes,
                     seconds_excess=round(time.perf_counter() - start, 3))
        edges = solver.improve_tiles(reqs, pairs, edges)
        incumbent = (edges, pairs)
        tiles = len({c for e in edges for c in e if solver.free[c]})
        stats["tiles_upper_bound"] = tiles

        ports = list(reqs)
        selections = [
            [list(reqs[p].required) + list(extra)
             for extra in itertools.combinations(reqs[p].tied, reqs[p].choose)]
            for p in ports
        ]
        for combo in itertools.product(*selections):
            todo = []
            for port, chosen in zip(ports, combo):
                for city in chosen:
                    todo.append((solver.index[instance.ports[port]],
                                 solver.index[instance.cities[city]],
                                 reqs[port].distance[city]))
            # long (rigid) pairs first, grouped by port
            todo.sort(key=lambda t: (t[0], -t[2], t[1]))
            res = solver.path_search(todo, excess, tiles)
            if res is not None:
                tiles, edges = res
                pairs = dict(zip(ports, combo))
                incumbent = (edges, pairs)
                stats["tiles_upper_bound"] = tiles
        solution = Solution(
            edges={frozenset((solver.cells[a], solver.cells[b])) for a, b in edges},
            pairs={p: list(cs) for p, cs in pairs.items()},
        )
        stats.update(status="OPTIMAL", optimal=True, tiles=tiles, nodes=solver.nodes)
        del stats["tiles_upper_bound"]
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
