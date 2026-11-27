"""NP-hardness side: the reduction Rectilinear Steiner Tree -> Train Network.

RECTILINEAR STEINER TREE (Garey & Johnson 1977): given a set A of points with integer
coordinates and an integer L, is there a rectilinear Steiner tree for A of total length
at most L?

`rst_to_train(points, L)` is the reduction of docs/result.md, section 6: scale the
points by s = 4|A| + 1, make the first point the only port and all the others cities,
take k = |A| - 1, no blocked cells, an excess bound that never binds, and the tile bound
K = s*L + 3|A| + 1.

The rest of the module is test support: an exact Steiner tree solver on the Hanan grid
(Dreyfus-Wagner) and `witness`, which turns an optimal tree into a feasible network of
the reduced instance (the constructive half of the correctness proof).
"""
from __future__ import annotations

from network_solver.instance import Cell, Instance, Solution

Point = tuple[int, int]
MARGIN = 2


def scale_factor(points: list[Point]) -> int:
    return 4 * len(points) + 1


def _place(points: list[Point]) -> tuple[int, list[Cell]]:
    s = scale_factor(points)
    x0 = min(x for x, _ in points)
    y0 = min(y for _, y in points)
    return s, [(s * (x - x0) + MARGIN, s * (y - y0) + MARGIN) for x, y in points]


def rst_to_train(points: list[Point], L: int) -> tuple[Instance, int, int]:
    """The reduction. Requires at least two distinct points."""
    if len(points) < 2 or len(set(points)) != len(points):
        raise ValueError("need at least two distinct points")
    m = len(points)
    s, cells = _place(points)
    width = max(x for x, _ in cells) + MARGIN + 1
    height = max(y for _, y in cells) + MARGIN + 1
    inst = Instance(
        width=width, height=height, blocked=frozenset(), k=m - 1,
        ports={"P": cells[0]},
        cities={f"C{i}": c for i, c in enumerate(cells[1:], start=1)},
    )
    X = (m - 1) * width * height   # never binds: every network distance is < W*H
    K = s * L + 3 * m + 1
    return inst, X, K


# --------------------------------------------------------------------------------------
# Exact rectilinear Steiner trees on the Hanan grid (test support)
# --------------------------------------------------------------------------------------

def hanan_steiner_tree(points: list[Point]) -> tuple[int, set[frozenset]]:
    """Minimum rectilinear Steiner tree of `points`, by the Dreyfus-Wagner recursion on
    the Hanan grid (Hanan 1966: some optimal tree lies on it). Returns its length and
    its set of Hanan-grid edges, each a frozenset of two grid points."""
    xs = sorted({x for x, _ in points})
    ys = sorted({y for _, y in points})
    nodes = [(x, y) for x in xs for y in ys]
    index = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    inf = float("inf")
    dist = [[inf] * n for _ in range(n)]
    nxt = [[-1] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
        nxt[i][i] = i
    for (xa, xb) in zip(xs, xs[1:]):
        for y in ys:
            a, b = index[(xa, y)], index[(xb, y)]
            dist[a][b] = dist[b][a] = xb - xa
            nxt[a][b], nxt[b][a] = b, a
    for (ya, yb) in zip(ys, ys[1:]):
        for x in xs:
            a, b = index[(x, ya)], index[(x, yb)]
            dist[a][b] = dist[b][a] = yb - ya
            nxt[a][b], nxt[b][a] = b, a
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if dist[i][k] + dist[k][j] < dist[i][j]:
                    dist[i][j] = dist[i][k] + dist[k][j]
                    nxt[i][j] = nxt[i][k]

    def path_edges(i: int, j: int) -> set[frozenset]:
        out = set()
        while i != j:
            step = nxt[i][j]
            out.add(frozenset((nodes[i], nodes[step])))
            i = step
        return out

    terms = [index[p] for p in points]
    root, rest = terms[0], terms[1:]
    full = (1 << len(rest)) - 1
    dp = [[inf] * n for _ in range(full + 1)]
    how: list[list[tuple | None]] = [[None] * n for _ in range(full + 1)]
    for b, t in enumerate(rest):
        for v in range(n):
            dp[1 << b][v] = dist[t][v]
            how[1 << b][v] = ("leaf", t)
    for mask in range(1, full + 1):
        if mask & (mask - 1) == 0:
            continue
        merged = [inf] * n
        split = [0] * n
        sub = (mask - 1) & mask
        while sub:
            if sub < mask ^ sub:
                for v in range(n):
                    c = dp[sub][v] + dp[mask ^ sub][v]
                    if c < merged[v]:
                        merged[v], split[v] = c, sub
            sub = (sub - 1) & mask
        for v in range(n):
            best, arg = inf, -1
            for u in range(n):
                c = merged[u] + dist[u][v]
                if c < best:
                    best, arg = c, u
            dp[mask][v] = best
            how[mask][v] = ("join", arg, split[arg])

    def build(mask: int, v: int) -> set[frozenset]:
        h = how[mask][v]
        if h[0] == "leaf":
            return path_edges(h[1], v)
        _, u, sub = h
        return path_edges(u, v) | build(sub, u) | build(mask ^ sub, u)

    return int(dp[full][root]), build(full, root)


def rst_length(points: list[Point]) -> int:
    return hanan_steiner_tree(points)[0]


# --------------------------------------------------------------------------------------
# From a Steiner tree to a network (the constructive half of the proof; test support)
# --------------------------------------------------------------------------------------

RING = [(0, -1), (1, -1), (1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1)]  # clockwise


def witness(points: list[Point], tree: set[frozenset]) -> Solution:
    """A feasible network for `rst_to_train(points, .)` built from a Steiner tree on the
    Hanan grid of `points`: the scaled tree, repaired around every city of degree >= 2
    (cities cannot be passed through) and every free cell of degree 4."""
    s, cells = _place(points)
    x0 = min(x for x, _ in points)
    y0 = min(y for _, y in points)

    def img(p: Point) -> Cell:
        return (s * (p[0] - x0) + MARGIN, s * (p[1] - y0) + MARGIN)

    edges: set[frozenset] = set()
    for e in tree:
        a, b = (img(p) for p in e)
        (ax, ay), (bx, by) = sorted((a, b))
        if ay == by:
            for x in range(ax, bx):
                edges.add(frozenset(((x, ay), (x + 1, ay))))
        else:
            for y in range(ay, by):
                edges.add(frozenset(((ax, y), (ax, y + 1))))

    def nbrs(c: Cell) -> list[Cell]:
        return [d for e in edges if c in e for d in e if d != c]

    cities = set(cells[1:])
    port = cells[0]
    corners = {c for e in edges for c in e}
    for p in sorted(corners):
        arms = nbrs(p)
        if p in cities and len(arms) >= 2:
            # link the arm cells by the shortest arc of the ring around p
            pos = sorted(RING.index((a[0] - p[0], a[1] - p[1])) for a in arms)
            gaps = [((pos[(i + 1) % len(pos)] - pos[i]) % 8 or 8, i) for i in range(len(pos))]
            _, i = max(gaps)
            start, end = pos[(i + 1) % len(pos)], pos[i]
            length = (end - start) % 8
            ring = [(p[0] + RING[(start + j) % 8][0], p[1] + RING[(start + j) % 8][1])
                    for j in range(length + 1)]
            for a in arms:
                edges.discard(frozenset((p, a)))
            for a, b in zip(ring, ring[1:]):
                edges.add(frozenset((a, b)))
            edges.add(frozenset((p, ring[0])))
        elif p not in cities and p != port and len(arms) == 4:
            north, east, ne = (p[0], p[1] - 1), (p[0] + 1, p[1]), (p[0] + 1, p[1] - 1)
            edges.discard(frozenset((p, north)))
            edges.add(frozenset((north, ne)))
            edges.add(frozenset((ne, east)))
    return Solution(edges=edges, pairs={"P": [f"C{i}" for i in range(1, len(points))]})


def grid_steiner_edges(width: int, height: int, terminals: list[Cell]) -> int:
    """Minimum number of edges of a connected subgraph of the full `width x height`
    grid graph that contains all `terminals` (Dreyfus-Wagner with Dijkstra relaxation).
    Independent of `hanan_steiner_tree`: it does not use Hanan's theorem."""
    import heapq

    inf = float("inf")
    cells = [(x, y) for x in range(width) for y in range(height)]
    root, rest = terminals[0], terminals[1:]
    full = (1 << len(rest)) - 1

    def relax(start: dict[Cell, float]) -> dict[Cell, float]:
        dist = dict(start)
        heap = [(d, c) for c, d in start.items() if d < inf]
        heapq.heapify(heap)
        while heap:
            d, (x, y) = heapq.heappop(heap)
            if d > dist[(x, y)]:
                continue
            for nxt in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
                if 0 <= nxt[0] < width and 0 <= nxt[1] < height and d + 1 < dist[nxt]:
                    dist[nxt] = d + 1
                    heapq.heappush(heap, (d + 1, nxt))
        return dist

    dp: dict[int, dict[Cell, float]] = {}
    for b, t in enumerate(rest):
        dp[1 << b] = relax({c: (0 if c == t else inf) for c in cells})
    for mask in range(1, full + 1):
        if mask & (mask - 1) == 0:
            continue
        merged = {c: inf for c in cells}
        sub = (mask - 1) & mask
        while sub:
            if sub < mask ^ sub:
                a, b = dp[sub], dp[mask ^ sub]
                for c in cells:
                    if a[c] + b[c] < merged[c]:
                        merged[c] = a[c] + b[c]
            sub = (sub - 1) & mask
        dp[mask] = relax(merged)
    return int(dp[full][root])


def random_points(rng, m: int, box: int) -> list[Point]:
    return rng.sample([(x, y) for x in range(box) for y in range(box)], m)
