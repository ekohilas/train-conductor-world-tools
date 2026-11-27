"""Exact layered dynamic program for the problem in docs/problem.md.

The solver works on *certificates* instead of networks. Fix an instance, let ports be
indexed j = 0..q-1 (sorted by cell) and fix a *choice family* (for every port: its
required cities plus `choose` cities of its tie group). A certificate gives every
in-bounds cell x

  * four edge bits e[R], e[D], e[L], e[U]  (R = (x+1, y), D = (x, y+1), ...), and
  * for every port j an entry: None, or (d, delta) with 0 <= d <= W*H and delta a
    direction (the "predecessor direction").

With free(x), allow(x, delta) (x and its delta-neighbour in bounds and not blocked),
src_j(x) (x is port j), transit_j(x) = free(x) or src_j(x), and dem_j(x) = g(j, x) if x
is a city chosen for port j (else None), the constraints are

  (U1) e[delta] => allow(x, delta)
  (U2) free(x) => at most 3 edge bits
  (U3) src_j(x) => entry_j = (0, anything); otherwise entry_j is None or (d, delta)
       with d >= 1 and e[delta] set
  (U4) dem_j(x) != None => entry_j != None
  (B1) e_x[delta] = e_y[opp delta]                      for y the delta-neighbour of x
  (B2) entry_j(x) = (d, delta), not src_j(x) => transit_j(y) and entry_j(y) = (d-1, .)
  (B3) entry_j(y) = (d, opp delta), not src_j(y) => transit_j(x), entry_j(x) = (d-1, .)

and the cost is (excess, tiles) compared lexicographically, where
excess = sum over demands of (d - g) and tiles = #{free x with an edge bit}. Entries are
upper bounds on network distances and the true distances of a feasible network form a
certificate, so the minimum over all families and certificates is the optimum of the
problem. The network of a certificate is {x, x+R} for e_x[R] plus {x, x+D} for e_x[D].

Two modes
---------

``mode="verbatim"``: exactly the system above, solved by a DP over whole layers (columns
if H <= W, else rows). The table of layer i maps every self-valid layer state to the
cheapest completion over layers i..last. Self-valid states are produced by backtracking
over the cells of the layer (same set as filtering all tuples) and the layer-to-layer
minimum is taken over projections of the states onto what (B1)-(B3) can see. No other
constraint is used. Only tiny inputs finish.

``mode="pruned"`` (default): the same optimisation restricted to *canonical*
certificates, processed one cell at a time (broken-profile DP; if H > W the instance is
transposed first so that a layer always has min(W, H) cells). Predecessor directions
are not enumerated: a frontier cell carries, per port, a "parent still needed" and a
"child still needed" flag.

The canonical certificate. Let N be the network of an optimal solution. For every port
j take the BFS tree of N from port j (walks with free interior) in which the parent of
a cell v is the first of its neighbours, in the fixed order L, U, D, R, that is joined
to v in N, is transit_j and has distance dist(v) - 1. Port j's chosen paths are the
tree paths to its chosen cities; their union S_j is a tree rooted at port j whose
leaves are exactly the chosen cities of j. The network N' is the union of the S_j (a
sub-network of N with the same pair distances, hence also optimal) and port j labels
exactly the cells of S_j with their exact network distance. Each chosen path is a
network-shortest path, so this is a special case of "network = union of one
network-shortest path per chosen pair, labelled with exact distances". In N', the
parent of v in S_j is still the first neighbour (order L, U, D, R) that is joined to v,
transit_j and labelled d_j(v) - 1: those neighbours are a subset of the candidates in
N and contain the tree parent. Call that neighbour the *parent* of v for j. It is a
function of labels and edge bits and exists for every labelled non-source cell of any
certificate (U3/B2/B3).

The canonical certificate satisfies all of the following rules, so none of them changes
the optimum, and every assignment the DP accepts is a certificate of the system above.

  (P1) corridor of budget X: an entry d for port j at x needs
       g_j(x) <= d <= max over chosen cities c of (g(j, c) + X - h(x, c)); for a city
       cell only its own bound g(j, x) + X is used (its label is the length of its own
       path). X runs through 0, 2, 4, 8, 16, ...; a run whose optimum has excess <= X
       is globally optimal; the run with X >= W*H is final: its corridor contains the
       canonical certificate of every feasible solution, so "no certificate" there
       means infeasible.
  (P2) Lipschitz: on a network edge x-y with both cells labelled for j and x
       transit_j: d_j(y) <= d_j(x) + 1.
  (P3) successor, in the sharper form (P3t): a free cell labelled for j is the parent,
       for j, of one of its network neighbours (which is then labelled d + 1). True
       because a free cell of S_j is interior to a tree path, and the next cell of
       that path has it as parent.
  (P4) a cell with an edge bit has a port entry; a city has an entry for j only if it
       is chosen for j; a port only for itself; and, sharper than "every network edge
       has a port for which both ends are labelled with labels differing by 1", (P4t):
       every network edge joins some cell to its parent for some port. True because
       every edge of N' is an edge of some S_j.
  (P5) a free cell with an edge bit has at least 2 edge bits.

Rules added on top of P1-P5 (P3t and P4t above are also additions), each with its
justification:

  (P6) excess cap: in a non-final run of budget X, partial certificates whose
       accumulated excess exceeds X are dropped. Excess terms are non-negative, so a
       certificate of total excess <= X never has a partial sum above X; a non-final
       run is only accepted when its optimum has excess <= X, and then the optimal
       canonical certificate (excess E* <= that) survives the cap. The final run has
       no cap.
  (P7) incumbent bound: all families are solved at the same budget and the best is
       taken; while solving a family, partial certificates whose cost is already >= the
       best complete certificate of an earlier family are dropped. Costs only grow
       along the DP, so such states cannot improve the minimum over families.
  (P8) budget split across ports (generalises P1): for an entry d of port j at x let
       eta_j(x) = min over cities c chosen for j of (d + h(x, c) - g(j, c)) (for a city
       cell: d - g(j, x)); P1 says eta_j(x) <= X. In a non-final run of budget X,
       sum over ports j of max over x in S of eta_j(x) <= X is required for S = a new
       cell together with its processed network neighbours, and for S = the frontier
       (the processed cells that still have an edge to an unprocessed cell) after
       every cell. Justification: in the canonical certificate x lies on port j's
       chosen path to some chosen city c_x, whose excess is
       d(x) + (rest of the path) - g(j, c_x) >= d(x) + h(x, c_x) - g(j, c_x)
       >= eta_j(x). Picking for every port the cell with the largest eta gives pairs
       of distinct ports, hence distinct pairs, so the total excess is at least the
       sum; and the total excess of the optimal certificate is <= X whenever the run
       is accepted. The final run does not use P8.
  (P9) leaf count: after every cell, for every port j,
         (number of pending child obligations of port j)
           <= #{chosen cities of j not processed yet}
              + #{frontier cells labelled for j whose parent is not processed yet},
       where a frontier cell x contributes to the left-hand side the larger of
       [x still needs a child for j (P3t)] and the number of its edges to unprocessed
       cells z for which "z gets x as parent for j" is the only way left (given the
       label domains of z and which parents x still lacks) to satisfy P4t.
       Justification: every counted obligation is a distinct edge x-z of the tree S_j
       from a processed parent x to an unprocessed child z. Follow a tree path from z
       down to a leaf and stop at the first processed cell (its parent is unprocessed,
       so it is counted on the right) or, if there is none, at the leaf (an
       unprocessed chosen city). The map is injective: if x-z and x'-z' had the same
       image w, then z and z' are both ancestors-or-equal of w; z = z' gives x = x',
       and if z is strictly above z' then x' is a processed cell on the unique tree
       path from z to w before w, contradicting the choice of w.
  (P10) root count (mirror image of P9): after every cell, for every port j,
         #{frontier cells labelled for j whose parent is not processed yet}
           <= #{chosen cities of j already processed}
              + (number of pending child obligations of port j, as in P9).
       Justification: from a cell x of the left-hand side walk down the tree S_j
       through processed children for as long as there is one. The walk ends at a
       processed chosen city of j or at a free cell without processed child, which
       still needs a child and so contributes at least 1 to the obligations. The end
       cell determines x (x is its first ancestor-or-self whose parent is not
       processed), so the map is injective.

Not rules, only consequences of the above used to drop dead states early: labels have
the parity of g_j(x) (every grid walk from port j to x has that parity); a cell that no
port can label carries no edge (P4) and is skipped; an edge to an unprocessed cell is
only created or kept if the label domains still allow it to become a parent edge (and
two such edges of one cell need two different ports if both can only lead to parents
of that cell); a pending parent or child must still be obtainable from an unprocessed
neighbour. Dominance is the ordinary one: best cost per frontier state.

The families are enumerated inside the budget loop (for each X: all families), which
gives the same minimum as "for each family: iterative deepening" but never needs the
final run for an infeasible family when another family is feasible. The final run is
by far the most expensive one (labels range over all of 0..W*H and P6/P8 are off), so
proving infeasibility is slow beyond roughly 20 cells with many pairs.
"""
from __future__ import annotations

import itertools
import resource
import sys
import time

from network_solver import verify
from network_solver.distances import bfs, requirements
from network_solver.instance import Cell, Instance, Solution

R, D, L, U = 0, 1, 2, 3
DELTA = ((1, 0), (0, 1), (-1, 0), (0, -1))
OPP = (L, U, R, D)

_SLOT_BITS = 24
_SLOT_MASK = (1 << _SLOT_BITS) - 1


class _Stop(Exception):
    """Raised when a time / memory guard fires."""

    def __init__(self, reason: str) -> None:
        super().__init__(reason)
        self.reason = reason


class _Control:
    def __init__(self, time_limit: float | None, max_states: int | None,
                 max_rss_mb: float | None, stats: dict, verbose: bool) -> None:
        self.start = time.perf_counter()
        self.deadline = None if time_limit is None else self.start + time_limit
        self.max_states = max_states
        self.max_rss_mb = max_rss_mb
        self.stats = stats
        self.verbose = verbose

    def check(self, table_size: int = 0) -> None:
        if table_size > self.stats["states"]:
            self.stats["states"] = table_size
        if self.deadline is not None and time.perf_counter() > self.deadline:
            raise _Stop("time_limit")
        if self.max_states is not None and table_size > self.max_states:
            raise _Stop("max_states")
        if self.max_rss_mb is not None:
            rss_mb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0
            if rss_mb > self.max_rss_mb:
                raise _Stop("max_rss")

    def log(self, message: str) -> None:
        if self.verbose:
            print(f"[layerdp {time.perf_counter() - self.start:8.1f}s] {message}",
                  file=sys.stderr, flush=True)


def port_order(instance: Instance) -> list[str]:
    """Ports in the fixed order used for the index j (sorted by cell)."""
    return sorted(instance.ports, key=lambda p: instance.ports[p])


def choice_families(instance: Instance, reqs=None) -> list[dict[str, tuple[str, ...]]]:
    """Every valid choice family: per port, required cities plus a `choose`-subset of
    the tie group."""
    reqs = requirements(instance) if reqs is None else reqs
    names = port_order(instance)
    per_port = [
        [tuple(reqs[p].required) + extra
         for extra in itertools.combinations(reqs[p].tied, reqs[p].choose)]
        for p in names
    ]
    return [dict(zip(names, combo)) for combo in itertools.product(*per_port)]


# --------------------------------------------------------------------------------------
# Verbatim mode
# --------------------------------------------------------------------------------------

def _verbatim_family(inst: Instance, names: list[str], family: dict, reqs: dict,
                     ctl: _Control) -> tuple[int, set] | None:
    """Layered DP over full layer states for one choice family. Returns
    (excess * M + tiles, edges) or None if the family has no certificate."""
    width, height = inst.width, inst.height
    dmax = width * height
    big = dmax + 1
    q = len(names)
    pcell = [inst.ports[p] for p in names]
    blocked, terminals = inst.blocked, inst.terminals
    by_cols = height <= width
    nlayers, m = (width, height) if by_cols else (height, width)
    inner, cross = (D, R) if by_cols else (R, D)

    def cell(i: int, a: int) -> Cell:
        return (i, a) if by_cols else (a, i)

    def inb(c: Cell) -> bool:
        return 0 <= c[0] < width and 0 <= c[1] < height

    def free(c: Cell) -> bool:
        return inb(c) and c not in blocked and c not in terminals

    def nbr(c: Cell, dr: int) -> Cell:
        return (c[0] + DELTA[dr][0], c[1] + DELTA[dr][1])

    def allow(c: Cell, dr: int) -> bool:
        y = nbr(c, dr)
        return inb(c) and c not in blocked and inb(y) and y not in blocked

    def transit(j: int, c: Cell) -> bool:
        return free(c) or c == pcell[j]

    dem = [{inst.cities[c]: reqs[p].distance[c] for c in family[p]} for p in names]

    def cell_labels(x: Cell) -> list:
        """All labels (edge bits, entries) of cell x satisfying U1-U4."""
        out = []
        allowed = [allow(x, dr) for dr in range(4)]
        is_free = free(x)
        for e in itertools.product((0, 1), repeat=4):
            if any(e[dr] and not allowed[dr] for dr in range(4)):
                continue  # U1
            if is_free and sum(e) > 3:
                continue  # U2
            per_port = []
            for j in range(q):
                if x == pcell[j]:
                    opts = [(0, dr) for dr in range(4)]  # U3, source
                else:
                    opts = [] if x in dem[j] else [None]  # U4
                    opts += [(d, dr) for d in range(1, dmax + 1)
                             for dr in range(4) if e[dr]]  # U3
                per_port.append(opts)
            out.extend((e, ent) for ent in itertools.product(*per_port))
        return out

    def cell_cost(x: Cell, lab) -> int:
        e, ent = lab
        cost = 1 if free(x) and any(e) else 0
        for j in range(q):
            if x in dem[j] and ent[j] is not None:
                cost += (ent[j][0] - dem[j][x]) * big
        return cost

    def project(x: Cell, lab, dr: int) -> tuple:
        """What the pair constraints with the dr-neighbour of x can see of lab."""
        e, ent = lab
        return (e[dr], tuple(
            (-1, False) if en is None else (en[0], en[1] == dr and x != pcell[j])
            for j, en in enumerate(ent)))

    compat_memo: dict = {}

    def compatible(x: Cell, px: tuple, y: Cell, py: tuple) -> bool:
        """B1-B3 for x and its neighbour y, on the projections of their labels."""
        key = (x, px, y, py)
        hit = compat_memo.get(key)
        if hit is None:
            hit = px[0] == py[0]  # B1
            if hit:
                for j in range(q):
                    dx, fx = px[1][j]
                    dy, fy = py[1][j]
                    if fx and not (transit(j, y) and dy == dx - 1):  # B2
                        hit = False
                        break
                    if fy and not (transit(j, x) and dx == dy - 1):  # B3
                        hit = False
                        break
            compat_memo[key] = hit
        return hit

    def layer_states(i: int) -> list:
        cells = [cell(i, a) for a in range(m)]
        labels = [cell_labels(x) for x in cells]
        fwd = [[project(cells[a], lab, inner) for lab in labels[a]] for a in range(m)]
        bwd = [[project(cells[a], lab, OPP[inner]) for lab in labels[a]] for a in range(m)]
        states: list = []
        acc: list = []
        acc_idx: list = []

        def rec(a: int) -> None:
            if a == m:
                states.append(tuple(acc))
                if not len(states) & 0xFFF:
                    ctl.check(len(states))
                return
            for idx, lab in enumerate(labels[a]):
                if a and not compatible(cells[a - 1], fwd[a - 1][acc_idx[-1]],
                                        cells[a], bwd[a][idx]):
                    continue
                acc.append(lab)
                acc_idx.append(idx)
                rec(a + 1)
                acc.pop()
                acc_idx.pop()

        rec(0)
        ctl.check(len(states))
        return states

    def sig(i: int, state, dr: int) -> tuple:
        return tuple(project(cell(i, a), state[a], dr) for a in range(m))

    def state_cost(i: int, state) -> int:
        return sum(cell_cost(cell(i, a), state[a]) for a in range(m))

    # Backward recursion: table[s] = cheapest completion of layers i..last from s.
    choice: list[dict] = [dict() for _ in range(nlayers)]
    table: dict = {}
    for i in range(nlayers - 1, -1, -1):
        states = layer_states(i)
        ctl.log(f"verbatim layer {i}: {len(states)} self-valid states")
        new: dict = {}
        if i == nlayers - 1:
            for s in states:
                new[s] = state_cost(i, s)
        else:
            # Group the next table by what the transition can see of its states.
            by_edges: dict = {}
            seen: dict = {}
            for s2, c2 in table.items():
                key = sig(i + 1, s2, OPP[cross])
                old = seen.get(key)
                if old is None or c2 < old[0]:
                    seen[key] = (c2, s2)
            for key, (c2, s2) in seen.items():
                by_edges.setdefault(tuple(p[0] for p in key), []).append((key, c2, s2))
            best_for: dict = {}
            xs = [cell(i, a) for a in range(m)]
            ys = [cell(i + 1, a) for a in range(m)]
            for n_done, s in enumerate(states):
                if not n_done & 0xFF:
                    ctl.check()
                key = sig(i, s, cross)
                if key not in best_for:
                    best = None
                    for key2, c2, s2 in by_edges.get(tuple(p[0] for p in key), ()):
                        if (best is None or c2 < best[0]) and all(
                                compatible(xs[a], key[a], ys[a], key2[a]) for a in range(m)):
                            best = (c2, s2)
                    best_for[key] = best
                best = best_for[key]
                if best is not None:
                    new[s] = state_cost(i, s) + best[0]
            choice[i] = {k: v[1] for k, v in best_for.items() if v is not None}
        table = new
        if not table:
            return None
    state = min(table, key=table.get)
    cost = table[state]
    edges = set()
    for i in range(nlayers):
        for a in range(m):
            x = cell(i, a)
            e = state[a][0]
            if e[R]:
                edges.add(frozenset((x, nbr(x, R))))
            if e[D]:
                edges.add(frozenset((x, nbr(x, D))))
        if i + 1 < nlayers:
            state = choice[i][sig(i, state, cross)]
    return cost, edges


# --------------------------------------------------------------------------------------
# Pruned mode
# --------------------------------------------------------------------------------------

class _Grid:
    """Family-independent data of the (possibly transposed) instance. Internally the
    cell (x, y) has index t = x * m + y with m = height <= width, so that the left
    neighbour is t - m and the upper neighbour is t - 1."""

    def __init__(self, instance: Instance, names: list[str]) -> None:
        self.transposed = instance.height > instance.width
        if self.transposed:
            def flip(c: Cell) -> Cell:
                return (c[1], c[0])
            inst = Instance(
                width=instance.height, height=instance.width, k=instance.k,
                blocked=frozenset(flip(c) for c in instance.blocked),
                ports={p: flip(c) for p, c in instance.ports.items()},
                cities={n: flip(c) for n, c in instance.cities.items()})
        else:
            inst = instance
        self.inst = inst
        self.m = m = inst.height
        self.n = inst.width
        self.ncell = ncell = self.m * self.n
        self.names = names
        self.q = len(names)
        self.dmax = ncell

        def index(c: Cell) -> int:
            return c[0] * m + c[1]

        self.index = index
        self.blocked = [False] * ncell
        for c in inst.blocked:
            self.blocked[index(c)] = True
        self.port_at = [-1] * ncell
        for j, p in enumerate(names):
            self.port_at[index(inst.ports[p])] = j
        self.city_at: list[str | None] = [None] * ncell
        for name, c in inst.cities.items():
            self.city_at[index(c)] = name
        self.free = [not self.blocked[t] and self.port_at[t] < 0 and self.city_at[t] is None
                     for t in range(ncell)]
        self.transit = [[self.free[t] or self.port_at[t] == j for t in range(ncell)]
                        for j in range(self.q)]

        def dist_list(source: Cell) -> list[int]:
            out = [-1] * ncell
            for c, v in bfs(inst, source).items():
                out[index(c)] = v
            return out

        self.g = [dist_list(inst.ports[p]) for p in names]
        self.h = {name: dist_list(c) for name, c in inst.cities.items()}

    def cell(self, t: int) -> Cell:
        """Cell of index t in the coordinates of the original instance."""
        x, y = divmod(t, self.m)
        return (y, x) if self.transposed else (x, y)


def _pruned_run(grid: _Grid, family: dict, reqs: dict, budget: int, final: bool,
                incumbent: int | None, ctl: _Control) -> tuple[int, set] | None:
    """Frontier DP for one family and one corridor budget. Returns
    (excess * M + tiles, edges in original coordinates) for the cheapest canonical
    certificate that beats `incumbent`, or None."""
    m, n, q, ncell = grid.m, grid.n, grid.q, grid.ncell
    dmax = grid.dmax
    big = dmax + 1
    names = grid.names
    port_at, free, transit = grid.port_at, grid.free, grid.transit

    # Label domains (P1, P4): port j may label cell t with d in lo..hi (step 2).
    lo = [[1] * ncell for _ in range(q)]
    hi = [[0] * ncell for _ in range(q)]
    dem = [[-1] * ncell for _ in range(q)]
    # eta_j(x) = d - base[j][x] (P8); base is the upper end of the X = 0 corridor.
    base = [[0] * ncell for _ in range(q)]
    split = not final and budget > 0 and q > 1  # whether P8 says more than P1
    for j, p in enumerate(names):
        chosen = [(reqs[p].distance[c], grid.h[c]) for c in family[p]]
        chosen_names = set(family[p])
        gj = grid.g[j]
        lo_j, hi_j, dem_j, base_j = lo[j], hi[j], dem[j], base[j]
        for t in range(ncell):
            if grid.blocked[t]:
                continue
            if port_at[t] >= 0:
                if port_at[t] == j:
                    lo_j[t] = hi_j[t] = 0
                continue
            city = grid.city_at[t]
            if city is not None:
                if city in chosen_names:
                    dist = reqs[p].distance[city]
                    dem_j[t] = dist
                    lo_j[t] = base_j[t] = dist
                    hi_j[t] = min(dist + budget, dmax)
                    hi_j[t] -= (hi_j[t] - dist) & 1
                continue
            if gj[t] < 0:
                continue
            top = -1
            for dist, h in chosen:
                if h[t] >= 0 and dist + budget - h[t] > top:
                    top = dist + budget - h[t]
            base_j[t] = top - budget
            top = min(top, dmax)
            if top >= gj[t]:
                lo_j[t] = gj[t]
                hi_j[t] = top - ((top - gj[t]) & 1)

    active = [any(lo[j][t] <= hi[j][t] for j in range(q)) for t in range(ncell)]

    def can_witness_static(a: int, b: int) -> bool:
        return any(lo[j][a] <= hi[j][a] and lo[j][b] <= hi[j][b]
                   and lo[j][b] <= hi[j][a] + 1 and lo[j][a] <= hi[j][b] + 1
                   for j in range(q))

    edge_opts: list = [()] * ncell
    for t in range(ncell):
        if not active[t]:
            continue
        r_ok = t + m < ncell and active[t + m] and can_witness_static(t, t + m)
        d_ok = t % m < m - 1 and active[t + 1] and can_witness_static(t, t + 1)
        edge_opts[t] = tuple((er, ed) for er in ((0, 1) if r_ok else (0,))
                             for ed in ((0, 1) if d_ok else (0,)))

    # Frontier slots are interned: id 0 is "nothing pending"; any other id stands for
    # (eR, eD, labels, pred-needed mask, succ-needed mask) of a processed cell.
    slot_id: dict = {}
    slots: list = [None]

    def intern(desc: tuple) -> int:
        sid = slot_id.get(desc)
        if sid is None:
            sid = len(slots)
            if sid > _SLOT_MASK:
                raise _Stop("slot_overflow")
            slot_id[desc] = sid
            slots.append(desc)
        return sid

    count_bias = sum(0x4000 << (16 * j) for j in range(q))

    def can_pred(j: int, d: int, z: int) -> bool:
        return transit[j][z] and lo[j][z] <= d - 1 <= hi[j][z]

    def can_succ(j: int, d: int, z: int) -> bool:
        return lo[j][z] <= d + 1 <= hi[j][z]

    def can_witness(t: int, labs: tuple, pp: int, z: int) -> bool:
        """Whether the edge from t to its unprocessed neighbour z can still become a
        parent edge of some port (P4)."""
        for j in range(q):
            d = labs[j]
            if d < 0:
                continue
            if transit[j][t] and lo[j][z] <= d + 1 <= hi[j][z]:
                return True  # z may get t as its parent
            if (pp >> j) & 1 and transit[j][z] and lo[j][z] <= d - 1 <= hi[j][z]:
                return True  # z may become the parent of t
        return False

    def can_witness_both(t: int, labs: tuple, pp: int) -> bool:
        """Same for both pending edges of t together: a cell has one parent per port,
        so two edges that can only lead to parents of t need two different ports."""
        parents = []
        for z in (t + m, t + 1):
            ports = set()
            for j in range(q):
                d = labs[j]
                if d < 0:
                    continue
                if transit[j][t] and lo[j][z] <= d + 1 <= hi[j][z]:
                    ports = None  # z may get t as its parent: no restriction
                    break
                if (pp >> j) & 1 and transit[j][z] and lo[j][z] <= d - 1 <= hi[j][z]:
                    ports.add(j)
            if ports is not None:
                parents.append(ports)
        return len(parents) < 2 or len(parents[0] | parents[1]) >= 2

    net_memo: dict[tuple[int, int], int] = {}

    def net_count(t: int, sid: int) -> int:
        """Packed per-port (pending child obligations - parent needed) of slot `sid`
        sitting at cell t (P9)."""
        if not sid:
            return 0
        out = net_memo.get((t, sid))
        if out is None:
            e_r, e_d, labs, pp, sp = slots[sid]
            forced = [0] * q
            for z in ((t + m,) if e_r else ()) + ((t + 1,) if e_d else ()):
                ways = []
                for j in range(q):
                    d = labs[j]
                    if d < 0:
                        continue
                    if transit[j][t] and lo[j][z] <= d + 1 <= hi[j][z]:
                        ways.append(j)  # z may get t as parent for j
                    if (pp >> j) & 1 and transit[j][z] and lo[j][z] <= d - 1 <= hi[j][z]:
                        ways.append(-1)  # z may become the parent of t
                if len(ways) == 1 and ways[0] >= 0:
                    forced[ways[0]] += 1
            out = 0
            for j in range(q):
                out += (max(forced[j], (sp >> j) & 1) - ((pp >> j) & 1)) << (16 * j)
            net_memo[(t, sid)] = out
        return out

    def positive(count: int) -> bool:
        """Whether some field of a packed (signed) count vector is positive."""
        count += count_bias
        return any(((count >> (16 * j)) & 0xFFFF) > 0x4000 for j in range(q))

    def negative(count: int) -> bool:
        count += count_bias
        return any(((count >> (16 * j)) & 0xFFFF) < 0x4000 for j in range(q))

    def gen(t: int, lid: int, uid: int) -> list:
        """All ways to label cell t. `lid` is the slot of the left neighbour (non-zero
        iff the edge to it is present), `uid` that of the upper neighbour (non-zero
        only if the edge to it is present). Returns [(new upper slot, slot of t,
        cost delta, eta, count delta, check)], where eta is the eta-vector of t if t
        stays on the frontier with some positive eta (P8), else None; count delta is
        the packed change of (child obligations - parents needed) per port (P9, P10),
        followed by whether it is positive / negative for some port."""
        ls = slots[lid] if lid else None
        us = slots[uid] if uid else None
        e_l = 1 if lid else 0
        e_u = 1 if uid else 0
        is_free = free[t]
        tl, tu = t - m, t - 1
        per_port = []
        for j in range(q):
            a, b = lo[j][t], hi[j][t]
            trx = transit[j][t]
            src = port_at[t] == j
            dj = dem[j][t]
            ll = ls[2][j] if e_l else -1
            lu = us[2][j] if e_u else -1
            pp_l = e_l and (ls[3] >> j) & 1
            sp_l = e_l and (ls[4] >> j) & 1
            pp_u = e_u and (us[3] >> j) & 1
            sp_u = e_u and (us[4] >> j) & 1
            opts = []
            eta_n = 0  # largest eta_j among the processed network neighbours
            if split:
                if ll >= 0:
                    eta_n = ll - base[j][tl]
                if lu >= 0 and lu - base[j][tu] > eta_n:
                    eta_n = lu - base[j][tu]
            if dj < 0 and not src and not pp_l and not sp_l:
                opts.append((-1, 0, 0, 0, 0, pp_u, sp_u, 0, eta_n))  # no entry for port j
            if a <= b:
                first = a
                if ll >= 0:  # P2 on the left edge
                    if transit[j][tl] and ll + 1 < b:
                        b = ll + 1
                    if trx and ll - 1 > a:
                        a = ll - 1
                if lu >= 0:  # P2 on the upper edge
                    if transit[j][tu] and lu + 1 < b:
                        b = lu + 1
                    if trx and lu - 1 > a:
                        a = lu - 1
                if pp_l:  # the left cell leaves the frontier: t must be its predecessor
                    if trx:
                        a, b = max(a, ll - 1), min(b, ll - 1)
                    else:
                        b = a - 1
                if sp_l:  # ... or its successor
                    a, b = max(a, ll + 1), min(b, ll + 1)
                a += (a - first) & 1
                for d in range(a, b + 1, 2):
                    # The parent of t is the first of L, U, D, R that qualifies.
                    qual_l = d > 0 and ll == d - 1 and transit[j][tl]
                    qual_u = d > 0 and lu == d - 1 and transit[j][tu] and not qual_l
                    res_u = pp_u and trx and d == lu - 1  # t becomes the parent of U
                    opts.append((
                        d,
                        not (src or qual_l or qual_u),      # parent still needed
                        is_free and not (pp_l or res_u),    # child still needed
                        qual_l or pp_l,                     # left edge is a parent edge
                        qual_u or res_u,                    # upper edge is a parent edge
                        pp_u and not res_u,
                        sp_u and not qual_u,
                        d - dj if dj >= 0 else 0,
                        max(eta_n, d - base[j][t])))
            if not opts:
                return []
            per_port.append(opts)

        best: dict = {}
        etas: dict = {}
        # packed P9 counts that disappear with the old slots
        gone = net_count(tl, lid) + net_count(tu, uid)
        for combo in itertools.product(*per_port):
            labs = tuple(o[0] for o in combo)
            if max(labs) < 0:
                # No entry at all: by P4 the cell has no edge.
                if not (e_l or e_u):
                    best[(0, 0)] = (0, 0)
                continue
            if split and sum(o[8] for o in combo) > budget:
                continue  # P8 on the cell and its processed network neighbours
            if e_l and not any(o[3] for o in combo):
                continue  # P4: the left edge needs a witness port
            if e_u and not any(o[4] for o in combo):
                continue
            pp = sp = 0
            for j, o in enumerate(combo):
                if o[1]:
                    pp |= 1 << j
                if o[2]:
                    sp |= 1 << j
            new_u = 0
            count_u = -gone
            if e_u:
                pp_u = sp_u = 0
                for j, o in enumerate(combo):
                    if o[5]:
                        pp_u |= 1 << j
                    if o[6]:
                        sp_u |= 1 << j
                if us[0]:
                    # The upper cell keeps its right edge; whatever it still needs must
                    # be available from its right neighbour.
                    ok = True
                    for j in range(q):
                        if (pp_u >> j) & 1 and not can_pred(j, us[2][j], tu + m):
                            ok = False
                        if (sp_u >> j) & 1 and not can_succ(j, us[2][j], tu + m):
                            ok = False
                    if not ok:
                        continue
                    if not can_witness(tu, us[2], pp_u, tu + m):
                        continue
                    new_u = intern((1, 0, us[2], pp_u, sp_u))
                    count_u += net_count(tu, new_u)
                elif pp_u or sp_u:
                    continue
            excess = sum(o[7] for o in combo)
            for e_r, e_d in edge_opts[t]:
                deg = e_l + e_u + e_r + e_d
                if is_free and not 2 <= deg <= 3:
                    continue  # U2, P5 (a labelled free cell needs an edge anyway)
                if e_r or e_d:
                    ok = True
                    for j in range(q):
                        d = labs[j]
                        if d < 0:
                            continue
                        if (pp >> j) & 1 and not (
                                (e_r and can_pred(j, d, t + m)) or (e_d and can_pred(j, d, t + 1))):
                            ok = False
                            break
                        if (sp >> j) & 1 and not (
                                (e_r and can_succ(j, d, t + m)) or (e_d and can_succ(j, d, t + 1))):
                            ok = False
                            break
                    if not ok:
                        continue
                    if e_r and not can_witness(t, labs, pp, t + m):
                        continue
                    if e_d and not can_witness(t, labs, pp, t + 1):
                        continue
                    if e_r and e_d and not can_witness_both(t, labs, pp):
                        continue
                    new_x = intern((e_r, e_d, labs, pp, sp))
                    if split and new_x not in etas:
                        eta = tuple(d - base[j][t] if d >= 0 else 0
                                    for j, d in enumerate(labs))
                        etas[new_x] = eta if any(eta) else None
                else:
                    if pp or sp:
                        continue
                    new_x = 0
                delta = excess * big + (1 if is_free and deg else 0)
                key = (new_u, new_x)
                old = best.get(key)
                if old is None or delta < old[0]:
                    count = count_u + net_count(t, new_x)
                    best[key] = (delta, count)
        return [(nu, nx, delta, etas.get(nx), count, positive(count), negative(count))
                for (nu, nx), (delta, count) in best.items()]

    last_active = {t // m: t for t in range(ncell) if active[t]}
    limit = big * big * (q + 1) * (ncell + 1)  # larger than any cost
    if not final:
        limit = min(limit, (budget + 1) * big)  # P6
    if incumbent is not None:
        limit = min(limit, incumbent)  # P7

    def slot_eta(cache: dict, t: int, sid: int):
        """eta-vector of slot `sid` sitting at cell t (None if all zero)."""
        eta = cache.get(sid, cache)
        if eta is cache:
            eta = tuple(d - base[j][t] if d >= 0 else 0 for j, d in enumerate(slots[sid][2]))
            eta = cache[sid] = eta if any(eta) else None
        return eta

    def join(e1, e2):
        if e1 is None:
            return e2
        if e2 is None:
            return e1
        return tuple(map(max, e1, e2))

    # P9: the state carries, above its slots, per port the 16-bit field
    # 0x4000 + #child-needed - #parent-needed (a function of the slots).
    top = m * _SLOT_BITS
    slots_mask = (1 << top) - 1
    guard = sum(0x8000 << (16 * j) for j in range(q))
    start_state = count_bias << top
    unprocessed = [sum(1 for j2 in range(q) if dem[j2][t2] >= 0) for t2 in range(ncell)]
    total = [sum(1 for t2 in range(ncell) if dem[j][t2] >= 0) for j in range(q)]
    left = list(total)  # chosen cities not processed yet

    table: dict[int, int] = {start_state: 0}
    backs: list[tuple[int, dict]] = []
    # P8 bookkeeping, per row: eta cache of the slots of that row (for the current and
    # for the previous column) and memo of the eta maxima of state prefixes/suffixes.
    cur_eta: list[dict] = [dict() for _ in range(m)]
    old_eta: list[dict] = [dict() for _ in range(m)]
    prefix_memo: list[dict] = [dict() for _ in range(m + 1)]
    suffix_memo: list[dict] = [dict() for _ in range(m + 1)]
    column = -1
    for t in range(ncell):
        if not active[t]:
            continue
        row = t % m
        if split and t // m != column:
            column = t // m
            old_eta, cur_eta = cur_eta, [dict() for _ in range(m)]
            prefix_memo = [dict() for _ in range(m + 1)]
            suffix_memo = [dict() for _ in range(m + 1)]
        if row:
            shift = (row - 1) * _SLOT_BITS
            mask = (1 << (2 * _SLOT_BITS)) - 1
        else:
            shift = 0
            mask = _SLOT_MASK
        clear = ~(mask << shift)
        is_city = unprocessed[t] > 0
        for j in range(q):
            if dem[j][t] >= 0:
                left[j] -= 1
        # With n = packed counts of a state: room_up - n has the guard bit set in
        # every field iff P9 holds, and n + room_down iff P10 holds.
        room_up = sum((left[j] + 0x4000 + 0x8000) << (16 * j) for j in range(q))
        room_down = sum((total[j] - left[j] + 0x4000) << (16 * j) for j in range(q))
        memo: dict = {}
        base_memo: dict = {}
        new: dict[int, int] = {}
        back: dict[int, int] = {}
        get = new.get
        count = 0

        def outcomes(key: int) -> tuple[list, list, list]:
            if row:
                uid = key & _SLOT_MASK
                lid = key >> _SLOT_BITS
            else:
                uid, lid = 0, key
            if uid and not slots[uid][1]:
                # No edge to the upper cell: its slot is untouched.
                raw = base_memo.get(lid)
                if raw is None:
                    raw = base_memo[lid] = gen(t, lid, 0)
                keep = uid
            else:
                raw = gen(t, lid, uid)
                keep = 0
            plain, counted, special = [], [], []
            for nu, nx, delta, eta, count, pos, neg in raw:
                bits = (((nu or keep) | (nx << _SLOT_BITS)) << shift) if row else nx
                bits += count << top
                if eta is not None:
                    special.append((bits, delta, count, eta))
                elif pos or neg or is_city:
                    counted.append((bits, delta, count))
                else:
                    plain.append((bits, delta))
            return plain, counted, special

        if split:
            low_mask = (1 << (row * _SLOT_BITS)) - 1
            high_shift = (row + 1) * _SLOT_BITS
            col_base = t - row

            def prefix_eta(low: int, rows: int):
                """Per-port max eta over the slots of rows < `rows` (current column)."""
                if not low:
                    return None
                cache = prefix_memo[rows]
                hit = cache.get(low, cache)
                if hit is cache:
                    high_bit = (rows - 1) * _SLOT_BITS
                    sid = low >> high_bit
                    hit = prefix_eta(low & ((1 << high_bit) - 1), rows - 1)
                    if sid:
                        hit = join(hit, slot_eta(cur_eta[rows - 1], col_base + rows - 1, sid))
                    cache[low] = hit
                return hit

            def suffix_eta(high: int, rows: int):
                """Per-port max eta over the slots of rows >= `rows` (previous column)."""
                if not high:
                    return None
                cache = suffix_memo[rows]
                hit = cache.get(high, cache)
                if hit is cache:
                    sid = high & _SLOT_MASK
                    hit = suffix_eta(high >> _SLOT_BITS, rows + 1)
                    if sid:
                        hit = join(hit, slot_eta(old_eta[rows], col_base - m + rows, sid))
                    cache[high] = hit
                return hit

        for s, c0 in table.items():
            key = (s >> shift) & mask
            outs = memo.get(key)
            if outs is None:
                outs = memo[key] = outcomes(key)
            plain, counted, special = outs
            rest = s & clear
            for bits, delta in plain:
                c2 = c0 + delta
                s2 = rest + bits
                if c2 < get(s2, limit):
                    new[s2] = c2
                    back[s2] = s
            if counted:
                packed = s >> top
                for bits, delta, cnt in counted:
                    cnt += packed
                    if (room_up - cnt) & guard != guard or (cnt + room_down) & guard != guard:
                        continue  # P9 / P10
                    c2 = c0 + delta
                    s2 = rest + bits
                    if c2 < get(s2, limit):
                        new[s2] = c2
                        back[s2] = s
            if special:
                packed = s >> top
                others = join(prefix_eta(s & low_mask, row),
                              suffix_eta((s & slots_mask) >> high_shift, row + 1))
                for bits, delta, cnt, eta in special:
                    cnt += packed
                    if (room_up - cnt) & guard != guard or (cnt + room_down) & guard != guard:
                        continue  # P9 / P10
                    if others is not None and sum(map(max, others, eta)) > budget:
                        continue  # P8 on the frontier
                    c2 = c0 + delta
                    s2 = rest + bits
                    if c2 < get(s2, limit):
                        new[s2] = c2
                        back[s2] = s
            count += 1
            if not count & 0xFFF:
                ctl.check(len(new))
        table = new
        backs.append((t, back))
        ctl.stats["progress"].update(column=t // m, row=row, table=len(table))
        ctl.check(len(table))
        if last_active[t // m] == t:
            ctl.log(f"X={budget} column {t // m}/{n - 1}: {len(table)} states, "
                    f"{len(slots)} slots")
        if not table:
            return None
    cost = table.get(start_state)
    if cost is None:
        return None
    edges = set()
    state = start_state
    for t, back in reversed(backs):
        sid = (state >> ((t % m) * _SLOT_BITS)) & _SLOT_MASK
        if sid:
            if slots[sid][0]:
                edges.add(frozenset((grid.cell(t), grid.cell(t + m))))
            if slots[sid][1]:
                edges.add(frozenset((grid.cell(t), grid.cell(t + 1))))
        state = back[state]
    return cost, edges


# --------------------------------------------------------------------------------------
# Public API
# --------------------------------------------------------------------------------------

def solve(instance: Instance, mode: str = "pruned", time_limit: float | None = None, *,
          max_states: int | None = None, max_rss_mb: float | None = None,
          verbose: bool = False) -> tuple[Solution | None, dict]:
    """Solves `instance` exactly. Returns (solution, stats).

    stats["status"] is "OPTIMAL" (solution is an optimum, checked with the verifier),
    "INFEASIBLE" (no feasible solution exists; solution is None) or "TIMEOUT" (a guard
    fired: stats["stopped"] is "time_limit", "max_states" or "max_rss"; solution is
    None). stats["states"] is the largest DP table that was built.
    """
    if mode not in ("pruned", "verbatim"):
        raise ValueError(f"unknown mode {mode!r}")
    stats: dict = {"mode": mode, "status": None, "seconds": 0.0, "excess": None,
                   "tiles": None, "states": 0, "progress": {}}
    ctl = _Control(time_limit, max_states, max_rss_mb, stats, verbose)

    def done(status: str, **extra) -> dict:
        stats.update(status=status, seconds=round(time.perf_counter() - ctl.start, 3), **extra)
        return stats

    try:
        reqs = requirements(instance)
    except ValueError as exc:
        # Some port reaches fewer than k cities: no solution (docs/problem.md).
        return None, done("INFEASIBLE", reason=str(exc))
    names = port_order(instance)
    families = choice_families(instance, reqs)
    stats["families"] = len(families)
    big = instance.width * instance.height + 1
    best: tuple[int, set, dict] | None = None
    try:
        if mode == "verbatim":
            for idx, family in enumerate(families):
                stats["progress"].update(family=idx)
                res = _verbatim_family(instance, names, family, reqs, ctl)
                if res is not None and (best is None or res[0] < best[0]):
                    best = (res[0], res[1], family)
        else:
            grid = _Grid(instance, names)
            budget = 0
            runs = 0
            while True:
                final = budget >= instance.width * instance.height
                best = None
                for idx, family in enumerate(families):
                    stats["progress"].update(budget=budget, family=idx, column=0, row=0, table=1)
                    res = _pruned_run(grid, family, reqs, budget, final,
                                      None if best is None else best[0], ctl)
                    runs += 1
                    if res is not None and (best is None or res[0] < best[0]):
                        best = (res[0], res[1], family)
                stats["budget"] = budget
                stats["runs"] = runs
                if final or (best is not None and best[0] // big <= budget):
                    break
                if best is not None:
                    budget = best[0] // big  # an upper bound on the optimal excess
                else:
                    budget = 2 if budget == 0 else 2 * budget
    except _Stop as stop:
        return None, done("TIMEOUT", stopped=stop.reason)
    if best is None:
        return None, done("INFEASIBLE")
    cost, edges, family = best
    excess, tiles = divmod(cost, big)
    solution = Solution(edges=edges, pairs={p: list(family[p]) for p in instance.ports})
    report = verify.check(instance, solution)
    assert report.ok, report.errors
    assert (report.excess, report.tiles) == (excess, tiles), (
        f"certificate cost {(excess, tiles)} != verified cost {(report.excess, report.tiles)}")
    return solution, done("OPTIMAL", excess=excess, tiles=tiles)
