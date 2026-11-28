"""Exact frontier ("plug") dynamic program for the problem in docs/problem.md.

Walk formulation
----------------
Fix a tie choice. It gives a list D of demand pairs (p_j, c_j), j = 0..m-1 (port cell,
city cell). A *routing* gives each pair j a simple path P_j from p_j to c_j in the grid,
over non-blocked in-bounds cells, whose interior cells are all free: P_j touches no
terminal other than its own two endpoints. The routing is *admissible* if at every free
cell at most 3 of its 4 incident grid edges are used by the union of all paths
(different paths may share edges and cells freely). Its cost is the pair

    (sum_j |P_j| in edges,  number of free cells lying on at least one path),

compared lexicographically. The optimum of the original problem equals the minimum of
this cost over all tie choices and admissible routings, with
excess = sum_j |P_j| - sum_j d(p_j, c_j); the union of the paths together with that tie
choice is an optimal Solution. (This equivalence is proved elsewhere; this module only
implements the search.)

The dynamic program
-------------------
Cells are swept in row-major order when W <= H. When W > H the instance is transposed,
solved and the solution transposed back (a column-major sweep), so the frontier always
has min(W, H) vertical plugs plus 1 horizontal plug. After a cell is processed, the
*frontier edges* are the grid edges between processed and unprocessed cells.

State: for each path j, a tuple over the frontier edges. An entry says whether path j
uses that edge (a *plug*) and, if so, which *fragment* of P_j it belongs to. A fragment
is a connected piece of P_j among the processed cells. It has either two open ends on
the frontier (a *pair label* occurring exactly twice), or one open end and its other
end at p_j (tag S) or at c_j (tag T). Labels are canonical: 0 = unused, 1 = S, 2 = T,
3.. = pair labels numbered by first occurrence, so equal configurations are equal
tuples. The DP value of a state is the lexicographically minimal
(total edges so far, tiles so far).

Transition at a cell v, with incoming frontier edges up/left and outgoing right/down:

* v blocked: no path may have an incoming plug; nothing is created.
* Otherwise every path j independently chooses its edges at v:
  - v = p_j (tag S) or v = c_j (tag T): exactly one incident edge is used by j. If
    there is exactly one incoming plug it is that edge; if there is none, exactly one
    of right/down is created; two incoming plugs are invalid. The fragment gets the
    tag. If the incoming fragment already carries the other tag, the path is complete,
    and then it must have no other plug left (otherwise invalid).
  - v a terminal that is not an endpoint of j: j may not use v (incoming plug: invalid).
  - v free: j uses 0 or 2 edges at v. Two incoming plugs: the two fragments are joined
    (same pair label: a cycle, invalid; S with T: the path is complete and must have no
    other plug). One incoming plug: extend it right or down. None: either nothing, or
    a new fragment using both right and down.
* A created plug must lead to an in-bounds, non-blocked cell that is free or an
  endpoint of that same path.
* Degree: if v is free, at most 3 of its 4 edges may be used by at least one path.
* Cost: +1 edge for every (path, created plug); +1 tile if v is free and at least one
  path uses it.

After the last cell there are no frontier edges, and the state in which every path is
complete carries the optimum for this tie choice. The edge set is rebuilt by following
parent pointers: the plugs that the chosen transition leaves at v are exactly the used
edges from v to its right and lower neighbours.

Corridors and the slack certificate (same idea as cpsat.py)
-----------------------------------------------------------
With a slack X, path j may only use a cell u if dp_j(u) + dc_j(u) <= d_j + X, where
dp_j / dc_j are `distances.bfs` distances from p_j / c_j and d_j = d(p_j, c_j).
The outer loop runs the DP over all tie choices for X = 0, 2, 4, 8, ... (the step after
0 is 2; an excess is always even because the grid is bipartite):

* a best routing with excess <= X is globally optimal, because any routing at least as
  good has every pair's excess <= its total excess <= X, hence lies in the corridors;
* a best routing with excess > X: set X = max(2 X, found excess) and repeat;
* nothing found: double X. Once X >= W*H and still nothing is found, the instance is
  infeasible: a simple path has fewer than W*H edges, so every cell u on any valid
  path for pair j has dp_j(u) + dc_j(u) < W*H and passes the corridor test.

Further pruning
---------------
Each rule only discards states that cannot lead to an admissible routing of total
excess <= X inside the corridors. The soundness arguments are in the comments.

  R1  Edge budget (`_Path.remaining`, `_joint_moves`, `_sweep`). A state is dropped when
      (edges so far) + (a lower bound on the edges its paths still have to create)
      exceeds sum_j d_j + X. With R1 a round returns the best routing of total excess
      <= X inside the corridors, or nothing. Compared with the loop above, this only
      turns the outcome "found, but excess > X" into "nothing found", and both lead to
      a larger X. The infeasibility verdict is the one place where "nothing found" has
      to mean "no routing at all", so there the round is repeated without R1 first.
  R2  A completed path creates no new fragment (`_Path._choices`).

Three implementation shortcuts are not pruning. A cell that lies in no path's corridor
(blocked cells in particular) leaves every state unchanged and is skipped. A path whose
corridor does not contain v is not touched at v. Parent pointers are stored as (position
of the parent state, number of the move taken); the edges are rebuilt by replaying the
moves.

Complexity
----------
A path's frontier tuple has min(W, H) + 1 entries with labels at most
(min(W, H) + 1) / 2 + 2, so there are 2^{O(m * min(W, H) * log min(W, H))} states, each
with at most 2^m transitions per cell. For one tie choice and one slack the running
time is therefore 2^{O(m * min(W, H) * log min(W, H))} * poly(N), N = W * H; the slack
loop multiplies this by O(log N).

  python -m network_solver.frontier INSTANCE.json [--max-states N] [--out SOLUTION] [--quiet]
"""
from __future__ import annotations

import argparse
import itertools
import json
import signal
import sys
import time
from array import array
from typing import Callable

from network_solver import verify
from network_solver.distances import PortRequirement, bfs, requirements
from network_solver.instance import Cell, Instance, Solution

INF = float("inf")
S, T = 1, 2  # fragment tags; pair labels are 3, 4, ...
UP, LEFT, RIGHT, DOWN = 1, 2, 4, 8  # the four edges of a cell, as a bit mask
POPCOUNT = [bin(mask).count("1") for mask in range(16)]


class StateLimit(RuntimeError):
    """The frontier held more than `max_states` states: the solver did not finish.

    `info` says where: slack, tie choice, cell index and coordinates, states, seconds.
    """

    def __init__(self, info: dict):
        super().__init__(
            f"more than {info['max_states']} frontier states at cell {info['cell']} "
            f"of {info['cells']} (slack {info['slack']}, tie choice {info['tie_choice']} "
            f"of {info['tie_choices']})"
        )
        self.info = info


class _Grid:
    """The grid in sweep order (cell (x, y) has index y * W + x) and the table that
    gives every canonical path state (a label tuple of length W + 1) a small integer id.
    Entry x < W of a tuple is the vertical plug in column x, entry W the horizontal one.
    """

    def __init__(self, instance: Instance, transposed: bool = False):
        self.instance = instance  # already transposed if `transposed`
        self.transposed = transposed
        self.W, self.H = instance.width, instance.height
        self.N = self.W * self.H
        self.cells = [(x, y) for y in range(self.H) for x in range(self.W)]
        self.free = [instance.is_free(cell) for cell in self.cells]
        self.tuples: list[tuple[int, ...]] = [(0,) * (self.W + 1)]  # id 0: no plug
        self.ids = {self.tuples[0]: 0}
        self._distances: dict[Cell, list] = {}

    def state_id(self, labels: list[int]) -> int:
        """Canonicalises `labels` (pair labels renumbered by first occurrence)."""
        rename: dict[int, int] = {}
        canonical = tuple(
            a if a <= T else rename.setdefault(a, len(rename) + 3) for a in labels
        )
        sid = self.ids.get(canonical)
        if sid is None:
            sid = self.ids[canonical] = len(self.tuples)
            self.tuples.append(canonical)
        return sid

    def original(self, v: int) -> Cell:
        """Cell index -> coordinates in the instance the caller passed to `solve`."""
        x, y = self.cells[v]
        return (y, x) if self.transposed else (x, y)

    def distances(self, source: Cell) -> list:
        """`distances.bfs` from a terminal, as a list over cell indices (INF = unreached)."""
        if source not in self._distances:
            dist = bfs(self.instance, source)
            self._distances[source] = [dist.get(cell, INF) for cell in self.cells]
        return self._distances[source]


class _Path:
    """One demand pair (p, c) under a fixed slack: its corridor and its transitions.

    The transitions of a path depend only on the cell and on the path's own frontier
    tuple, so they are memoised here and shared by all joint states and tie choices.
    """

    def __init__(self, grid: _Grid, port: Cell, city: Cell, slack: int):
        self.grid = grid
        self.p, self.c = grid.cells.index(port), grid.cells.index(city)
        self.dp, self.dc = grid.distances(port), grid.distances(city)
        self.d = self.dp[self.c]
        # The corridor: cells path j may use. Free cells and its own two endpoints
        # only, and dp + dc <= d + slack.
        self.inside = [
            (grid.free[u] or u in (self.p, self.c)) and self.dp[u] + self.dc[u] <= self.d + slack
            for u in range(grid.N)
        ]
        self._memo: dict[tuple[int, int], tuple] = {}

    def choices(self, v: int, sid: int) -> tuple:
        """The path's possible moves at corridor cell `v` from state `sid`, as tuples
        (new state id, mask of the edges of v it uses, plugs created, change of
        `remaining`). Empty when the state is invalid at v."""
        found = self._memo.get((v, sid))
        if found is None:
            old = self.grid.tuples[sid]
            before = self.remaining(v - 1, old)
            moves = []
            for labels, mask, created in self._choices(v, old):
                new = self.grid.state_id(labels)
                after = self.remaining(v, self.grid.tuples[new])
                moves.append((new, mask, created, after - before))
            found = self._memo[(v, sid)] = tuple(moves)
        return found

    def _choices(self, v: int, old: tuple[int, ...]) -> list[tuple[list[int], int, int]]:
        W = self.grid.W
        x = v % W
        up, left = old[x], old[W]
        # A created plug must lead to a cell of the corridor (in bounds, not blocked,
        # free or an endpoint of this path).
        right_ok = x + 1 < W and self.inside[v + 1]
        down_ok = v + W < self.grid.N and self.inside[v + W]
        rest = list(old)
        rest[x] = rest[W] = 0  # the incoming plugs end at v
        out: list[tuple[list[int], int, int]] = []

        def create(label: int, right: bool, down: bool, incoming: int) -> None:
            new = list(rest)
            if right:
                new[W] = label
            if down:
                new[x] = label
            out.append((new, incoming | (RIGHT if right else 0) | (DOWN if down else 0),
                        right + down))

        if v in (self.p, self.c):  # an endpoint: exactly one edge of v is used
            tag = S if v == self.p else T
            if up and left:
                return []
            label = up or left
            if not label:
                if right_ok:
                    create(tag, True, False, 0)
                if down_ok:
                    create(tag, False, True, 0)
            elif label == 3 - tag:  # the fragment from the other endpoint arrives
                if not any(rest):  # complete; any other plug left would be invalid
                    out.append((rest, UP if up else LEFT, 0))
            elif label > T:  # a pair fragment arrives: its other end now carries the tag
                rest[rest.index(label)] = tag
                out.append((rest, UP if up else LEFT, 0))
            return out

        # A free cell: 0 or 2 edges of v are used.
        if up and left:
            if up == left:
                return []  # the two ends of one fragment: a cycle
            if up <= T and left <= T:  # S meets T
                if any(rest):
                    return []  # complete, but another plug is left
            elif up <= T:
                rest[rest.index(left)] = up
            elif left <= T:
                rest[rest.index(up)] = left
            else:  # two pair fragments become one
                rest[rest.index(left)] = up
            out.append((rest, UP | LEFT, 0))
        elif up or left:
            incoming = UP if up else LEFT
            if right_ok:
                create(up or left, True, False, incoming)
            if down_ok:
                create(up or left, False, True, incoming)
        else:
            out.append((rest, 0, 0))
            # R2: a completed path creates no new fragment. A path with both endpoints
            # processed and no plug is complete (after p_j is processed the S fragment
            # keeps an open end until it meets T). A new fragment of a complete path
            # has a pair label and no S or T fragment is left to absorb it, so its two
            # ends could only ever be joined to each other, which is a cycle: such a
            # state never reaches the final state.
            complete = self.p < v and self.c < v and not any(old)
            if right_ok and down_ok and not complete:
                create(max(max(old), T) + 1, True, True, 0)
        return out

    def remaining(self, cut: int, labels: tuple[int, ...]) -> int:
        """R1, the lower bound. With cells 0..cut processed and path state `labels`,
        returns a lower bound on the number of plugs this path still has to create.

        Soundness: plugs are counted when created, so what remains are the edges of
        P_j with both ends unprocessed. They form sub-paths of P_j among the
        unprocessed cells; each starts at the unprocessed end u of a plug ("target")
        and ends at another target or at an unprocessed endpoint of the path.
        * No plug and no endpoint processed: all of P_j remains, at least d edges.
        * p (resp. c) unprocessed and plugs present: the sub-path from p (resp. c) to
          the first processed cell ends at a target u and has free interior cells, so
          it has at least dp(u) (resp. dc(u)) edges; take the minimum over targets.
          With both unprocessed these are two different sub-paths, so the bounds add.
        * Both processed and exactly two plugs: they are the S and the T end, joined
          by one sub-path between the two targets: at least their Manhattan distance.
        """
        p_done, c_done = self.p <= cut, self.c <= cut
        if not any(labels):
            return 0 if p_done or c_done else self.d
        W = self.grid.W
        x, y = cut % W, cut // W
        # The unprocessed end of the vertical plug in column col is the first
        # unprocessed cell of that column; the horizontal plug leads to cell cut + 1.
        targets = [col + (y + 1 if col <= x else y) * W for col in range(W) if labels[col]]
        if labels[W]:
            targets.append(cut + 1)
        if p_done and c_done:
            if len(targets) != 2:
                return 0
            a, b = targets
            return abs(a % W - b % W) + abs(a // W - b // W)
        bound = 0
        if not p_done:
            bound += min(self.dp[u] for u in targets)
        if not c_done:
            bound += min(self.dc[u] for u in targets)
        return bound


class _Run:
    """Bookkeeping shared by all sweeps of one `solve` call."""

    def __init__(self, grid: _Grid, max_states: int | None,
                 progress: Callable[[dict], None] | None):
        self.grid = grid
        self.max_states = max_states
        self.progress = progress
        self.start = time.perf_counter()
        self.states_peak = 1
        self.slack = 0
        self.budget = True  # is rule R1 active in the current sweep?
        self.tie_choice = 0
        self.tie_choices = 0
        self.paths = 0
        self.building: tuple[int, dict] = (0, {})  # the cell being processed, its new layer

    def seconds(self) -> float:
        return round(time.perf_counter() - self.start, 3)

    def info(self, v: int, states: int) -> dict:
        return {
            "slack": self.slack, "budget": self.budget, "tie_choice": self.tie_choice,
            "tie_choices": self.tie_choices, "paths": self.paths,
            "cell": v, "cells": self.grid.N, "cell_xy": list(self.grid.original(v)),
            "states": states, "states_peak": max(self.states_peak, states),
            "max_states": self.max_states, "seconds": self.seconds(),
        }


def _joint_moves(paths: list[_Path], active: list[int], v: int, sub: tuple[int, ...],
                 free: bool, big: int, room) -> list[tuple[tuple[int, ...], int, int]]:
    """All joint moves of the active paths at cell v from their states `sub`, as tuples
    (new state ids of the active paths, change of the DP key, growth). The DP key is
    edges * big + tiles; *growth* is the change of (edges so far + sum of the paths'
    `remaining` bounds). The result is a deterministic function of the arguments.

    R1 is applied here: only moves with growth <= `room` are returned (`room` is the
    budget minus the state's current edges + remaining bounds; INF without a budget).
    """
    options = [paths[j].choices(v, sid) for j, sid in zip(active, sub)]
    # least[i]: the least growth the paths i, i+1, ... can contribute together, so a
    # partial combination that already needs more than room - least[i] can be dropped.
    least = [0] * (len(options) + 1)
    for i in reversed(range(len(options))):
        if not options[i]:
            return []  # some path has no valid move: the state is invalid at v
        least[i] = least[i + 1] + min(c + delta for _, _, c, delta in options[i])
    partial = [((), 0, 0, 0)]  # (new ids, union of edge masks, plugs created, growth)
    for i, choices in enumerate(options):
        allowed = room - least[i + 1]
        partial = [
            (new + (new_sid,), used | mask, created + c, growth + c + delta)
            for new, used, created, growth in partial
            for new_sid, mask, c, delta in choices
            # R1, and the degree rule: a free cell has at most 3 used edges.
            if growth + c + delta <= allowed and (not free or POPCOUNT[used | mask] <= 3)
        ]
    # +1 tile if v is free and at least one path uses it.
    return [(new, created * big + (1 if free and used else 0), growth)
            for new, used, created, growth in partial]


def _sweep(grid: _Grid, paths: list[_Path], limit: int | None,
           run: _Run) -> tuple[int, int, set[tuple[int, int]]] | None:
    """The DP for one tie choice. Returns (edges, tiles, used grid edges as pairs of
    cell indices) of a cheapest admissible routing inside the corridors that has at
    most `limit` edges in total (no limit if None), or None if there is none."""
    W, N, big = grid.W, grid.N, grid.N + 1  # big > any tile count
    m = len(paths)
    # R1, the budget: a state is discarded when
    #     edges so far + sum_j paths[j].remaining(...) > limit = sum_j d_j + slack.
    # Every completion of such a state has more than `limit` edges, i.e. total excess
    # > slack, and the certificate of a round only speaks about routings of total
    # excess <= slack. `lowers` holds the left-hand side for every state. It is the
    # state's edge count plus a function of the state, so it adds nothing to the state.
    budget = INF if limit is None else limit
    states: list[tuple[int, ...]] = [(0,) * m]  # per path the id of its frontier tuple
    keys = [0]  # DP value: edges so far * big + tiles so far
    lowers = [sum(path.d for path in paths)]
    history = []  # per processed cell: (cell, active paths, parent positions, move numbers)
    for v in range(N):
        active = [j for j in range(m) if paths[j].inside[v]]
        if not active:
            continue  # no path may touch v: every state stays as it is
        free = grid.free[v]
        everyone = len(active) == m
        memo: dict[tuple, list] = {}  # _joint_moves at this cell
        memo_size = 0
        index: dict[tuple[int, ...], int] = {}  # new state -> position in the new layer
        new_keys: list[int] = []
        new_lowers: list[int] = []
        parents, picks = array("i"), array("i")
        run.building = (v, index)
        for pos, state in enumerate(states):
            sub = state if everyone else tuple([state[j] for j in active])
            key, lower = keys[pos], lowers[pos]
            room = budget - lower
            moves = memo.get((sub, room))
            if moves is None:
                moves = _joint_moves(paths, active, v, sub, free, big, room)
                if memo_size < _MEMO_LIMIT:  # a cache only; the cap bounds its memory
                    memo[sub, room] = moves
                    memo_size += 1 + len(moves)
            for number, (new_sub, dkey, growth) in enumerate(moves):
                if everyone:
                    successor = new_sub
                else:
                    successor = list(state)
                    for j, sid in zip(active, new_sub):
                        successor[j] = sid
                    successor = tuple(successor)
                at = index.get(successor)
                if at is None:
                    index[successor] = len(new_keys)
                    new_keys.append(key + dkey)
                    new_lowers.append(lower + growth)
                    parents.append(pos)
                    picks.append(number)
                elif key + dkey < new_keys[at]:
                    new_keys[at] = key + dkey
                    new_lowers[at] = lower + growth
                    parents[at] = pos
                    picks[at] = number
            if run.max_states is not None and len(index) > run.max_states:
                raise StateLimit(run.info(v, len(index)))
        states, keys, lowers = list(index), new_keys, new_lowers
        history.append((v, active, parents, picks))
        run.states_peak = max(run.states_peak, len(states))
        if run.progress is not None:
            run.progress(run.info(v, len(states)))
        if not states:
            return None
    # No frontier edge is left, so every path has the empty tuple: all are complete.
    assert states == [(0,) * m] and lowers == [keys[0] // big], states

    # Reconstruction. Follow the parent pointers backwards to learn which move was
    # taken at every processed cell, then replay those moves from the start. The plugs
    # a path has in v's column and at the horizontal position right after v is
    # processed are exactly its edges from v downwards and to the right.
    trail = []
    at = 0
    for v, active, parents, picks in reversed(history):
        trail.append((v, active, picks[at]))
        at = parents[at]
    edges = set()
    state = [0] * m
    lower = sum(path.d for path in paths)
    for v, active, number in reversed(trail):
        sub = tuple([state[j] for j in active])
        moves = _joint_moves(paths, active, v, sub, grid.free[v], big, budget - lower)
        new_sub, _, growth = moves[number]
        lower += growth
        for j, sid in zip(active, new_sub):
            state[j] = sid
            labels = grid.tuples[sid]
            if labels[v % W]:
                edges.add((v, v + W))
            if labels[W]:
                edges.add((v, v + 1))
    return keys[0] // big, keys[0] % big, edges


_MEMO_LIMIT = 1_000_000  # joint moves memoised per cell (a cache; bounds memory only)


def _transpose(instance: Instance) -> Instance:
    def flip(cell: Cell) -> Cell:
        return (cell[1], cell[0])

    return Instance(
        width=instance.height,
        height=instance.width,
        blocked=frozenset(flip(c) for c in instance.blocked),
        ports={name: flip(c) for name, c in instance.ports.items()},
        cities={name: flip(c) for name, c in instance.cities.items()},
        k=instance.k,
    )


def _tie_choices(reqs: dict[str, PortRequirement]) -> list[dict[str, list[str]]]:
    """Every valid selection: per port, the required cities plus `choose` tied ones."""
    per_port = [
        [list(req.required) + list(extra)
         for extra in itertools.combinations(req.tied, req.choose)]
        for req in reqs.values()
    ]
    return [dict(zip(reqs, combo)) for combo in itertools.product(*per_port)]


def _best_routing(grid: _Grid, choices: list[dict[str, list[str]]], slack: int,
                  budget: bool, run: _Run):
    """Runs the DP for every tie choice with corridors of the given slack. Returns
    ((excess, tiles), used edges, tie choice) of the best routing found, or None."""
    inst = grid.instance
    run.slack, run.budget = slack, budget
    cache: dict[tuple[str, str], _Path] = {}  # a pair's transitions do not depend on the tie choice
    best = None
    for number, pairs in enumerate(choices, 1):
        run.tie_choice = number
        paths = []
        for port, cities in pairs.items():
            for city in cities:
                if (port, city) not in cache:
                    cache[port, city] = _Path(grid, inst.ports[port], inst.cities[city], slack)
                paths.append(cache[port, city])
        run.paths = len(paths)
        total_d = sum(path.d for path in paths)  # the same for every tie choice
        found = _sweep(grid, paths, total_d + slack if budget else None, run)
        if found is not None:
            cost = (found[0] - total_d, found[1])
            if best is None or cost < best[0]:
                best = (cost, found[2], pairs)
    return best


def solve(instance: Instance, max_states: int | None = None,
          progress: Callable[[dict], None] | None = None) -> tuple[Solution | None, dict]:
    """Returns (optimal solution, stats) with stats["optimal"] == True, or (None, stats)
    with stats["status"] == "INFEASIBLE" when no feasible network exists (including the
    case where some port reaches fewer than k cities).

    Raises `StateLimit` as soon as a frontier holds more than `max_states` states.
    `progress`, if given, is called with a dict after every processed cell.
    """
    transposed = instance.width > instance.height  # sweep along the longer side
    inst = _transpose(instance) if transposed else instance
    grid = _Grid(inst, transposed)
    run = _Run(grid, max_states, progress)
    try:
        choices = _tie_choices(requirements(inst))
    except ValueError:  # a port reaches fewer than k cities
        return None, {"status": "INFEASIBLE", "slack": 0, "states_peak": 0,
                      "seconds": run.seconds()}
    run.tie_choices = len(choices)

    slack = rounds = 0
    try:
        while True:
            rounds += 1
            best = _best_routing(grid, choices, slack, True, run)
            if best is None and slack >= grid.N:
                # With R1 an empty round only says "no routing of total excess <= slack".
                # Infeasibility needs the round without R1: the corridors of this slack
                # exclude no valid path, so then nothing found means no routing at all.
                best = _best_routing(grid, choices, slack, False, run)
                if best is None:
                    return None, {"status": "INFEASIBLE", "slack": slack,
                                  "states_peak": run.states_peak, "seconds": run.seconds()}
            if best is None:
                slack = max(2 * slack, 2)
            elif best[0][0] <= slack:
                break  # the slack certificate holds
            else:
                slack = max(2 * slack, best[0][0])
    except KeyboardInterrupt:
        if progress is not None:  # say where the sweep was stopped
            v, layer = run.building
            progress({**run.info(v, len(layer)), "interrupted": True})
        raise

    (excess, tiles), edges, pairs = best
    solution = Solution(
        edges={frozenset((grid.original(a), grid.original(b))) for a, b in edges},
        pairs={port: list(cities) for port, cities in pairs.items()},
    )
    stats = {
        "status": "OPTIMAL", "optimal": True, "excess": excess, "tiles": tiles,
        "slack": slack, "states_peak": run.states_peak, "seconds": run.seconds(),
        "paths": run.paths, "tie_choices": len(choices), "rounds": rounds,
    }
    return solution, stats


def _progress_line(info: dict) -> str:
    x, y = info["cell_xy"]
    return (f"[frontier] slack {info['slack']}{'' if info['budget'] else ' (no budget)'}, "
            f"tie choice {info['tie_choice']}/{info['tie_choices']}, {info['paths']} paths, "
            f"cell {info['cell']}/{info['cells']} (x={x}, y={y}): {info['states']} states "
            f"(peak {info['states_peak']}), {info['seconds']:.1f} s"
            f"{' -- interrupted' if info.get('interrupted') else ''}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m network_solver.frontier",
                                     description="Exact frontier dynamic program.")
    parser.add_argument("instance")
    parser.add_argument("--max-states", type=int,
                        help="give up when a frontier holds more states than this")
    parser.add_argument("--out", help="write the solution JSON here")
    parser.add_argument("--quiet", action="store_true", help="no progress lines on stderr")
    parser.add_argument("--progress-every", type=float, default=5.0, metavar="SECONDS")
    args = parser.parse_args(argv)

    instance = Instance.load(args.instance)
    last: dict = {}
    due = [0.0]

    def progress(info: dict) -> None:
        last.clear()
        last.update(info)
        if not args.quiet and (info["seconds"] >= due[0] or info.get("interrupted")):
            due[0] = info["seconds"] + args.progress_every
            print(_progress_line(info), file=sys.stderr, flush=True)

    try:
        solution, stats = solve(instance, max_states=args.max_states, progress=progress)
    except StateLimit as stop:
        if not args.quiet:
            print(_progress_line(stop.info), file=sys.stderr, flush=True)
        print(json.dumps({"status": "STATE_LIMIT", "optimal": False, **stop.info}), flush=True)
        return 2
    except KeyboardInterrupt:
        print(json.dumps({"status": "INTERRUPTED", "optimal": False, **last}), flush=True)
        return 130
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


def _interrupt(signum, frame):
    raise KeyboardInterrupt


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, _interrupt)  # so `timeout` still gets a final report
    sys.exit(main())
