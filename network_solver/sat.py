"""CNF-SAT (the known problem K) and the reduction Train Network -> SAT.

This module mirrors `lean/TrainNetwork/` (see docs/result.md):

* A CNF formula is a list of clauses, a clause is a list of literals, and a literal is a
  pair ``(var, polarity)`` with ``var`` a natural number.
* ``to_sat(instance, X, K)`` is the many-one reduction `toK`: the formula it yields is
  satisfiable iff the instance has a feasible solution with total excess <= X and at
  most K track tiles.

The formula is produced lazily (a generator of clauses) because it has
Theta(|P| * N^2) clauses, where N = W * H.
"""
from __future__ import annotations

from typing import Iterable, Iterator

from network_solver.instance import Cell, Instance

Lit = tuple[int, bool]
Clause = list[Lit]


def pair(a: int, b: int) -> int:
    """`Nat.pair` from Mathlib: an injective map N x N -> N."""
    return b * b + a if a < b else a * a + a + b


def cell_code(c: Cell) -> int:
    return pair(c[0], c[1])


# Variable families. Tags match lean/TrainNetwork/Encode.lean.
def v_edge(u: Cell, v: Cell) -> int:
    cu, cv = cell_code(u), cell_code(v)
    return pair(0, pair(min(cu, cv), max(cu, cv)))


def v_sel(p: Cell, c: Cell) -> int:
    return pair(1, pair(cell_code(p), cell_code(c)))


def v_grid(p: Cell, t: int, v: Cell) -> int:
    return pair(2, pair(cell_code(p), pair(t, cell_code(v))))


def v_net(p: Cell, t: int, v: Cell) -> int:
    return pair(3, pair(cell_code(p), pair(t, cell_code(v))))


def v_step(p: Cell, t: int, v: Cell, u: Cell) -> int:
    return pair(4, pair(cell_code(p), pair(t, pair(cell_code(v), cell_code(u)))))


def v_tile(x: Cell) -> int:
    return pair(5, cell_code(x))


def v_count(tag: int, i: int, j: int) -> int:
    """Counter variable (i, j) of the cardinality gadget number `tag`."""
    return pair(6, pair(tag, pair(i, j)))


def at_most(items: Iterable[list[Lit]], bound: int, tag: int) -> Iterator[Clause]:
    """Sequential counter: at most `bound` of the items are active, where an item (a
    list of literals) is active iff all its literals are true.

    Counter variable s(i, j) reads "more than j of the first i items are active".
    """
    m = 0
    for i, item in enumerate(items):
        neg = [(v, not pol) for v, pol in item]
        for j in range(bound + 1):
            yield [(v_count(tag, i, j), False), (v_count(tag, i + 1, j), True)]
            if j == 0:
                yield neg + [(v_count(tag, i + 1, 0), True)]
            else:
                yield neg + [(v_count(tag, i, j - 1), False), (v_count(tag, i + 1, j), True)]
        m = i + 1
    yield [(v_count(tag, m, bound), False)]


def grid_neighbours(inst: Instance, v: Cell) -> list[Cell]:
    x, y = v
    out = [(x + 1, y), (x, y + 1)]
    if x >= 1:
        out.append((x - 1, y))
    if y >= 1:
        out.append((x, y - 1))
    return [u for u in out if inst.in_bounds(u)]


def to_sat(inst: Instance, X: int, K: int) -> Iterator[Clause]:
    """The reduction `toK`. Yields the clauses of the formula."""
    W, H = inst.width, inst.height
    T = W * H
    cells = [(x, y) for x in range(W) for y in range(H)]
    ports = [c for c in cells if c in set(inst.ports.values())]
    cities = [c for c in cells if c in set(inst.cities.values())]
    terminals = inst.terminals

    def is_open(c: Cell) -> bool:
        return inst.in_bounds(c) and c not in inst.blocked

    def is_free(c: Cell) -> bool:
        return is_open(c) and c not in terminals

    # (1) Edges join open cells; (2) a free cell has at most 3 network neighbours;
    # (3) a free cell touched by an edge is a tile.
    for v in cells:
        x, y = v
        for u in ((x + 1, y), (x, y + 1)):
            if not (is_open(v) and is_open(u)):
                yield [(v_edge(v, u), False)]
            else:
                if is_free(v):
                    yield [(v_edge(v, u), False), (v_tile(v), True)]
                if is_free(u):
                    yield [(v_edge(v, u), False), (v_tile(u), True)]
        if is_free(v) and x >= 1 and y >= 1:
            yield [(v_edge(v, u), False)
                   for u in ((x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1))]

    for p in ports:
        # (4) g(p, t, v) <-> gridDist(p, v) <= t, by the BFS recurrence.
        # (5) r(p, t, v)  -> netDist(p, v) <= t, with step witnesses.
        for v in cells:
            if v == p:
                yield [(v_grid(p, 0, v), True)]
            else:
                yield [(v_grid(p, 0, v), False)]
                yield [(v_net(p, 0, v), False)]
        for t in range(T):
            for v in cells:
                nbrs = [u for u in grid_neighbours(inst, v) if u == p or is_free(u)]
                gsteps = [u for u in nbrs if is_open(u) and is_open(v)]
                yield ([(v_grid(p, t + 1, v), False), (v_grid(p, t, v), True)]
                       + [(v_grid(p, t, u), True) for u in gsteps])
                yield [(v_grid(p, t, v), False), (v_grid(p, t + 1, v), True)]
                for u in gsteps:
                    yield [(v_grid(p, t, u), False), (v_grid(p, t + 1, v), True)]
                yield ([(v_net(p, t + 1, v), False), (v_net(p, t, v), True)]
                       + [(v_step(p, t, v, u), True) for u in nbrs])
                for u in nbrs:
                    yield [(v_step(p, t, v, u), False), (v_net(p, t, u), True)]
                    yield [(v_step(p, t, v, u), False), (v_edge(u, v), True)]
        # (6) Chosen cities are reachable in the grid and in the network.
        for c in cities:
            yield [(v_sel(p, c), False), (v_grid(p, T, c), True)]
            yield [(v_sel(p, c), False), (v_net(p, T, c), True)]
        # (7) No chosen city is farther than an unchosen one.
        for c in cities:
            for c2 in cities:
                for t in range(T + 1):
                    yield [(v_sel(p, c), False), (v_sel(p, c2), True),
                           (v_grid(p, t, c2), False), (v_grid(p, t, c), True)]
        # (8) Exactly k cities are chosen.
        pc = cell_code(p)
        yield from at_most(([(v_sel(p, c), True)] for c in cities), inst.k, pair(0, pc))
        yield from at_most(([(v_sel(p, c), False)] for c in cities),
                           len(cities) - inst.k, pair(1, pc))

    # (9) Total excess <= X: one unit per (p, c, t) with gridDist <= t < netDist.
    yield from at_most(
        ([(v_sel(p, c), True), (v_grid(p, t, c), True), (v_net(p, t, c), False)]
         for p in ports for c in cities for t in range(T)),
        X, pair(2, 0))
    # (10) At most K tiles.
    yield from at_most(([(v_tile(x), True)] for x in cells), K, pair(3, 0))


def formula_size(clauses: Iterable[Clause]) -> int:
    """Encoding length of a formula: one symbol per clause plus, for every literal, a
    sign and the binary length of its variable (`KInstance.size` in Lean)."""
    return sum(1 + sum(1 + v.bit_length() for v, _ in cl) for cl in clauses)


def lean_string(clauses: Iterable[Clause]) -> str:
    """The formula as Lean prints `(toK I X K).val.clauses` with `toString`."""
    return "[" + ", ".join(
        "[" + ", ".join(f"({v}, {'true' if pol else 'false'})" for v, pol in cl) + "]"
        for cl in clauses) + "]"


def satisfiable(clauses: Iterable[Clause], time_limit: float = 600.0,
                workers: int = 8) -> dict[int, bool] | None:
    """Decides a CNF formula with CP-SAT used as a plain SAT solver. Returns a
    satisfying assignment (variable -> bool) or None."""
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    var: dict[int, cp_model.IntVar] = {}

    def lit(v: int, pol: bool):
        if v not in var:
            var[v] = model.new_bool_var("")
        return var[v] if pol else var[v].negated()

    for cl in clauses:
        model.add_bool_or([lit(v, pol) for v, pol in cl])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    status = solver.solve(model)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return {v: bool(solver.value(x)) for v, x in var.items()}
    if status == cp_model.INFEASIBLE:
        return None
    raise RuntimeError(f"SAT solver stopped with status {solver.status_name(status)}")


def check_assignment(clauses: Iterable[Clause], assignment: dict[int, bool]) -> bool:
    return all(any(assignment.get(v, False) == pol for v, pol in cl) for cl in clauses)

