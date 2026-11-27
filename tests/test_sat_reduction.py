"""The reduction Train Network -> SAT (`network_solver.sat.to_sat`) against the CP-SAT
oracle, on random instances of varied sizes, with and without blocked cells and ties.

For every instance and every query (X, K):
  * the formula is satisfiable  iff  the oracle says "yes";
  * a satisfying assignment decodes to a network that the independent verifier accepts,
    with excess <= X and at most K tiles.
"""
from __future__ import annotations

import hashlib
import itertools
import random

import pytest

from network_solver import cpsat, sat, verify
from network_solver.decide import decide_cpsat, decide_sat
from network_solver.distances import requirements
from network_solver.generate import random_instance
from network_solver.instance import Instance

N_INSTANCES = 210


def make_instance(seed: int) -> Instance:
    rng = random.Random(7919 * seed + 13)
    for _ in range(100):
        width = rng.choice([2, 3, 3, 4, 4, 5, 5, 6])
        height = rng.choice([2, 3, 3, 4, 4, 5])
        ports = rng.choice([1, 1, 2, 2, 3])
        cities = rng.choice([1, 2, 2, 3, 3, 4, 5])
        if ports + cities > width * height:
            continue
        k = rng.randint(1, cities)
        blocked = rng.choice([0.0, 0.0, 0.1, 0.2, 0.3])
        try:
            return random_instance(width, height, ports, cities, k, blocked,
                                   seed=rng.randrange(10**9), max_tries=50)
        except RuntimeError:
            continue
    raise AssertionError("could not generate an instance")


def queries(inst: Instance, seed: int) -> list[tuple[int, int]]:
    rng = random.Random(seed)
    cells = inst.width * inst.height
    sol, stats = cpsat.solve(inst, time_limit=60)
    if sol is None:  # no feasible network at all
        return [(0, 0), (cells, cells)]
    assert stats["optimal"], stats
    excess, tiles = stats["excess"], stats["tiles"]
    out = [(excess, tiles), (rng.randint(0, excess + 3), rng.randint(0, tiles + 2))]
    if tiles > 0:
        out.append((excess, tiles - 1))                      # a "no" by lexicographic optimality
        out.append((excess + 2 * rng.randint(1, 2), tiles - 1))  # trade excess for tiles
    if excess > 0:
        out.append((excess - 1, cells))                      # a "no": excess below the minimum
    return out


@pytest.mark.parametrize("seed", range(N_INSTANCES))
def test_to_sat_agrees_with_cpsat(seed):
    inst = make_instance(seed)
    for X, K in queries(inst, seed):
        expected = decide_cpsat(inst, X, K)
        answer, witness = decide_sat(inst, X, K)
        assert answer == expected, (inst.to_json(), X, K, expected)
        if answer:
            report = verify.check(inst, witness)
            assert report.ok, (report.errors, inst.to_json(), X, K)
            assert report.excess <= X and report.tiles <= K, (report.cost, X, K)


def test_instance_mix_is_varied():
    """The random instances cover blocked cells, ties, several sizes and several k."""
    insts = [make_instance(seed) for seed in range(N_INSTANCES)]
    assert len(insts) >= 200
    assert sum(1 for i in insts if i.blocked) >= 50
    assert sum(1 for i in insts if not i.blocked) >= 50
    with_ties = sum(1 for i in insts
                    if any(r.choose < len(r.tied) for r in requirements(i).values()))
    assert with_ties >= 20
    assert len({(i.width, i.height) for i in insts}) >= 10
    assert len({i.k for i in insts}) >= 3


def test_pair_is_injective():
    seen = {}
    for a in range(40):
        for b in range(40):
            assert sat.pair(a, b) not in seen
            seen[sat.pair(a, b)] = (a, b)


@pytest.mark.parametrize("n,bound", [(n, b) for n in range(5) for b in range(4)])
def test_at_most_gadget(n, bound):
    """The sequential counter is satisfiable exactly for the assignments of its items
    with at most `bound` active items (brute force over all assignments)."""
    items = [[(1000 + i, True)] for i in range(n)]
    clauses = list(sat.at_most(items, bound, tag=7))
    aux = sorted({v for cl in clauses for v, _ in cl if v < 1000 or v >= 1000 + n})
    for bits in itertools.product([False, True], repeat=n):
        base = {1000 + i: bits[i] for i in range(n)}
        ok = any(sat.check_assignment(clauses, {**base, **dict(zip(aux, extra))})
                 for extra in itertools.product([False, True], repeat=len(aux))) \
            if len(aux) <= 12 else None
        if ok is not None:
            assert ok == (sum(bits) <= bound), (bits, bound)


def test_formula_is_polynomial_in_practice():
    inst = random_instance(4, 4, 2, 3, 2, 0.1, seed=3)
    clauses = list(sat.to_sat(inst, 2, 5))
    n = inst.width * inst.height + 1 + 2 + 5
    assert len(clauses) <= 200 * n ** 4
    assert max(len(cl) for cl in clauses) <= 6
    assert sat.formula_size(clauses) <= 200_000_000 * n ** 7


@pytest.mark.parametrize("inst,query,clauses,size,digest", [
    (Instance(width=3, height=1, blocked=frozenset(), k=1,
              ports={"P": (0, 0)}, cities={"C": (2, 0)}),
     (0, 1), 99, 3459, "7b66fadc11c86e08e4c66db9e97b742f50ac82d6d1ce2a78ebb398b177f86eee"),
    (Instance(width=3, height=2, blocked=frozenset({(1, 0)}), k=1,
              ports={"P1": (0, 0), "P2": (2, 1)}, cities={"C1": (2, 0), "C2": (0, 1)}),
     (1, 2), 645, 32735, "98b696280614825b4019830f84ff8141ba920d35aa4073f39a6c8c5c4f26425a"),
])
def test_matches_lean_reduction(inst, query, clauses, size, digest):
    """The Python generator outputs exactly the clause list of the verified Lean
    reduction `toK` (same clauses, same order, same variable numbers). The expected
    values were printed by `lean/Check/CompareWithPython.lean`."""
    formula = list(sat.to_sat(inst, *query))
    assert len(formula) == clauses
    assert sat.formula_size(formula) == size
    assert hashlib.sha256(sat.lean_string(formula).encode()).hexdigest() == digest
