"""Cross-checks of `network_solver.exact` (our combinatorial exact solver) against the
CP-SAT oracle `network_solver.cpsat`, on 296 random instances of varied sizes plus
hand-built families. Both solutions are scored by the independent verifier.

`exact` is exact but exponential in the worst case; see docs/result.md. These tests are
evidence that it implements docs/problem.md, not evidence of polynomial running time.
"""
from __future__ import annotations

import pytest

from network_solver import cpsat, exact, verify
from network_solver.distances import requirements
from network_solver.families import (plus_instance, ring_instance, snake_instance,
                                      trident_instance)
from network_solver.generate import random_instance

# (width, height, ports, cities, k)
OPEN_CONFIGS = [
    (3, 3, 1, 2, 1), (3, 3, 2, 3, 2), (3, 4, 2, 3, 2), (4, 4, 1, 4, 3),
    (4, 4, 2, 3, 2), (4, 5, 2, 4, 2), (5, 5, 2, 3, 2), (5, 5, 2, 4, 2),
    (5, 5, 3, 4, 2), (6, 5, 2, 4, 3), (6, 6, 2, 4, 2), (6, 6, 3, 5, 2),
    (7, 7, 3, 5, 3), (8, 8, 3, 6, 3), (9, 5, 3, 7, 4), (10, 10, 3, 6, 3),
]
OPEN_FRACTIONS = [0.0, 0.1, 0.2, 0.3]
MAZE_CONFIGS = [
    (5, 5, 1, 4, 3), (6, 6, 1, 5, 4), (6, 6, 2, 4, 3),
    (7, 7, 2, 5, 3), (8, 8, 2, 6, 4), (8, 6, 3, 5, 3),
]
MAZE_FRACTIONS = [0.35, 0.45, 0.5]


def _cases():
    out = []
    for ci, cfg in enumerate(OPEN_CONFIGS):
        for seed in range(14):
            out.append((cfg, OPEN_FRACTIONS[seed % 4], 100 * ci + seed))
    for ci, cfg in enumerate(MAZE_CONFIGS):
        for seed in range(12):
            out.append((cfg, MAZE_FRACTIONS[seed % 3], 5000 + 100 * ci + seed))
    return out


CASES = _cases()


def _instance(case):
    (w, h, p, c, k), fraction, seed = case
    return random_instance(w, h, p, c, k, blocked_fraction=fraction, seed=seed)


def _cost(inst, sol):
    if sol is None:
        return None
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    return report.cost


def _agree(inst):
    sol, stats = exact.solve(inst, time_limit=300)
    assert stats["optimal"], stats
    oracle, oracle_stats = cpsat.solve(inst, time_limit=300, workers=4)
    if oracle is None:
        assert oracle_stats["status"] == "INFEASIBLE", oracle_stats
    else:
        assert oracle_stats["optimal"], oracle_stats
    got, want = _cost(inst, sol), _cost(inst, oracle)
    assert got == want, (got, want, inst.to_json())
    if sol is not None:
        assert (stats["excess"], stats["tiles"]) == got
        # Lemma B of docs/result.md: the network returned is the union of a canonical
        # path system, so it has at most m(m-1) T-junctions, m = number of pairs.
        m = len(inst.ports) * inst.k
        degree = {}
        for edge in sol.edges:
            for cell in edge:
                degree[cell] = degree.get(cell, 0) + 1
        junctions = sum(1 for cell, dg in degree.items() if dg == 3 and inst.is_free(cell))
        assert junctions <= m * (m - 1)
    return got


def test_suite_is_large_and_varied():
    assert len(CASES) >= 200
    insts = [_instance(case) for case in CASES]
    assert len({(i.width, i.height) for i in insts}) >= 10
    assert sum(1 for i in insts if i.blocked) >= 100
    tied = sum(1 for i in insts
               if any(r.choose < len(r.tied) for r in requirements(i).values()))
    assert tied >= 60


@pytest.mark.parametrize("case", CASES, ids=lambda c: f"{c[0]}-{c[1]}-{c[2]}")
def test_exact_matches_cpsat(case):
    _agree(_instance(case))


def test_random_suite_contains_hard_outcomes():
    # The suite is not all "excess 0": some instances need detours, some are infeasible.
    costs = [exact.solve(_instance(case), time_limit=300)[0] for case in CASES[224:]]
    assert sum(1 for s in costs if s is None) >= 1
    assert any(s is not None and verify.check(_instance(case), s).excess > 0
               for case, s in zip(CASES[224:], costs))


def test_plus_is_infeasible():
    assert _agree(plus_instance()) is None


@pytest.mark.parametrize("n", [3, 4, 6, 8])
def test_ring_needs_long_detour(n):
    # 4 terminals, and the optimal excess grows linearly with the side of the grid.
    excess, _ = _agree(ring_instance(n))
    assert excess == 6 * n + 6


@pytest.mark.parametrize("n", [3, 4, 6, 8])
def test_trident_single_port_needs_long_detour(n):
    # One port and three cities: the centre cannot branch three ways.
    excess, _ = _agree(trident_instance(n))
    assert excess == 4 * n + 2


@pytest.mark.parametrize("n", [1, 2, 3])
def test_snake_uses_most_of_the_grid(n):
    inst = snake_instance(n)
    excess, tiles = _agree(inst)
    assert excess == 0
    assert tiles == (2 * n + 1) * (n + 1) + n - 2
