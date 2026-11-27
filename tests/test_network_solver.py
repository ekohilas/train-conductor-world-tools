"""Tests for the CP-SAT baseline and verifier.

The brute-force solver below enumerates every edge subset of a tiny grid, so it shares
no modelling with CP-SAT; agreement on random instances is the evidence that the CP-SAT
model encodes docs/problem.md.
"""
from __future__ import annotations

import itertools

import pytest

from network_solver import cpsat, verify
from network_solver.distances import requirements
from network_solver.generate import random_instance
from network_solver.instance import Instance, Solution


def brute_force(inst: Instance) -> tuple[int, int] | None:
    cells = [(x, y) for x in range(inst.width) for y in range(inst.height)
             if (x, y) not in inst.blocked]
    edges = [frozenset((a, b)) for a, b in itertools.combinations(cells, 2)
             if abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1]
    reqs = requirements(inst)
    choices = [
        [list(r.required) + list(extra) for extra in itertools.combinations(r.tied, r.choose)]
        for r in reqs.values()
    ]
    best = None
    for mask in range(1 << len(edges)):
        net = {e for i, e in enumerate(edges) if mask >> i & 1}
        for combo in itertools.product(*choices):
            sol = Solution(edges=net, pairs=dict(zip(reqs, combo)))
            report = verify.check(inst, sol)
            if report.ok and (best is None or report.cost < best):
                best = report.cost
    return best


def test_requirements_tie_group():
    inst = Instance(width=5, height=3, blocked=frozenset(), k=2,
                    ports={"P": (2, 0)}, cities={"A": (0, 0), "B": (2, 2), "C": (3, 0)})
    r = requirements(inst)["P"]
    assert r.required == ("C",)
    assert set(r.tied) == {"A", "B"} and r.choose == 1


def test_terminals_are_not_transit():
    # P . C1 C2 : C2 is reachable from P only through C1, which is forbidden.
    inst = Instance(width=4, height=1, blocked=frozenset(), k=2,
                    ports={"P": (0, 0)}, cities={"C1": (2, 0), "C2": (3, 0)})
    with pytest.raises(ValueError):
        requirements(inst)


def test_verifier_rejects_degree_four():
    inst = Instance(width=3, height=3, blocked=frozenset(), k=1,
                    ports={"P": (1, 0)}, cities={"C": (1, 2)})
    centre = (1, 1)
    sol = Solution(edges={frozenset((centre, n)) for n in [(0, 1), (2, 1), (1, 0), (1, 2)]},
                   pairs={"P": ["C"]})
    assert any("degree 4" in e for e in verify.check(inst, sol).errors)


def test_crossing_forces_excess():
    # Plus shape, k=2 so every port needs both cities. P1->C1 runs along row 2 and
    # P2->C2 along column 2. Each has exactly
    # one shortest path, and they cross at (2, 2). With no crossing tile, the optimum
    # detours one pair by 2.
    inst = Instance(width=5, height=5, blocked=frozenset(), k=2,
                    ports={"P1": (0, 2), "P2": (2, 0)}, cities={"C1": (4, 2), "C2": (2, 4)})
    sol, stats = cpsat.solve(inst, time_limit=30)
    assert stats["optimal"], stats
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    assert report.excess == 2


@pytest.mark.parametrize("seed", range(12))
def test_cpsat_matches_brute_force(seed):
    inst = random_instance(width=3, height=3, ports=2, cities=3, k=2,
                           blocked_fraction=0.15, seed=seed)
    expected = brute_force(inst)
    sol, stats = cpsat.solve(inst, time_limit=30)
    if expected is None:
        assert sol is None
        return
    assert stats["optimal"], stats
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    assert report.cost == expected, (report.cost, expected, inst.to_json())
