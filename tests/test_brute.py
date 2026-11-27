"""`network_solver.brute` is the Python mirror of the Lean-verified exhaustive solver
(`lean/TrainNetwork/Brute/Solve.lean`). It follows the Lean definitions directly
(`IsNearestChoice`, not `requirements`), so agreement with `exact` and with CP-SAT on
tiny instances also checks that the Python and Lean readings of docs/problem.md agree.
"""
from __future__ import annotations

import pytest

from network_solver import brute, cpsat, exact, verify
from network_solver.families import plus_instance
from network_solver.generate import random_instance

CONFIGS = [(3, 3, 1, 2, 1), (3, 3, 2, 3, 2), (3, 3, 2, 4, 2), (2, 4, 1, 3, 2),
           (4, 3, 2, 3, 2), (3, 4, 2, 4, 3), (4, 4, 2, 3, 2)]
MAX_EDGES = 13


def _instances():
    out = []
    for ci, (w, h, p, c, k) in enumerate(CONFIGS):
        for seed in range(8):
            fractions = [0.1, 0.2, 0.3, 0.4] if w * h > 9 else [0.0, 0.1, 0.2, 0.3]
            inst = random_instance(w, h, p, c, k, blocked_fraction=fractions[seed % 4],
                                   seed=9000 + 100 * ci + seed)
            if len(brute.all_edges(inst)) <= MAX_EDGES:
                out.append(inst)
    return out


INSTANCES = _instances()


def _cost(inst, sol):
    if sol is None:
        return None
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    return report.cost


def test_enough_tiny_instances():
    assert len(INSTANCES) >= 40


@pytest.mark.parametrize("index", range(len(INSTANCES)))
def test_brute_matches_exact_and_cpsat(index):
    inst = INSTANCES[index]
    want = _cost(inst, brute.solve(inst)[0])
    sol, stats = exact.solve(inst)
    assert stats["optimal"]
    assert _cost(inst, sol) == want, inst.to_json()
    assert _cost(inst, cpsat.solve(inst, time_limit=60)[0]) == want, inst.to_json()


def test_brute_plus_is_infeasible():
    assert brute.solve(plus_instance())[0] is None
