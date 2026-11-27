"""The hardness reduction Rectilinear Steiner Tree -> Train Network
(`network_solver.steiner.rst_to_train`, docs/result.md section 6).

For a point set A with optimum L* = RST(A) the reduction must give

    (I, X, K) is a yes-instance   iff   L >= L*.

Checked here on random point sets:
  * "yes" side, constructively: the network built from an optimal Steiner tree is
    accepted by the independent verifier and has at most K(L*) tiles;
  * "no" side, by an independent lower bound: every network uses at least
    (minimum Steiner tree of the terminals in the grid graph) + 1 - |A| tiles, and that
    exceeds K(L* - 1). The grid Steiner tree is computed on the full scaled grid without
    Hanan's theorem, so the test also checks RST(s*A) = s * RST(A);
  * both sides against the CP-SAT oracle where it finishes: "yes" on small instances,
    "no" on collinear pairs (a refutation with a slack of one tile is beyond CP-SAT on
    two-dimensional instances).
"""
from __future__ import annotations

import random

import pytest

from network_solver import steiner, verify
from network_solver.decide import decide_cpsat


def point_set(seed: int) -> list[tuple[int, int]]:
    rng = random.Random(104729 * seed + 7)
    m = rng.choice([2, 3, 3, 4, 4, 5])
    box = rng.choice([2, 3, 4, 5]) if m <= 4 else rng.choice([3, 4])
    return steiner.random_points(rng, m, box)


@pytest.mark.parametrize("seed", range(300))
def test_reduction_thresholds(seed):
    pts = point_set(seed)
    m, s = len(pts), steiner.scale_factor(pts)
    opt, tree = steiner.hanan_steiner_tree(pts)

    # yes side: an explicit feasible network with at most K(opt) tiles
    inst, X, K = steiner.rst_to_train(pts, opt)
    report = verify.check(inst, steiner.witness(pts, tree))
    assert report.ok, (pts, report.errors)
    assert report.tiles <= K and report.excess <= X, (pts, report.cost, X, K)

    # no side: tiles >= (grid Steiner tree) + 1 - m > K(opt - 1)
    lower = steiner.grid_steiner_edges(inst.width, inst.height,
                                       [inst.ports["P"]] + list(inst.cities.values()))
    assert lower == s * opt, (pts, lower, s, opt)
    _, _, k_no = steiner.rst_to_train(pts, opt - 1)
    assert lower + 1 - m > k_no, (pts, lower, k_no)


@pytest.mark.parametrize("seed", range(25))
def test_yes_side_against_cpsat(seed):
    rng = random.Random(seed)
    pts = steiner.random_points(rng, rng.choice([2, 3, 3]), rng.choice([2, 3]))
    opt = steiner.rst_length(pts)
    inst, X, K = steiner.rst_to_train(pts, opt)
    assert decide_cpsat(inst, X, K, time_limit=300)


@pytest.mark.parametrize("gap,vertical", [(g, v) for g in (1, 2, 3) for v in (False, True)])
def test_no_side_against_cpsat_collinear(gap, vertical):
    pts = [(0, 0), (0, gap)] if vertical else [(0, 0), (gap, 0)]
    assert steiner.rst_length(pts) == gap
    inst, X, K = steiner.rst_to_train(pts, gap)
    assert decide_cpsat(inst, X, K, time_limit=300)
    inst, X, K = steiner.rst_to_train(pts, gap - 1)
    assert not decide_cpsat(inst, X, K, time_limit=300)


def test_hanan_solver_small_cases():
    assert steiner.rst_length([(0, 0), (3, 4)]) == 7
    assert steiner.rst_length([(0, 0), (2, 0), (1, 1)]) == 3
    assert steiner.rst_length([(0, 1), (2, 1), (1, 0), (1, 2)]) == 4      # a cross
    assert steiner.rst_length([(0, 0), (2, 0), (0, 2), (2, 2)]) == 6


def test_cross_needs_degree_repair():
    """Four points at the tips of a plus: the optimal tree has a degree-4 Steiner point,
    which the network may not have. The witness repairs it with one extra tile."""
    pts = [(0, 1), (2, 1), (1, 0), (1, 2)]
    opt, tree = steiner.hanan_steiner_tree(pts)
    inst, X, K = steiner.rst_to_train(pts, opt)
    report = verify.check(inst, steiner.witness(pts, tree))
    s, m = steiner.scale_factor(pts), len(pts)
    assert report.ok and report.tiles == s * opt + 1 - m + 1
    assert report.tiles <= K


def test_collinear_points_need_bypass():
    """Three collinear points: the tree passes through the middle point, a network may
    not pass through a city, and the witness goes around it with three extra tiles."""
    pts = [(0, 0), (1, 0), (2, 0)]
    opt, tree = steiner.hanan_steiner_tree(pts)
    inst, X, K = steiner.rst_to_train(pts, opt)
    report = verify.check(inst, steiner.witness(pts, tree))
    s, m = steiner.scale_factor(pts), len(pts)
    assert report.ok and report.tiles == s * opt + 1 - m + 3
    assert report.tiles <= K
