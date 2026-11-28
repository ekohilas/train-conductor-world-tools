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


def test_rejects_blocked_cell_outside_grid():
    with pytest.raises(ValueError, match="Blocked cell"):
        Instance(width=3, height=1, blocked=frozenset({(5000, 7)}), k=1,
                 ports={"P": (0, 0)}, cities={"C": (2, 0)})


def test_rejects_k_above_city_count():
    with pytest.raises(ValueError, match="k="):
        Instance(width=3, height=1, blocked=frozenset(), k=2,
                 ports={"P": (0, 0)}, cities={"C": (2, 0)})


def test_port_next_to_city_uses_direct_edge():
    # The port is adjacent to its only city, so the optimum is the direct terminal edge
    # with no track tile at all.
    inst = Instance(width=2, height=2, blocked=frozenset(), k=1,
                    ports={"P": (0, 0)}, cities={"C": (1, 0)})
    sol, stats = cpsat.solve(inst, time_limit=30)
    report = verify.check(inst, sol)
    assert report.ok and (report.excess, report.tiles) == (0, 0)


def test_tmx_export_round_trip(tmp_path):
    # The stored optimal Europe solution, written as Tiled tiles and read back, must give
    # the same network and the same verified cost.
    import json
    import pathlib

    from network_solver import tmx_tracks

    root = pathlib.Path(__file__).resolve().parent.parent
    inst = Instance.load(root / "data/instances/europe.json")
    sol = Solution.from_json(json.loads((root / "data/instances/europe.solution.json").read_text()))
    out = tmp_path / "optimal.tmx"
    tmx_tracks.write_tracks(tmx_tracks.TMX, out, tmx_tracks.solution_to_grid(inst, sol))
    edges, problems = tmx_tracks.grid_to_edges(inst, tmx_tracks.read_tracks(out))
    assert problems == []
    terminal_edges = {e for e in sol.edges if all(c in inst.terminals for c in e)}
    assert edges == sol.edges - terminal_edges
    _, report = tmx_tracks.best_report(inst, edges)
    assert report.ok and (report.excess, report.tiles) == (2, 210)
