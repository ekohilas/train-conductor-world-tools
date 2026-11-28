"""Tests for the two exact algorithms: `network_solver.exhaustive` (try everything) and
`network_solver.frontier` (the frontier dynamic program).

Both are compared with the CP-SAT oracle on random instances; every solution they return
is also run through the independent verifier. The instance lists are deterministic.
"""
from __future__ import annotations

import functools
import json
import pathlib
import subprocess
import sys

import pytest

from network_solver import cpsat, exhaustive, frontier, verify
from network_solver.distances import requirements
from network_solver.generate import random_instance
from network_solver.instance import Instance

ROOT = pathlib.Path(__file__).resolve().parent.parent

# A frontier with more states than this fails the test instead of eating the machine.
# Every instance below stays far under it (the largest frontier has about 41 000 states).
STATE_GUARD = 300_000

# (width, height, ports, cities, k, blocked_fraction, number of seeds).
# The number of paths per tie choice is ports * k. It is kept small on the larger grids:
# proving infeasibility needs a sweep without the edge budget, and that sweep explodes
# with many paths on many free cells (see test_state_limit_is_reported).
FRONTIER_FAMILIES = [
    (3, 3, 1, 2, 1, 0.0, 10), (3, 3, 1, 3, 2, 0.2, 10), (3, 3, 2, 3, 2, 0.15, 12),
    (3, 3, 2, 3, 3, 0.2, 10), (3, 3, 3, 4, 2, 0.1, 10), (3, 3, 3, 5, 3, 0.0, 10),
    (3, 3, 2, 5, 4, 0.1, 10),
    (3, 4, 2, 4, 3, 0.15, 10), (4, 3, 3, 3, 2, 0.1, 10), (4, 3, 2, 5, 5, 0.0, 6),
    (3, 5, 2, 4, 3, 0.2, 10), (5, 3, 3, 3, 2, 0.1, 10), (3, 6, 3, 4, 3, 0.15, 10),
    (6, 3, 2, 5, 4, 0.25, 10),
    (4, 4, 1, 5, 5, 0.2, 10), (4, 4, 2, 3, 2, 0.1, 10), (4, 4, 3, 5, 3, 0.25, 10),
    (4, 4, 3, 4, 4, 0.1, 10), (4, 4, 2, 5, 5, 0.0, 10), (4, 4, 3, 2, 2, 0.15, 10),
    (4, 5, 3, 5, 2, 0.2, 10), (5, 4, 2, 4, 4, 0.1, 10), (4, 6, 2, 5, 4, 0.15, 10),
    (6, 4, 2, 3, 3, 0.2, 10), (6, 4, 3, 3, 2, 0.2, 10),
    (5, 5, 1, 5, 5, 0.15, 10), (5, 5, 2, 3, 2, 0.15, 10), (5, 5, 3, 5, 3, 0.2, 10),
    (5, 5, 2, 5, 3, 0.25, 10), (5, 5, 3, 3, 2, 0.1, 10), (5, 5, 3, 4, 1, 0.0, 10),
    (5, 6, 3, 4, 2, 0.1, 10), (6, 5, 2, 5, 3, 0.25, 10), (5, 6, 1, 4, 4, 0.2, 10),
    (6, 5, 3, 3, 1, 0.15, 10),
    (6, 6, 1, 5, 4, 0.2, 10), (6, 6, 2, 4, 2, 0.25, 10), (6, 6, 3, 5, 2, 0.15, 10),
    (6, 6, 3, 5, 3, 0.1, 10), (6, 6, 2, 5, 1, 0.0, 10), (6, 6, 3, 2, 2, 0.2, 10),
    # Larger grids with few paths (at most 6): wider frontiers, more labels.
    (7, 7, 2, 4, 2, 0.15, 8), (7, 7, 3, 5, 2, 0.2, 8), (7, 5, 2, 5, 3, 0.2, 8),
    (5, 8, 3, 4, 2, 0.1, 8), (8, 6, 1, 5, 4, 0.2, 8), (8, 8, 2, 4, 2, 0.15, 8),
    (8, 8, 2, 5, 3, 0.25, 8), (9, 9, 2, 5, 2, 0.2, 8), (10, 7, 3, 5, 2, 0.15, 8),
    (10, 10, 3, 6, 2, 0.2, 8), (12, 9, 3, 5, 1, 0.25, 8), (6, 12, 2, 5, 3, 0.2, 8),
]

# Tiny grids only: at most 16 grid edges, so at most 2^16 networks per tie choice.
# The crowded 3x3 families at the end often need a detour (positive excess).
EXHAUSTIVE_FAMILIES = [
    (3, 3, 2, 3, 2, 0.15, 10), (3, 3, 1, 3, 2, 0.25, 6), (3, 3, 3, 3, 2, 0.0, 6),
    (3, 3, 2, 2, 2, 0.2, 6), (2, 4, 1, 3, 2, 0.0, 6), (4, 2, 2, 2, 1, 0.1, 6),
    (3, 2, 1, 2, 2, 0.0, 4), (2, 3, 2, 2, 1, 0.0, 4), (2, 5, 2, 3, 2, 0.1, 4),
    (5, 2, 1, 4, 3, 0.1, 4), (3, 4, 2, 2, 2, 0.3, 4), (4, 3, 1, 4, 3, 0.3, 4),
    (3, 3, 2, 3, 3, 0.0, 10), (3, 3, 3, 2, 2, 0.0, 10),
]
MAX_EXHAUSTIVE_EDGES = 16


def cases(families):
    return [(*family[:6], seed) for family in families for seed in range(family[6])]


def case_id(case) -> str:
    w, h, ports, cities, k, fraction, seed = case
    return f"{w}x{h}-p{ports}-c{cities}-k{k}-b{round(fraction * 100)}-s{seed}"


def make(case) -> Instance:
    w, h, ports, cities, k, fraction, seed = case
    return random_instance(w, h, ports, cities, k, blocked_fraction=fraction, seed=seed)


FRONTIER_CASES = cases(FRONTIER_FAMILIES)
EXHAUSTIVE_CASES = cases(EXHAUSTIVE_FAMILIES)


@functools.lru_cache(maxsize=None)
def oracle(case) -> tuple[int, int] | None:
    """The optimal (excess, tiles) proved by CP-SAT, or None if it proves infeasibility."""
    return oracle_cost(make(case))


def oracle_cost(inst: Instance) -> tuple[int, int] | None:
    solution, stats = cpsat.solve(inst, time_limit=120)
    if solution is None:
        assert stats["status"] == "INFEASIBLE", stats
        return None
    assert stats["optimal"], stats
    report = verify.check(inst, solution)
    assert report.ok, report.errors
    return report.cost


def has_tie(inst: Instance) -> bool:
    """Some port has more cities at the k-th distance than it may choose."""
    return any(len(r.tied) > r.choose for r in requirements(inst).values())


def check_against(inst: Instance, expected: tuple[int, int] | None, solution, stats) -> None:
    """`solution, stats` come from one of the exact solvers; `expected` from the oracle."""
    context = json.dumps(inst.to_json())
    if expected is None:
        assert solution is None and stats["status"] == "INFEASIBLE", (stats, context)
        return
    assert solution is not None, (stats, expected, context)
    assert stats["optimal"] is True, stats
    report = verify.check(inst, solution)
    assert report.ok, (report.errors, context)
    assert report.cost == (stats["excess"], stats["tiles"]), (report.cost, stats, context)
    assert report.cost == expected, (report.cost, expected, context)


# --- frontier DP against CP-SAT on random instances ---------------------------------


@pytest.mark.parametrize("case", FRONTIER_CASES, ids=case_id)
def test_frontier_matches_cpsat(case):
    inst = make(case)
    solution, stats = frontier.solve(inst, max_states=STATE_GUARD)
    check_against(inst, oracle(case), solution, stats)


def test_frontier_cases_are_varied():
    instances = [make(case) for case in FRONTIER_CASES]
    assert len(instances) >= 200  # 504
    # A tie at the k-th place: 149 instances. At least one blocked cell: 350 instances.
    assert sum(has_tie(inst) for inst in instances) >= 30
    assert sum(bool(inst.blocked) for inst in instances) >= 100
    # The same two counts hold on the grids up to 6x6 alone (114 and 257 of 408).
    small = [inst for inst in instances if max(inst.width, inst.height) <= 6]
    assert len(small) >= 200
    assert sum(has_tie(inst) for inst in small) >= 30
    assert sum(bool(inst.blocked) for inst in small) >= 100
    shapes = {(inst.width, inst.height) for inst in instances}
    assert {(3, 3), (6, 6)} <= shapes
    assert any(w < h for w, h in shapes) and any(w > h for w, h in shapes)
    assert {len(inst.ports) for inst in instances} == {1, 2, 3}
    assert {len(inst.cities) for inst in instances} == {2, 3, 4, 5, 6}
    assert {inst.k for inst in instances} == {1, 2, 3, 4, 5}
    # The interesting outcomes all occur: infeasible (34 instances), forced detours
    # (63 with positive excess, 20 with excess >= 4, the largest is 14).
    costs = [oracle(case) for case in FRONTIER_CASES]
    assert sum(cost is None for cost in costs) >= 20
    assert sum(cost is not None and cost[0] > 0 for cost in costs) >= 20
    assert sum(cost is not None and cost[0] >= 4 for cost in costs) >= 5


# --- exhaustive search against CP-SAT and the frontier DP ---------------------------


@pytest.mark.parametrize("case", EXHAUSTIVE_CASES, ids=case_id)
def test_exhaustive_matches_cpsat_and_frontier(case):
    inst = make(case)
    assert len(exhaustive.grid_edges(inst)) <= MAX_EXHAUSTIVE_EDGES
    expected = oracle(case)
    solution, stats = exhaustive.solve(inst)
    check_against(inst, expected, solution, stats)
    assert stats["candidates"] > 0 and stats["seconds"] >= 0
    check_against(inst, expected, *frontier.solve(inst, max_states=STATE_GUARD))


def test_exhaustive_cases_are_varied():
    instances = [make(case) for case in EXHAUSTIVE_CASES]
    assert len(instances) >= 40
    assert sum(has_tie(inst) for inst in instances) >= 5
    assert sum(bool(inst.blocked) for inst in instances) >= 10
    costs = [oracle(case) for case in EXHAUSTIVE_CASES]
    assert sum(cost is None for cost in costs) >= 3
    assert sum(cost is not None and cost[0] > 0 for cost in costs) >= 5


def test_exhaustive_refuses_large_grids():
    inst = Instance(width=4, height=4, blocked=frozenset(), k=1,
                    ports={"P": (0, 0)}, cities={"C": (3, 3)})
    assert len(exhaustive.grid_edges(inst)) == 24
    with pytest.raises(ValueError, match="max_edges"):
        exhaustive.solve(inst)
    small = Instance(width=2, height=2, blocked=frozenset(), k=1,
                     ports={"P": (0, 0)}, cities={"C": (1, 1)})
    with pytest.raises(ValueError, match="max_edges"):
        exhaustive.solve(small, max_edges=3)
    solution, stats = exhaustive.solve(small, max_edges=4)
    assert stats["candidates"] == 16 and (stats["excess"], stats["tiles"]) == (0, 1)


# --- hand-written instances -----------------------------------------------------------


def test_crossing_forces_excess():
    # The plus-shaped crossing of tests/test_network_solver.py: the two straight
    # shortest paths cross at (2, 2), and without a crossing tile one pair detours by 2.
    inst = Instance(width=5, height=5, blocked=frozenset(), k=2,
                    ports={"P1": (0, 2), "P2": (2, 0)}, cities={"C1": (4, 2), "C2": (2, 4)})
    solution, stats = frontier.solve(inst)
    assert stats["optimal"] and stats["excess"] == 2
    report = verify.check(inst, solution)
    assert report.ok and report.excess == 2
    assert report.cost == oracle_cost(inst)


def test_port_next_to_city_costs_nothing():
    inst = Instance(width=2, height=2, blocked=frozenset(), k=1,
                    ports={"P": (0, 0)}, cities={"C": (1, 0)})
    for solver in (frontier, exhaustive):
        solution, stats = solver.solve(inst)
        assert (stats["excess"], stats["tiles"]) == (0, 0)
        assert solution.edges == {frozenset({(0, 0), (1, 0)})}
        assert solution.pairs == {"P": ["C"]}
        assert verify.check(inst, solution).cost == (0, 0)


def plus_instance(arm: int) -> Instance:
    """Width-1 corridors forming a plus with arms of `arm` cells and a terminal at each
    arm end; everything else is blocked. With k = 2 both ports need both cities, in
    particular the one on the opposite arm, so the free centre cell needs degree 4."""
    size = 2 * arm + 1
    open_cells = {(x, arm) for x in range(size)} | {(arm, y) for y in range(size)}
    blocked = frozenset((x, y) for x in range(size) for y in range(size)) - open_cells
    return Instance(width=size, height=size, blocked=blocked, k=2,
                    ports={"P1": (0, arm), "P2": (arm, 0)},
                    cities={"C1": (size - 1, arm), "C2": (arm, size - 1)})


@pytest.mark.parametrize("arm", [1, 2, 3])
def test_degree_four_is_infeasible(arm):
    inst = plus_instance(arm)
    assert oracle_cost(inst) is None  # CP-SAT agrees
    for solver in (frontier, exhaustive):
        solution, stats = solver.solve(inst)
        assert solution is None and stats["status"] == "INFEASIBLE"
    # With k = 1 the same grid is feasible: both ports may pick the same city.
    easier = Instance(width=inst.width, height=inst.height, blocked=inst.blocked, k=1,
                      ports=inst.ports, cities=inst.cities)
    expected = oracle_cost(easier)
    assert expected == (0, 3 * arm - 2)
    for solver in (frontier, exhaustive):
        check_against(easier, expected, *solver.solve(easier))


def test_port_reaching_too_few_cities_is_infeasible():
    # P . C1 C2 : C2 is only reachable through C1, so `requirements` raises.
    inst = Instance(width=4, height=1, blocked=frozenset(), k=2,
                    ports={"P": (0, 0)}, cities={"C1": (2, 0), "C2": (3, 0)})
    with pytest.raises(ValueError):
        requirements(inst)
    for solver in (frontier, exhaustive):
        solution, stats = solver.solve(inst)
        assert solution is None and stats["status"] == "INFEASIBLE"


def test_tie_choice_is_part_of_the_optimum():
    #  A  .  P1 .  B        P2 can only reach B (through (3, 1) and (3, 0)).
    #  #  #  #  .  #        P1 has A and B tied at distance 2 and must pick one:
    #  #  #  #  P2 #        B shares the tile (3, 0), A needs the extra tile (1, 0).
    blocked = frozenset({(0, 1), (1, 1), (2, 1), (4, 1), (0, 2), (1, 2), (2, 2), (4, 2)})
    inst = Instance(width=5, height=3, blocked=blocked, k=1,
                    ports={"P1": (2, 0), "P2": (3, 2)}, cities={"A": (0, 0), "B": (4, 0)})
    assert has_tie(inst)
    for solver in (frontier, exhaustive):
        solution, stats = solver.solve(inst)
        assert solution.pairs == {"P1": ["B"], "P2": ["B"]}
        check_against(inst, (0, 2), solution, stats)
    assert oracle_cost(inst) == (0, 2)


def test_wide_instance_is_swept_along_its_long_side():
    # Wider than high, so the DP transposes it. The only way from P to C is around the
    # wall: 6 edges (that is d(P, C), so no excess) over 5 tiles.
    #  P  .  #  .  C
    #  .  .  .  .  .
    inst = Instance(width=5, height=2, blocked=frozenset({(2, 0)}), k=1,
                    ports={"P": (0, 0)}, cities={"C": (4, 0)})
    solution, stats = frontier.solve(inst)
    assert all(inst.in_bounds(cell) for edge in solution.edges for cell in edge)
    check_against(inst, (0, 5), solution, stats)
    assert oracle_cost(inst) == (0, 5)
    check_against(inst, (0, 5), *exhaustive.solve(inst))


# An infeasible instance (the free cell (4, 1) would need degree 4) with 9 paths.
# `random_instance(6, 4, 3, 3, 3, blocked_fraction=0.2, seed=6)`, written out.
HARD_INFEASIBLE = {
    "width": 6, "height": 4, "k": 3,
    "blocked": [[1, 2], [3, 0], [5, 3]],
    "ports": {"P0": [5, 0], "P1": [3, 1], "P2": [2, 1]},
    "cities": {"C0": [5, 2], "C1": [3, 2], "C2": [4, 0]},
}


def test_state_limit_is_reported():
    # Proving this instance infeasible needs the sweep without the edge budget, and
    # with 9 paths that sweep has millions of states. The DP must say so, not hang.
    inst = Instance.from_json(HARD_INFEASIBLE)
    assert inst == random_instance(6, 4, 3, 3, 3, blocked_fraction=0.2, seed=6)
    assert oracle_cost(inst) is None
    with pytest.raises(frontier.StateLimit) as stop:
        frontier.solve(inst, max_states=20_000)
    info = stop.value.info
    assert info["states"] > 20_000 == info["max_states"]
    assert info["slack"] >= inst.width * inst.height and info["budget"] is False
    assert 0 <= info["cell"] < info["cells"] == 24 and info["paths"] == 9


def test_progress_callback_sees_every_round():
    inst = Instance(width=5, height=5, blocked=frozenset(), k=2,
                    ports={"P1": (0, 2), "P2": (2, 0)}, cities={"C1": (4, 2), "C2": (2, 4)})
    seen = []
    solution, stats = frontier.solve(inst, progress=seen.append)
    assert {info["slack"] for info in seen} == {0, 2} and stats["slack"] == 2
    assert max(info["states"] for info in seen) == stats["states_peak"]
    assert all(info["cells"] == 25 and info["paths"] == 4 for info in seen)


# --- command lines --------------------------------------------------------------------


@pytest.fixture
def instance_file(tmp_path):
    inst = Instance(width=3, height=3, blocked=frozenset(), k=1,
                    ports={"P": (0, 0)}, cities={"C": (2, 2)})
    path = tmp_path / "instance.json"
    inst.save(path)
    return path


@pytest.mark.parametrize("module", [frontier, exhaustive])
def test_main_prints_stats_and_verifies(module, instance_file, tmp_path, capsys):
    out = tmp_path / "solution.json"
    assert module.main([str(instance_file), "--out", str(out)]) == 0
    stats_line, verify_line = capsys.readouterr().out.strip().splitlines()
    stats = json.loads(stats_line)
    assert stats["optimal"] is True and (stats["excess"], stats["tiles"]) == (0, 3)
    assert verify_line == "verify: OK excess=0 tiles=3"
    assert json.loads(out.read_text())["tiles"] == 3


def test_frontier_main_reports_the_state_limit(tmp_path, capsys):
    path = tmp_path / "hard.json"
    path.write_text(json.dumps(HARD_INFEASIBLE))
    assert frontier.main([str(path), "--max-states", "2000", "--quiet"]) == 2
    captured = capsys.readouterr()
    report = json.loads(captured.out)
    assert report["status"] == "STATE_LIMIT" and report["optimal"] is False
    assert report["states"] > 2000 and captured.err == ""


@pytest.mark.parametrize("module", ["network_solver.frontier", "network_solver.exhaustive"])
def test_modules_are_runnable(module, instance_file):
    done = subprocess.run([sys.executable, "-m", module, str(instance_file)],
                          capture_output=True, text=True, timeout=120, cwd=ROOT)
    assert done.returncode == 0, done.stderr
    assert json.loads(done.stdout.splitlines()[0])["tiles"] == 3
    assert done.stdout.splitlines()[1].startswith("verify: OK")
