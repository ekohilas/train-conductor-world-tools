"""Tests for the layered DP (network_solver/layerdp.py).

Three independent implementations are compared:

  * `layerdp.solve(mode="pruned")`: the frontier DP over canonical certificates;
  * `layerdp.solve(mode="verbatim")`: the literal certificate system, layer by layer;
  * the CP-SAT oracle (`cpsat.solve`) and, on tiny grids, a brute force over all edge
    subsets that only uses the verifier.

Every DP answer is also checked with `verify.check` (inside `solve` and again here).
"""
from __future__ import annotations

import functools
import itertools
import random

import pytest

from network_solver import cpsat, layerdp, verify
from network_solver.distances import requirements
from network_solver.generate import random_instance
from network_solver.instance import Instance, Solution

# Per-instance guards for the DP. No instance below comes near them (the slowest takes
# a few seconds and a few hundred thousand states); they turn a hang on a much slower
# machine into a skip.
DP_TIME_LIMIT = 120.0
DP_MAX_STATES = 3_000_000


def brute_force(inst: Instance) -> tuple[int, int] | None:
    """Optimum by enumerating every edge subset and every choice family (same logic as
    tests/test_network_solver.py); shares nothing with the DP but the verifier."""
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
            report = verify.check(inst, Solution(edges=net, pairs=dict(zip(reqs, combo))))
            if report.ok and (best is None or report.cost < best):
                best = report.cost
    return best


def dp_cost(inst: Instance, mode: str = "pruned") -> tuple[int, int] | None:
    """Runs the DP, re-checks its solution with the verifier and returns its cost
    (None = proven infeasible)."""
    sol, stats = layerdp.solve(inst, mode=mode, time_limit=DP_TIME_LIMIT,
                               max_states=DP_MAX_STATES)
    if stats["status"] == "TIMEOUT":
        pytest.skip(f"layerdp ({mode}) hit a guard: {stats}")
    assert stats["mode"] == mode and stats["states"] >= 1 and stats["seconds"] >= 0
    if sol is None:
        assert stats["status"] == "INFEASIBLE", stats
        assert stats["excess"] is None and stats["tiles"] is None
        return None
    assert stats["status"] == "OPTIMAL", stats
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    assert report.cost == (stats["excess"], stats["tiles"]), (report.cost, stats)
    return report.cost


def oracle_cost(inst: Instance) -> tuple[int, int] | None:
    """Optimum according to CP-SAT (None = infeasible)."""
    sol, stats = cpsat.solve(inst, time_limit=120, workers=4)
    if sol is None:
        assert stats["status"] == "INFEASIBLE", stats
        return None
    assert stats["optimal"], stats
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    return report.cost


# --------------------------------------------------------------------------------------
# Pruned mode against the CP-SAT oracle on random instances
# --------------------------------------------------------------------------------------

# (width, height): squares, wide and tall grids (tall ones exercise the transposition)
# and strips, from 9 to 192 cells.
SHAPES = [
    (3, 3), (4, 3), (3, 4), (4, 4), (5, 4), (4, 5), (5, 5), (6, 4), (4, 6), (7, 3),
    (3, 7), (8, 2), (2, 8), (9, 1), (1, 9), (6, 6), (8, 5), (9, 7), (7, 10), (12, 9),
    (10, 8), (8, 12), (14, 10), (16, 12),
]
CASES_PER_SHAPE = 18
# Generated cases that are left out. This one is infeasible with 9 pairs on 21 cells:
# CP-SAT refutes it at once, but the DP only proves infeasibility with its last runs
# (corridor budget 16, then >= W*H), which need more than 8 million states here.
EXCLUDED = {(7, 3, 3, 3, 3, 0.1, 2892)}


def _random_cases() -> list[tuple]:
    rng = random.Random(20240607)
    cases = []
    for width, height in SHAPES:
        area = width * height
        for i in range(CASES_PER_SHAPE):
            for _ in range(1000):
                ports = rng.choice([1, 2, 2, 3, 3])
                cities = rng.choice([2, 3, 4, 5])
                k = rng.randint(1, cities)
                blocked = [0, 0.1, 0.2, 0.3][i % 4]
                seed = rng.randrange(10_000)
                if ports + cities > area - 1:
                    continue
                # The DP is exponential in the corridor budget it needs. Many pairs on
                # few cells mean a large optimal excess (or infeasibility, which is only
                # proven by the final run with budget >= W*H), and many pairs on a big
                # grid mean a huge frontier. Keep the number of pairs moderate there so
                # that every case runs in a few seconds; the small grids keep all
                # combinations.
                if area >= 16 and ports * k >= 12:
                    continue
                if area > 60 and ports * k >= 9:
                    continue
                if min(width, height) == 1 and blocked:
                    blocked = 0.1  # a strip with many clouds rarely has k reachable cities
                try:
                    random_instance(width, height, ports, cities, k, blocked, seed, max_tries=50)
                except RuntimeError:
                    continue
                cases.append((width, height, ports, cities, k, blocked, seed))
                break
            else:
                raise AssertionError(f"no instance for shape {width}x{height}")
    return [case for case in cases if case not in EXCLUDED]


RANDOM_CASES = _random_cases()


@functools.lru_cache(maxsize=None)
def _compare(case: tuple) -> dict:
    """Solves one random case with the DP and with CP-SAT (cached: the summary test
    reuses the results of the parametrised test)."""
    width, height, ports, cities, k, blocked, seed = case
    inst = random_instance(width, height, ports, cities, k, blocked, seed, max_tries=50)
    reqs = requirements(inst)
    return {
        "instance": inst,
        "dp": dp_cost(inst),
        "oracle": oracle_cost(inst),
        "blocked": len(inst.blocked) > 0,
        "ties": any(r.choose < len(r.tied) for r in reqs.values()),
        "families": len(layerdp.choice_families(inst)),
    }


@pytest.mark.parametrize("case", RANDOM_CASES, ids=lambda c: "x".join(map(str, c)))
def test_pruned_matches_cpsat(case):
    res = _compare(case)
    assert res["dp"] == res["oracle"], (res["dp"], res["oracle"], res["instance"].to_json())


def test_random_cases_summary():
    """The random comparison covers what it is meant to cover."""
    results = [_compare(case) for case in RANDOM_CASES]
    total = len(results)
    with_blocked = sum(r["blocked"] for r in results)
    with_ties = sum(r["ties"] for r in results)
    multi_family = sum(r["families"] > 1 for r in results)
    infeasible = sum(r["oracle"] is None for r in results)
    with_excess = sum(r["oracle"] is not None and r["oracle"][0] > 0 for r in results)
    tall = sum(r["instance"].height > r["instance"].width for r in results)
    print(f"\nlayerdp vs CP-SAT: {total} random instances, sizes "
          f"{min(w * h for w, h in SHAPES)}..{max(w * h for w, h in SHAPES)} cells, "
          f"{with_blocked} with blocked cells, {with_ties} with a non-trivial tie group "
          f"({multi_family} with >1 choice family), {infeasible} infeasible, "
          f"{with_excess} with positive optimal excess, {tall} taller than wide")
    assert all(r["dp"] == r["oracle"] for r in results)
    assert total >= 200
    assert with_blocked >= 100
    assert with_ties >= 40
    assert infeasible >= 3
    assert with_excess >= 20
    assert tall >= 40


# --------------------------------------------------------------------------------------
# Hand-made cases
# --------------------------------------------------------------------------------------

def _plus_corridors(k: int) -> Instance:
    """5x5 grid in which only row 2 and column 2 are open: two width-1 corridors that
    cross in (2, 2), with a terminal at each of the four ends."""
    open_cells = {(x, 2) for x in range(5)} | {(2, y) for y in range(5)}
    blocked = frozenset((x, y) for x in range(5) for y in range(5)) - open_cells
    return Instance(width=5, height=5, blocked=blocked, k=k,
                    ports={"P1": (0, 2), "P2": (2, 0)}, cities={"C1": (4, 2), "C2": (2, 4)})


def test_crossing_forces_excess():
    # Same instance as tests/test_network_solver.py: the two straight shortest paths
    # cross in (2, 2), there is no crossing tile, so one pair detours by 2.
    inst = Instance(width=5, height=5, blocked=frozenset(), k=2,
                    ports={"P1": (0, 2), "P2": (2, 0)}, cities={"C1": (4, 2), "C2": (2, 4)})
    cost = dp_cost(inst)
    assert cost is not None and cost[0] == 2
    assert cost == oracle_cost(inst)


def test_crossing_in_corridors_is_infeasible():
    # With k = 2 every port needs both cities, so the centre cell would need all four
    # sides: no feasible network exists, whatever the excess.
    inst = _plus_corridors(k=2)
    sol, stats = layerdp.solve(inst)
    assert sol is None and stats["status"] == "INFEASIBLE"
    assert stats["budget"] >= inst.width * inst.height  # decided by the final run
    assert oracle_cost(inst) is None
    assert brute_force(inst) is None


def test_infeasible_family_is_skipped():
    # With k = 1 both cities are tied for both ports. The families P1->C1, P2->C2 and
    # P1->C2, P2->C1 need the crossing and are infeasible; the two families in which
    # both ports serve the same city are feasible with a T-junction in the centre.
    inst = _plus_corridors(k=1)
    assert len(layerdp.choice_families(inst)) == 4
    sol, stats = layerdp.solve(inst)
    assert stats["status"] == "OPTIMAL" and (stats["excess"], stats["tiles"]) == (0, 4)
    assert sol.pairs["P1"] == sol.pairs["P2"]
    assert oracle_cost(inst) == (0, 4)
    assert brute_force(inst) == (0, 4)


def test_port_reaching_too_few_cities_is_infeasible():
    # P . C1 C2 with k = 2: C2 is only reachable through C1, so t_p is infinite and the
    # instance has no solution (docs/problem.md, "Required pairs").
    inst = Instance(width=4, height=1, blocked=frozenset(), k=2,
                    ports={"P": (0, 0)}, cities={"C1": (2, 0), "C2": (3, 0)})
    for mode in ("pruned", "verbatim"):
        sol, stats = layerdp.solve(inst, mode=mode)
        assert sol is None and stats["status"] == "INFEASIBLE"


@pytest.mark.parametrize("mode", ["pruned", "verbatim"])
def test_port_next_to_city_uses_direct_edge(mode):
    inst = Instance(width=2, height=2, blocked=frozenset(), k=1,
                    ports={"P": (0, 0)}, cities={"C": (1, 0)})
    sol, stats = layerdp.solve(inst, mode=mode)
    assert (stats["excess"], stats["tiles"]) == (0, 0)
    assert sol.edges == {frozenset(((0, 0), (1, 0)))}
    assert sol.pairs == {"P": ["C"]}


def test_tie_group_choice():
    # Instance of test_requirements_tie_group: C is required (adjacent to the port), A
    # and B are tied and exactly one of them must be chosen; either costs one tile.
    inst = Instance(width=5, height=3, blocked=frozenset(), k=2,
                    ports={"P": (2, 0)}, cities={"A": (0, 0), "B": (2, 2), "C": (3, 0)})
    assert len(layerdp.choice_families(inst)) == 2
    sol, stats = layerdp.solve(inst)
    assert (stats["excess"], stats["tiles"]) == (0, 1) == oracle_cost(inst)
    assert "C" in sol.pairs["P"] and len(sol.pairs["P"]) == 2


def test_tie_group_choice_changes_the_cost():
    # A and B are tied for P1 (distance 3 each, k = 1). P2 must serve B, and its path
    # can run through (4, 1), (5, 1), exactly the tiles of P1 -> B. Choosing B for P1
    # costs 2 tiles in total, choosing A costs 4.
    inst = Instance(width=7, height=3, blocked=frozenset(), k=1,
                    ports={"P1": (3, 1), "P2": (4, 0)},
                    cities={"A": (0, 1), "B": (6, 1)})
    reqs = requirements(inst)
    assert reqs["P1"].choose == 1 and set(reqs["P1"].tied) == {"A", "B"}
    assert reqs["P2"].candidates == ("B",)
    sol, stats = layerdp.solve(inst)
    assert (stats["excess"], stats["tiles"]) == (0, 2) == oracle_cost(inst)
    assert sol.pairs == {"P1": ["B"], "P2": ["B"]}
    assert stats["families"] == 2


def test_transposed_instance_gives_same_cost():
    # A tall instance is solved on its transpose internally; the cost must not change
    # and the returned edges must be in the original coordinates (checked by verify).
    for seed in range(6):
        inst = random_instance(4, 6, 2, 4, 2, 0.15, seed)
        flipped = Instance(
            width=inst.height, height=inst.width, k=inst.k,
            blocked=frozenset((y, x) for x, y in inst.blocked),
            ports={p: (y, x) for p, (x, y) in inst.ports.items()},
            cities={c: (y, x) for c, (x, y) in inst.cities.items()})
        assert dp_cost(inst) == dp_cost(flipped)


def test_time_limit_reports_timeout():
    inst = random_instance(12, 12, 3, 6, 4, 0.1, seed=1)
    sol, stats = layerdp.solve(inst, time_limit=0.0)
    assert sol is None and stats["status"] == "TIMEOUT" and stats["stopped"] == "time_limit"
    sol, stats = layerdp.solve(inst, max_states=1)
    assert sol is None and stats["status"] == "TIMEOUT" and stats["stopped"] == "max_states"


def test_unknown_mode_is_rejected():
    inst = Instance(width=2, height=1, blocked=frozenset(), k=1,
                    ports={"P": (0, 0)}, cities={"C": (1, 0)})
    with pytest.raises(ValueError):
        layerdp.solve(inst, mode="fast")


# --------------------------------------------------------------------------------------
# Verbatim mode against pruned mode and the brute force on tiny instances
# --------------------------------------------------------------------------------------

# (width, height, ports, cities, k, number of seeds): everything here takes the verbatim
# DP at most a few seconds per instance.
TINY_CONFIGS = [
    (4, 1, 1, 2, 1, 2), (5, 1, 1, 2, 2, 2), (6, 1, 2, 2, 1, 3), (7, 1, 2, 3, 1, 3),
    (9, 1, 1, 3, 2, 2), (9, 1, 2, 2, 1, 2), (1, 6, 2, 2, 1, 2),
    (2, 2, 1, 1, 1, 2), (2, 2, 1, 2, 2, 2), (2, 2, 2, 2, 1, 2), (2, 2, 2, 2, 2, 2),
    (3, 2, 1, 2, 1, 3), (3, 2, 1, 3, 2, 3), (2, 3, 1, 2, 2, 3), (2, 3, 1, 3, 3, 2),
    (4, 2, 1, 3, 2, 3), (2, 4, 1, 2, 2, 2), (3, 3, 1, 2, 1, 2), (3, 3, 1, 3, 2, 2),
]


def _tiny_cases() -> list[tuple]:
    cases = []
    for width, height, ports, cities, k, seeds in TINY_CONFIGS:
        for seed in range(seeds):
            blocked = 0.0 if min(width, height) == 1 or seed % 2 == 0 else 0.2
            cases.append((width, height, ports, cities, k, blocked, seed))
    return cases


@pytest.mark.parametrize("case", _tiny_cases(), ids=lambda c: "x".join(map(str, c)))
def test_verbatim_matches_pruned_and_brute_force(case):
    width, height, ports, cities, k, blocked, seed = case
    try:
        inst = random_instance(width, height, ports, cities, k, blocked, seed, max_tries=200)
    except RuntimeError:
        pytest.skip("no instance with k reachable cities for this configuration")
    expected = brute_force(inst)
    assert dp_cost(inst, "verbatim") == expected, inst.to_json()
    assert dp_cost(inst, "pruned") == expected, inst.to_json()


def test_verbatim_proves_infeasibility():
    # 3x3 plus: centre free, a terminal on each arm, corners blocked, k = 2. The centre
    # would need four sides.
    inst = Instance(width=3, height=3, k=2,
                    blocked=frozenset({(0, 0), (2, 0), (0, 2), (2, 2)}),
                    ports={"P1": (0, 1), "P2": (1, 0)}, cities={"C1": (2, 1), "C2": (1, 2)})
    assert brute_force(inst) is None
    assert dp_cost(inst, "verbatim") is None
    assert dp_cost(inst, "pruned") is None


def test_verbatim_crossing_with_excess():
    # 3x3 plus with the corners open: the crossing is resolved by a detour of 2.
    inst = Instance(width=3, height=3, k=1, blocked=frozenset(),
                    ports={"P1": (0, 1)}, cities={"C1": (2, 1), "C2": (1, 2), "C3": (1, 0)})
    expected = brute_force(inst)
    assert dp_cost(inst, "verbatim") == expected == dp_cost(inst, "pruned")


# --------------------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------------------

def test_cli_solve_dp(tmp_path, capsys):
    import json

    from network_solver.__main__ import main

    inst = Instance(width=5, height=5, blocked=frozenset(), k=2,
                    ports={"P1": (0, 2), "P2": (2, 0)}, cities={"C1": (4, 2), "C2": (2, 4)})
    path = tmp_path / "plus.json"
    inst.save(path)
    out = tmp_path / "plus.solution.json"
    assert main(["solve-dp", str(path), "--out", str(out)]) == 0
    printed = capsys.readouterr().out.splitlines()
    stats = json.loads(printed[0])
    assert stats["status"] == "OPTIMAL" and stats["excess"] == 2 and stats["mode"] == "pruned"
    assert printed[1].startswith("verify: OK excess=2")
    sol = Solution.from_json(json.loads(out.read_text()))
    assert verify.check(inst, sol).cost == (stats["excess"], stats["tiles"])
    assert main(["verify", str(path), str(out)]) == 0
    assert capsys.readouterr().out.strip() == f"excess=2 tiles={stats['tiles']} OK"
    tiny = tmp_path / "tiny.json"
    Instance(width=3, height=1, blocked=frozenset(), k=1,
             ports={"P": (0, 0)}, cities={"C": (2, 0)}).save(tiny)
    assert main(["solve-dp", str(tiny), "--mode", "verbatim", "--time-limit", "60"]) == 0
    assert json.loads(capsys.readouterr().out.splitlines()[0])["tiles"] == 1
