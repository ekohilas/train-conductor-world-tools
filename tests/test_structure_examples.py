"""Small checks that back statements made in docs/result.md.

They do not test an algorithm. They pin down one example and one lemma that the report
uses when it explains why the quasi-polynomial goal was not reached.
"""
from __future__ import annotations

import pytest

from network_solver import cpsat, verify
from network_solver.distances import bfs, requirements
from network_solver.generate import random_instance
from network_solver.instance import Instance

INF = float("inf")


def bypass_instance() -> Instance:
    """A plus-shaped corridor system with one long bypass (docs/result.md, section 6.3).

        # d 2 . . . .
        # # . # # # .
        1 . . . . a .
        # # . # # # .
        # # b . . . .

    1, 2 are the ports P1, P2; a, b, d are the cities C1, C2, C4. With k = 2, P1 must
    serve C1 and C2, and P2 must serve C4 and C2. All shortest connections for P1-C1,
    P1-C2 and P2-C2 pass through the centre cell (2, 2) and together need all four of
    its sides.
    """
    width, height = 7, 5
    open_cells = {
        (0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),  # the horizontal corridor
        (2, 0), (2, 1), (2, 3), (2, 4),                  # the vertical corridor
        (1, 0),                                          # C4, next to P2
        (3, 0), (4, 0), (5, 0), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4),
        (5, 4), (4, 4), (3, 4),                          # the bypass from P2 to C2
    }
    blocked = frozenset((x, y) for x in range(width) for y in range(height)
                        if (x, y) not in open_cells)
    return Instance(width=width, height=height, blocked=blocked, k=2,
                    ports={"P1": (0, 2), "P2": (2, 0)},
                    cities={"C1": (5, 2), "C2": (2, 4), "C4": (1, 0)})


def test_segment_need_not_be_a_grid_shortest_path():
    """In the optimum, P2 reaches C2 by the 12-edge bypass although d(P2, C2) = 4, and
    the bypass shares no cell with the rest of the network. So "guess the junctions and
    join them by shortest paths of the grid" cannot find this optimum."""
    inst = bypass_instance()
    reqs = requirements(inst)
    # Both ports have exactly k = 2 candidate cities, so the selection is forced.
    assert set(reqs["P1"].candidates) == {"C1", "C2"}
    assert set(reqs["P2"].candidates) == {"C4", "C2"}
    assert bfs(inst, inst.ports["P2"])[inst.cities["C2"]] == 4

    sol, stats = cpsat.solve(inst, time_limit=60, workers=2)
    assert stats["optimal"], stats
    report = verify.check(inst, sol)
    assert report.ok, report.errors
    assert report.cost == (8, 16)
    # The north arm cell (2, 1) is unused: P2 does not go through the centre.
    assert all((2, 1) not in edge for edge in sol.edges)
    # The bypass is used in full.
    bypass = [(3, 0), (4, 0), (5, 0), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4),
              (5, 4), (4, 4), (3, 4)]
    assert all(cell in sol.track_cells(inst) for cell in bypass)


@pytest.mark.parametrize("seed", range(60))
def test_strict_pairs_have_disjoint_shortest_walks(seed):
    """Observation 6.1 of docs/result.md: if d(p1,c1) < d(p1,c2) and
    d(p2,c2) < d(p2,c1), then no free cell lies on both a shortest p1-c1 walk and a
    shortest p2-c2 walk."""
    inst = random_instance(width=4 + seed % 4, height=4 + (seed // 4) % 4,
                           ports=2 + seed % 2, cities=3 + seed % 3, k=1 + seed % 2,
                           blocked_fraction=0.05 * (seed % 5), seed=1000 + seed)
    dist = {name: bfs(inst, cell)
            for name, cell in list(inst.ports.items()) + list(inst.cities.items())}

    def d(a: str, b: str) -> float:
        cell = inst.cities.get(b) or inst.ports.get(b)
        return dist[a].get(cell, INF)

    free_cells = [(x, y) for x in range(inst.width) for y in range(inst.height)
                  if inst.is_free((x, y))]
    for p1 in inst.ports:
        for p2 in inst.ports:
            for c1 in inst.cities:
                for c2 in inst.cities:
                    if p1 == p2 or c1 == c2:
                        continue
                    if not (d(p1, c1) < d(p1, c2) and d(p2, c2) < d(p2, c1)):
                        continue
                    for z in free_cells:
                        on_first = dist[p1].get(z, INF) + dist[c1].get(z, INF) == d(p1, c1)
                        on_second = dist[p2].get(z, INF) + dist[c2].get(z, INF) == d(p2, c2)
                        assert not (on_first and on_second), (inst.to_json(), p1, c1, p2, c2, z)
