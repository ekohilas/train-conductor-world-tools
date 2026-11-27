"""Hand-built instance families used as evidence in docs/result.md.

All of them have a constant number of terminals. They show what bounding the number of
terminals does *not* give: bounded detours, bounded networks, or feasibility for free.
"""
from __future__ import annotations

from network_solver.instance import Instance


def from_ascii(rows: list[str], k: int) -> Instance:
    """`#` blocked, `.` free, a digit is a port, a letter is a city."""
    width = len(rows[0])
    blocked, ports, cities = set(), {}, {}
    for y, row in enumerate(rows):
        if len(row) != width:
            raise ValueError("ragged map")
        for x, ch in enumerate(row):
            if ch == "#":
                blocked.add((x, y))
            elif ch.isdigit():
                ports["P" + ch] = (x, y)
            elif ch.isalpha():
                cities["C" + ch] = (x, y)
            elif ch != ".":
                raise ValueError(f"bad symbol {ch!r}")
    return Instance(width=width, height=len(rows), blocked=frozenset(blocked),
                    ports=ports, cities=cities, k=k)


def plus_instance() -> Instance:
    """One port, three cities, k = 3, at the ends of a plus-shaped corridor.

    Every grid distance is finite, so the required pairs are well defined, but the
    centre cell would need four edges: the instance has no feasible solution.
    """
    return from_ascii(["##a##",
                       "##.##",
                       "1...b",
                       "##.##",
                       "##c##"], k=3)


def ring_instance(n: int) -> Instance:
    """Two ports, two cities, k = 2: a plus-shaped crossing with arms of length n,
    plus a single by-pass corridor from the north arm around the east city to the
    south arm. Grid side 2n + 5.

    The centre cannot carry both the west-east and the north-south traffic, so the
    north port reaches both cities through the by-pass. The optimal excess is 6n + 6:
    it grows linearly with the side of the grid although there are only 4 terminals.
    """
    if n < 3:
        raise ValueError("n >= 3 (for smaller n the by-pass touches the arms)")
    size = 2 * n + 5
    c = n + 2
    g = [["#"] * size for _ in range(size)]
    for i in range(2, 2 * n + 3):
        g[c][i] = "."
        g[i][c] = "."
    g[c][2], g[c][2 * n + 2] = "1", "a"
    g[2][c], g[2 * n + 2][c] = "2", "b"
    for x in range(c + 1, size):
        g[3][x] = "."
        g[size - 4][x] = "."
    for y in range(3, size - 3):
        g[y][size - 1] = "."
    return from_ascii(["".join(r) for r in g], k=2)


def snake_instance(n: int) -> Instance:
    """One port, one city, k = 1, at the two ends of a boustrophedon corridor that
    fills a (2n+1) x (2n+1) grid. The unique network uses Theta(W * H) track tiles."""
    size = 2 * n + 1
    g = [["#"] * size for _ in range(size)]
    for y in range(0, size, 2):
        for x in range(size):
            g[y][x] = "."
    for i, y in enumerate(range(1, size, 2)):
        g[y][size - 1 if i % 2 == 0 else 0] = "."
    g[0][0] = "1"
    g[size - 1][size - 1 if n % 2 == 0 else 0] = "a"
    return from_ascii(["".join(r) for r in g], k=1)
