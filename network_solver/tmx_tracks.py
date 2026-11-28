"""Convert between a Solution's track network and the Tiled map's `tracks` layer.

Tiles used are the "Transparent" track set from data/tiles.json (the track that can be
placed on anything except clouds, cities and ports):

    arms {U,D} │ 83   {L,R} ─ 84   {U,R} └ 85   {D,L} ┐ 86   {D,R} ┌ 87   {U,L} ┘ 88
    arms {U,D,R} ┣ 101   {L,R,D} ┳ 102   {L,R,U} ┻ 103   {U,D,L} ┫ 104

The T-junctions 101-104 allow all three turns, as docs/problem.md assumes. "Up" is y-1.

    python -m network_solver.tmx_tracks export SOLUTION.json OUT.tmx
    python -m network_solver.tmx_tracks check [TMX]   # verify a map's tracks layer
"""
from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import re
import sys
import xml.etree.ElementTree as ET

from network_solver import verify
from network_solver.distances import requirements
from network_solver.instance import Cell, Instance, Solution, from_tiled_map

ROOT = pathlib.Path(__file__).resolve().parent.parent
TMX = ROOT / "data/train-conductor-world.tmx"
TILES = ROOT / "data/tiles.json"

DIRS = {"U": (0, -1), "D": (0, 1), "L": (-1, 0), "R": (1, 0)}
ARMS_TO_TILE = {
    frozenset("UD"): 83, frozenset("LR"): 84, frozenset("UR"): 85, frozenset("DL"): 86,
    frozenset("DR"): 87, frozenset("UL"): 88, frozenset("UDR"): 101,
    frozenset("LRD"): 102, frozenset("LRU"): 103, frozenset("UDL"): 104,
}


def _tile_arms() -> dict[int, frozenset[str]]:
    """Arms of every track tile in tiles.json, keyed by tmx id (all track types)."""
    comp = {"vertical": "UD", "horizontal": "LR", "up_right": "UR",
            "down_left": "DL", "down_right": "DR", "up_left": "UL"}
    out = {}
    for tile in json.loads(TILES.read_text()):
        if tile.get("group") == "Track":
            out[tile["tmx_id"]] = frozenset("".join(d for k, d in comp.items() if tile.get(k)))
    return out


def solution_to_grid(instance: Instance, solution: Solution) -> list[list[int]]:
    arms: dict[Cell, set[str]] = {}
    for edge in solution.edges:
        a, b = tuple(edge)
        for src, dst in ((a, b), (b, a)):
            if instance.is_free(src):
                d = next(k for k, (dx, dy) in DIRS.items() if (src[0] + dx, src[1] + dy) == dst)
                arms.setdefault(src, set()).add(d)
    grid = [[0] * instance.width for _ in range(instance.height)]
    for (x, y), a in arms.items():
        key = frozenset(a)
        if key not in ARMS_TO_TILE:
            raise ValueError(f"cell {(x, y)} has arms {sorted(a)}: no tile for that shape")
        grid[y][x] = ARMS_TO_TILE[key]
    return grid


def grid_to_edges(instance: Instance, grid: list[list[int]]) -> tuple[set, list[str]]:
    """Edges of a tracks grid. An arm counts if it points at a terminal, or at a track
    whose own arm points back. Returns (edges, problems)."""
    arms_of = _tile_arms()
    opposite = {"U": "D", "D": "U", "L": "R", "R": "L"}
    edges, problems = set(), []
    for y, row in enumerate(grid):
        for x, gid in enumerate(row):
            if not gid:
                continue
            if gid not in arms_of:
                problems.append(f"cell {(x, y)}: tile id {gid} is not a track")
                continue
            if not instance.is_free((x, y)):
                problems.append(f"cell {(x, y)}: track on a cloud or terminal")
            for d in arms_of[gid]:
                dx, dy = DIRS[d]
                n = (x + dx, y + dy)
                if not instance.in_bounds(n) or n in instance.blocked:
                    problems.append(f"cell {(x, y)}: arm {d} points off-map or into a cloud")
                elif n in instance.terminals:
                    edges.add(frozenset(((x, y), n)))
                elif opposite[d] in arms_of.get(grid[n[1]][n[0]], frozenset()):
                    edges.add(frozenset(((x, y), n)))
                else:
                    problems.append(f"cell {(x, y)}: arm {d} is not met by a track at {n}")
    return edges, problems


def best_report(instance: Instance, edges: set) -> tuple[Solution, verify.Report]:
    """Verifies a network, choosing the tie-group cities that give the lowest cost."""
    reqs = requirements(instance)
    options = [[list(r.required) + list(extra) for extra in itertools.combinations(r.tied, r.choose)]
               for r in reqs.values()]
    best = None
    for combo in itertools.product(*options):
        sol = Solution(edges=set(edges), pairs=dict(zip(reqs, combo)))
        rep = verify.check(instance, sol)
        key = (len(rep.errors), rep.excess, rep.tiles)
        if best is None or key < best[0]:
            best = (key, sol, rep)
    return best[1], best[2]


def read_tracks(tmx_path: pathlib.Path) -> list[list[int]]:
    root = ET.parse(tmx_path).getroot()
    layer = next(l for l in root.iter("layer") if l.get("name") == "tracks")
    return [[int(v) for v in line.split(",") if v.strip()]
            for line in layer.find("data").text.strip().splitlines()]


def write_tracks(src: pathlib.Path, out: pathlib.Path, grid: list[list[int]]) -> None:
    """Copies the map, replacing only the tracks layer's CSV data (text-level edit, so
    the rest of the file is byte-identical)."""
    text = src.read_text()
    csv = "\n" + "\n".join(",".join(map(str, row)) + "," for row in grid)
    csv = csv[:-1] + "\n"  # Tiled omits the comma after the last cell
    pattern = re.compile(r'(<layer [^>]*name="tracks"[^>]*>\s*<data encoding="csv">)(.*?)(</data>)', re.S)
    new, n = pattern.subn(lambda m: m.group(1) + csv + m.group(3), text)
    if n != 1:
        raise ValueError("could not find exactly one tracks layer")
    out.write_text(new)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="network_solver.tmx_tracks")
    sub = parser.add_subparsers(dest="cmd", required=True)
    ex = sub.add_parser("export")
    ex.add_argument("solution")
    ex.add_argument("out")
    ch = sub.add_parser("check")
    ch.add_argument("tmx", nargs="?", default=str(TMX))
    args = parser.parse_args(argv)
    instance = from_tiled_map(TMX, TILES)

    if args.cmd == "export":
        sol = Solution.from_json(json.loads(pathlib.Path(args.solution).read_text()))
        grid = solution_to_grid(instance, sol)
        write_tracks(TMX, pathlib.Path(args.out), grid)
        args.tmx = args.out
    grid = read_tracks(pathlib.Path(args.tmx))
    edges, problems = grid_to_edges(instance, grid)
    sol, rep = best_report(instance, edges)
    for p in problems:
        print("tile problem:", p)
    for e in rep.errors:
        print("network problem:", e)
    print(f"{args.tmx}: excess={rep.excess} tiles={rep.tiles}",
          "OK" if rep.ok and not problems else "INVALID")
    return 0 if rep.ok and not problems else 1


if __name__ == "__main__":
    sys.exit(main())
