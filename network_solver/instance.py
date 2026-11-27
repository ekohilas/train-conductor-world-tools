"""Instance and solution data types, plus JSON I/O and extraction from the Tiled map.

See docs/problem.md for the formal definition these types encode.
"""
from __future__ import annotations

import dataclasses
import json
import os
import xml.etree.ElementTree as ET

Cell = tuple[int, int]  # (x, y); x is the column, y is the row, (0, 0) top-left.
Edge = frozenset  # frozenset({cell_a, cell_b}) of two orthogonally adjacent cells.


@dataclasses.dataclass(frozen=True)
class Instance:
    """A problem instance. See docs/problem.md, section "Input"."""

    width: int
    height: int
    blocked: frozenset[Cell]
    ports: dict[str, Cell]
    cities: dict[str, Cell]
    k: int = 9

    def __post_init__(self) -> None:
        terminals = list(self.ports.values()) + list(self.cities.values())
        if len(set(terminals)) != len(terminals):
            raise ValueError("Two terminals share a cell.")
        for cell in terminals:
            if not self.in_bounds(cell):
                raise ValueError(f"Terminal {cell} out of bounds.")
            if cell in self.blocked:
                raise ValueError(f"Terminal {cell} is on a blocked cell.")
        if set(self.ports) & set(self.cities):
            raise ValueError("A name is used for both a port and a city.")
        for cell in self.blocked:
            if not self.in_bounds(cell):
                raise ValueError(f"Blocked cell {cell} out of bounds.")
        if not 1 <= self.k <= len(self.cities):
            raise ValueError(f"k={self.k} must satisfy 1 <= k <= number of cities.")

    @property
    def terminals(self) -> frozenset[Cell]:
        return frozenset(self.ports.values()) | frozenset(self.cities.values())

    def in_bounds(self, cell: Cell) -> bool:
        x, y = cell
        return 0 <= x < self.width and 0 <= y < self.height

    def is_free(self, cell: Cell) -> bool:
        """A free cell may hold a track tile."""
        return (
            self.in_bounds(cell)
            and cell not in self.blocked
            and cell not in self.terminals
        )

    def neighbours(self, cell: Cell) -> list[Cell]:
        x, y = cell
        out = []
        for nxt in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if self.in_bounds(nxt) and nxt not in self.blocked:
                out.append(nxt)
        return out

    def to_json(self) -> dict:
        return {
            "width": self.width,
            "height": self.height,
            "k": self.k,
            "blocked": sorted([list(c) for c in self.blocked]),
            "ports": {n: list(c) for n, c in sorted(self.ports.items())},
            "cities": {n: list(c) for n, c in sorted(self.cities.items())},
        }

    @classmethod
    def from_json(cls, data: dict) -> "Instance":
        return cls(
            width=data["width"],
            height=data["height"],
            k=data.get("k", 9),
            blocked=frozenset(tuple(c) for c in data["blocked"]),
            ports={n: tuple(c) for n, c in data["ports"].items()},
            cities={n: tuple(c) for n, c in data["cities"].items()},
        )

    @classmethod
    def load(cls, path: os.PathLike) -> "Instance":
        with open(path, encoding="utf-8") as f:
            return cls.from_json(json.load(f))

    def save(self, path: os.PathLike) -> None:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.to_json(), f, indent=1)
            f.write("\n")


@dataclasses.dataclass
class Solution:
    """A track network: a set of undirected track connections between adjacent cells,
    plus the city chosen for each port (needed only to resolve distance ties)."""

    edges: set[Edge]
    pairs: dict[str, list[str]]

    def track_cells(self, instance: Instance) -> set[Cell]:
        return {c for e in self.edges for c in e if instance.is_free(c)}

    def cost(self, instance: Instance) -> int:
        return len(self.track_cells(instance))

    def to_json(self, instance: Instance) -> dict:
        return {
            "tiles": self.cost(instance),
            "pairs": {p: sorted(cs) for p, cs in sorted(self.pairs.items())},
            "edges": sorted(sorted(list(c) for c in e) for e in self.edges),
        }

    @classmethod
    def from_json(cls, data: dict) -> "Solution":
        return cls(
            edges={frozenset(tuple(c) for c in e) for e in data["edges"]},
            pairs={p: list(cs) for p, cs in data["pairs"].items()},
        )


def from_tiled_map(tmx_path: os.PathLike, tiles_path: os.PathLike, k: int = 9) -> Instance:
    """Builds the instance from the repo's Tiled map: clouds are blocked, Location tiles
    are ports/cities. Everything else (water, mountain, ...) is free, per the
    "better track" rule in docs/problem.md."""
    with open(tiles_path, encoding="utf-8") as f:
        tiles = {t["tmx_id"]: t for t in json.load(f)}
    root = ET.parse(tmx_path).getroot()
    layer = next(l for l in root.iter("layer") if l.get("name") == "map")
    rows = [
        [int(v) for v in line.split(",") if v.strip()]
        for line in layer.find("data").text.strip().splitlines()
    ]
    blocked, ports, cities = set(), {}, {}
    for y, row in enumerate(rows):
        for x, tile_id in enumerate(row):
            tile = tiles.get(tile_id)
            if tile is None:
                continue
            if tile["name"] == "Cloud":
                blocked.add((x, y))
            elif tile.get("group") == "Location":
                (ports if tile["type"] == "Port" else cities)[tile["name"]] = (x, y)
    return Instance(
        width=len(rows[0]),
        height=len(rows),
        blocked=frozenset(blocked),
        ports=ports,
        cities=cities,
        k=k,
    )
