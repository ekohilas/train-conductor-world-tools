import dataclasses
import functools
import typing

import data
import validations
from mapping.coordinate import Coordinate
from mapping.tile import Tile


@dataclasses.dataclass
class TileMap:
    """Represents the mapping of tiles within train conductor world."""

    grid: list
    width: int
    height: int

    @classmethod
    def from_matrix(
        cls,
        matrix: list[list[int]],
        world_data: data.Data,
    ) -> "TileMap":
        """Creates a TileMap from a given 2d integer list."""
        height = len(matrix)
        width = validations.validate_width(matrix)

        grid = []
        for y, row in enumerate(matrix):
            tiles = []
            for x, id_ in enumerate(row):
                tiles.append(
                    Tile.create_tile(
                        id_=id_,
                        coordinate=Coordinate(x=x, y=y),
                        world_data=world_data,
                    )
                )
            grid.append(tiles)

        return cls(grid=grid, width=width, height=height)

    @functools.cached_property
    def _name_to_coordinate(self) -> dict[str, Coordinate]:
        return {tile.name: tile.coordinate for tile in self if tile.group == "Location"}

    def coordinate_of(
        self,
        name: str,
    ) -> Coordinate:
        """Returns the coordinate of a given location name on the tile mapping."""
        return self._name_to_coordinate[name]

    def __iter__(self) -> typing.Iterator[Tile]:
        return (tile for row in self.grid for tile in row if tile is not None)

    def __getitem__(
        self,
        coordinate: Coordinate,
    ) -> Tile:
        return self.grid[coordinate.y][coordinate.x]

    def __len__(self) -> int:
        return sum(1 for _ in self)
