import dataclasses
import typing

import data
import mapping.coordinate
from graphing.pathing.path_component import PathComponent


@dataclasses.dataclass
class Tile:
    """Represents a tile on a train conductor world mapping."""

    # TODO: create subclasses for different tile types?
    id: int
    name: str
    abbreviation: str
    coordinate: mapping.coordinate.Coordinate
    group: str
    type: str = ""
    branching: bool = False
    overlays: list = dataclasses.field(default_factory=list)
    path_component: set = dataclasses.field(default_factory=set)

    @property
    def is_track(self) -> bool:
        """Returns whether the tile is a track."""
        return self.group == "Track"

    def placeable_on(self, tile: typing.Self) -> bool:
        """Returns whether the tile is placeable on the given tile."""
        if not self.is_track:
            raise ValueError(f"{self} is not a track.")

        if self.type != "Transparent" and tile.name not in self.overlays:
            return False
        if tile.name in ("Cloud", "Mountain"):
            return False
        if self.branching and tile.name == "Water":
            return False
        return True

    @classmethod
    def create_tile(
        cls,
        id_: int,
        coordinate: mapping.coordinate.Coordinate,
        world_data: data.Data,
    ) -> typing.Optional[typing.Self]:
        """Creates a tile with its required data given the tile id."""
        if id_ == 0:
            return None
        tile_data = world_data.data_of(tile_id=id_)
        path_component = PathComponent.from_dict(
            dictionary=tile_data,
        )
        return cls(
            name=tile_data["name"],
            abbreviation=tile_data["abbreviation"],
            id=id_,
            coordinate=coordinate,
            group=tile_data["group"],
            type=tile_data.get("type", ""),
            path_component=path_component,
            branching=tile_data.get("branching", False),
            overlays=tile_data.get("overlays", []),
        )
