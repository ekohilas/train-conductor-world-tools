import dataclasses
import functools
import typing

import data
import mapping.tile_map


@dataclasses.dataclass
class World:
    """
    Represents the train conductor world via a mapping of tiles and a mapping of tracks.
    """

    tile_map: mapping.tile_map.TileMap
    track_map: mapping.tile_map.TileMap

    @classmethod
    def from_matrices_and_data(
        cls,
        map_matrix: list[list[int]],
        track_matrix: list[list[int]],
        world_data: data.Data,
    ) -> typing.Self:
        """Creates a world from data lists."""
        tile_map = mapping.tile_map.TileMap.from_matrix(
            matrix=map_matrix,
            world_data=world_data,
        )
        track_map = mapping.tile_map.TileMap.from_matrix(
            matrix=track_matrix,
            world_data=world_data,
        )
        return cls(
            tile_map=tile_map,
            track_map=track_map,
        )

    @functools.cached_property
    def overlaying_tiles(
        self,
    ) -> list[tuple[mapping.tile.Tile, mapping.tile.Tile]]:
        """Returns the underlying tile for each track tile in the world mapping."""
        return [
            (track_tile, self.tile_map[track_tile.coordinate])
            for track_tile in self.track_map
        ]
