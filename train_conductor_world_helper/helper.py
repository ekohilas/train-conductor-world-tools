import dataclasses
import logging
import os

import annotations.annotator
import data

# why does this basic import work?
import graphing
import mapping
import stats

# but this one doesn't? Is it because they were already imported?
import tmx.tiled_map
import validations

PORT_LIMIT = 8

logger = logging.getLogger(__name__)


@dataclasses.dataclass
class Helper:
    """Facilitates the running of all the train conductor world tools."""

    distances_path: os.PathLike
    tiles_path: os.PathLike
    tmx_path: os.PathLike

    def update_map(self) -> None:
        """Re-reads the mapping and runs the helping methods."""
        self._read_map()
        self._run()

    def _run(self) -> None:
        self._stats()
        self._validations()
        self._annotations()

    def __post_init__(self) -> None:
        self.world_data = data.Data(
            distances_filename=self.distances_path,
            tiles_filename=self.tiles_path,
            port_limit=PORT_LIMIT,
        )
        self._read_map()

    def _read_map(self) -> None:
        logger.debug("Reading map...")
        tiled_map = tmx.tiled_map.TiledMap(
            filename=self.tmx_path,
        )
        map_grid = tiled_map.get_layer_data(name="map")
        track_grid = tiled_map.get_layer_data(name="tracks")
        self.world_map = mapping.world.World.from_matrices_and_data(
            map_matrix=map_grid,
            track_matrix=track_grid,
            world_data=self.world_data,
        )
        graph = graphing.graph.Graph(
            track_map=self.world_map.track_map,
        )
        self.paths = graphing.pathing.paths.Paths(
            world_map=self.world_map,
            world_data=self.world_data,
            graph=graph,
        )
        map_graph = graphing.graph.MapGraph(
            tile_map=self.world_map.tile_map,
        )
        self.annotator = annotations.annotator.Annotator(
            tiled_map=tiled_map,
            world_data=self.world_data,
            map_graph=map_graph,
            paths=self.paths,
        )

    def _stats(self) -> None:
        stats.count_tracks(
            world_map=self.world_map,
        )
        stats.output_track_coordinates_count(
            world_map=self.world_map,
        )
        stats.find_unused_edges(
            pathing=self.paths,
        )

    def _validations(self) -> None:
        validations.validate_track_placements(
            world_map=self.world_map,
        )
        validations.validate_distances(
            world_data=self.world_data,
            pathing=self.paths,
        )

    def _annotations(self) -> None:
        self.annotator.annotate_connections()
        self.annotator.annotate_areas()
        self.annotator.save()
