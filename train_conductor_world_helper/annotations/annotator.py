"""
Contains classes used for creating annotations through adding layers to the tmx file.
"""

import dataclasses
import logging

import graphing.graph
import annotations.connection_annotators
import annotations.area_annotators

# Type checking
import data
import graphing.pathing
import tmx.tiled_map

EMPTY_TILE_ID = 0

logger = logging.getLogger(__name__)


@dataclasses.dataclass
class Annotator:
    """Adds annotations through layers to the supplied tmx file."""

    tiled_map: tmx.tiled_map.TiledMap
    paths: graphing.pathing.paths.Paths
    map_graph: graphing.graph.MapGraph
    world_data: data.Data

    def __post_init__(self):
        self.width = self.tiled_map.width
        self.height = self.tiled_map.height
        self.annotation_layers: list[tmx.layers.layer] = []

    def annotate_areas(self) -> None:
        """Annotates the port and city areas of the tmx file."""
        annotator = annotations.area_annotators.AreasAnnotator(
            width=self.width,
            height=self.height,
            layer_name="Areas",
            world_data=self.world_data,
            map_graph=self.map_graph,
        )
        logger.info("Annotating areas...")
        annotation_layer = annotator.create_layer()
        self.annotation_layers.append(annotation_layer)

    def annotate_connections(self) -> None:
        """Annotates the port and city connections of the tmx file."""
        annotator = annotations.connection_annotators.ConnectionsAnnotator(
            width=self.width,
            height=self.height,
            layer_name="Annotations",
            world_data=self.world_data,
            paths=self.paths,
        )
        logger.info("Annotating layers...")
        annotation_layer = annotator.create_layer()
        self.annotation_layers.append(annotation_layer)

    def save(self):
        """Saves the created annotation layers to the `tmx_map`"""
        self.tiled_map.save_layers(*self.annotation_layers)
