"""Holds the annotators for creating connection annotation layers."""
import dataclasses
import functools
import typing

import annotations.base_annotators
import data
import graphing.pathing.paths
import graphing.graph
import mapping.coordinate
from graphing.pathing.path_component import PathComponent

HIGHLIGHT_TILE_ID = 1


@dataclasses.dataclass
class AreaTileLayerAnnotator(annotations.base_annotators.TileLayerAnnotator):
    """A base class to annotate connection tile layers."""

    world_data: data.Data
    city_name: str

    def in_area(self, coordinate: mapping.coordinate.Coordinate) -> bool:
        raise NotImplementedError

    def coordinate_to_tile_id(
        self,
        coordinate: mapping.coordinate.Coordinate,
    ) -> int:
        if self.in_area(coordinate=coordinate):
            return HIGHLIGHT_TILE_ID

        raise KeyError


@dataclasses.dataclass
class PortToCityAreaAnnotator(AreaTileLayerAnnotator):
    """A layer representing the connection between a port and a city."""

    port_name: str
    city_name: str
    world_data: data.Data
    map_graph: graphing.graph.MapGraph

    @functools.cached_property
    def _area_coordinates(
        self,
    ) -> set[mapping.coordinate.Coordinate]:
        area_coordinates = set(
            mapping.coordinate.Coordinate(x=x, y=y)
            for node_list in self.map_graph.all_paths(
                port_name=self.port_name,
                city_name=self.city_name,
            )
            for x, y in node_list
        )
        port_coordinate = self.map_graph.tile_map.coordinate_of(self.port_name)
        city_coordinate = self.map_graph.tile_map.coordinate_of(self.city_name)
        area_coordinates.remove(port_coordinate)
        area_coordinates.remove(city_coordinate)
        return area_coordinates

    def in_area(
        self,
        coordinate: mapping.coordinate.Coordinate,
    ) -> bool:
        return coordinate in self._area_coordinates


@dataclasses.dataclass
class PortToCityAnnotator(annotations.base_annotators.GroupLayerAnnotator):
    """A group layer for port to city connections."""

    port_name: str
    world_data: data.Data
    map_graph: graphing.graph.MapGraph

    def child_annotators(
        self,
    ) -> typing.Iterable[annotations.base_annotators.LayerAnnotator]:
        return (
            PortToCityAreaAnnotator(
                width=self.width,
                height=self.height,
                layer_name=city_name,
                port_name=self.port_name,
                city_name=city_name,
                world_data=self.world_data,
                map_graph=self.map_graph,
            )
            for city_name in self.world_data.city_names_from(
                port_name=self.layer_name,
            )
        )


@dataclasses.dataclass
class AreasAnnotator(annotations.base_annotators.GroupLayerAnnotator):
    """A group layer of ports and their connections."""

    world_data: data.Data
    map_graph: graphing.graph

    def child_annotators(
        self,
    ) -> typing.Iterable[annotations.base_annotators.LayerAnnotator]:
        return (
            PortToCityAnnotator(
                width=self.width,
                height=self.height,
                layer_name=port_name,
                port_name=port_name,
                world_data=self.world_data,
                map_graph=self.map_graph,
            )
            for port_name in self.world_data.port_names
        )
