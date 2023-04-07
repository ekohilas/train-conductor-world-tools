"""Holds the annotators for creating connection annotation layers."""
import dataclasses
import functools
import typing

import annotations.base_annotators
import data
import graphing.pathing.paths
import mapping.coordinate
from graphing.pathing.path_component import PathComponent


@dataclasses.dataclass
class ConnectionTileLayerAnnotator(annotations.base_annotators.TileLayerAnnotator):
    """A base class to annotate connection tile layers."""

    world_data: data.Data
    city_name: str

    def coordinate_to_connection_component(
            self, coordinate: mapping.coordinate.Coordinate
    ) -> PathComponent:
        raise NotImplementedError

    def coordinate_to_tile_id(
            self,
            coordinate: mapping.coordinate.Coordinate,
    ) -> int:
        connection_component = self.coordinate_to_connection_component(
            coordinate=coordinate,
        )
        tile_id = self.world_data.tile_id_from(
            city_name=self.city_name,
            connection_component=connection_component,
        )
        return tile_id


@dataclasses.dataclass
class CityToPortConnectionAnnotator(ConnectionTileLayerAnnotator):
    """A layer of city to port connections."""

    world_data: data.Data
    paths: graphing.pathing.paths.Paths

    @functools.cached_property
    def _coordinate_to_merged_path_component(
            self,
    ) -> dict[mapping.coordinate.Coordinate, PathComponent,]:
        city_name = self.city_name
        city_coordinate_to_path_components = {}
        for port_name in self.world_data.port_names_of(city_name=city_name):
            coordinate_to_path_component = self.paths.connection_path(
                port_name=port_name, city_name=city_name
            )
            for coordinate, path_component in coordinate_to_path_component.items():
                city_coordinate_to_path_components[coordinate] |= path_component
        return city_coordinate_to_path_components

    def coordinate_to_connection_component(
            self,
            coordinate: mapping.coordinate.Coordinate,
    ) -> PathComponent:
        return self._coordinate_to_merged_path_component[coordinate]


@dataclasses.dataclass
class CityConnectionsAnnotator(annotations.base_annotators.GroupLayerAnnotator):
    """A group layer of city connections."""

    world_data: data.Data
    paths: graphing.pathing.paths.Paths

    def child_annotators(
            self,
    ) -> typing.Iterable[annotations.base_annotators.LayerAnnotator]:
        return (
            CityToPortConnectionAnnotator(
                width=self.width,
                height=self.height,
                layer_name=city_name,
                city_name=city_name,
                world_data=self.world_data,
                paths=self.paths,
            )
            for city_name in self.world_data.city_names
        )


@dataclasses.dataclass
class PortToCityConnectionAnnotator(ConnectionTileLayerAnnotator):
    """A layer representing the connection between a port and a city."""

    port_name: str
    city_name: str
    world_data: data.Data
    paths: graphing.pathing.paths.Paths

    @functools.cached_property
    def _coordinate_to_path_component(
            self,
    ) -> dict[mapping.coordinate.Coordinate, PathComponent,]:
        return self.paths.connection_path(
            port_name=self.port_name,
            city_name=self.city_name,
        )

    def coordinate_to_connection_component(
            self,
            coordinate: mapping.coordinate.Coordinate,
    ) -> PathComponent:
        return self._coordinate_to_path_component[coordinate]


@dataclasses.dataclass
class PortConnectionAnnotator(annotations.base_annotators.GroupLayerAnnotator):
    """A group layer for port to city connections."""

    port_name: str
    world_data: data.Data
    paths: graphing.pathing.paths.Paths

    def child_annotators(
            self,
    ) -> typing.Iterable[annotations.base_annotators.LayerAnnotator]:
        return (
            PortToCityConnectionAnnotator(
                width=self.width,
                height=self.height,
                layer_name=city_name,
                port_name=self.port_name,
                city_name=city_name,
                world_data=self.world_data,
                paths=self.paths,
            )
            for city_name in self.world_data.city_names_from(
            port_name=self.layer_name,
        )
        )


@dataclasses.dataclass
class PortConnectionsAnnotator(annotations.base_annotators.GroupLayerAnnotator):
    """A group layer of ports and their connections."""

    world_data: data.Data
    paths: graphing.pathing.paths.Paths

    def child_annotators(
            self,
    ) -> typing.Iterable[annotations.base_annotators.LayerAnnotator]:
        return (
            PortConnectionAnnotator(
                width=self.width,
                height=self.height,
                layer_name=port_name,
                port_name=port_name,
                world_data=self.world_data,
                paths=self.paths,
            )
            for port_name in self.world_data.port_names
        )


@dataclasses.dataclass
class ConnectionsAnnotator(annotations.base_annotators.GroupLayerAnnotator):
    """A group layer of port and city connections."""

    world_data: data.Data
    paths: graphing.pathing.paths.Paths

    def child_annotators(
            self,
    ) -> typing.Iterable[annotations.base_annotators.LayerAnnotator]:
        city_annotator = CityConnectionsAnnotator(
            width=self.width,
            height=self.height,
            layer_name="City Connections",
            world_data=self.world_data,
            paths=self.paths,
        )
        port_annotator = PortConnectionsAnnotator(
            width=self.width,
            height=self.height,
            layer_name="Port Connections",
            world_data=self.world_data,
            paths=self.paths,
        )
        return city_annotator, port_annotator
