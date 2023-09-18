import collections
import functools
import logging
import typing

import networkx as nx

from train_conductor_world_helper import data
import graphing.graph
import mapping.coordinate
import mapping.world
from graphing.edge import Edge
from graphing.node import Node
from graphing.pathing.path_component import PathComponent

logger = logging.getLogger(__name__)


class Paths:
    """Represents the paths of connections within the train conductor world mapping."""

    def __init__(
            self,
            world_map: mapping.world.World,
            world_data: data.Data,
            graph: graphing.graph.Graph,
    ):
        self.world_map = world_map
        self.graph = graph
        self.world_data = world_data

    def distance_between(
            self,
            port_name: str,
            city_name: str,
    ) -> int:
        """Returns the calculated distance from the given port to the given city."""
        return len(
            self._path(
                port_name=port_name,
                city_name=city_name,
            )
        )

    def _path(
            self,
            port_name: str,
            city_name: str,
    ) -> list[graphing.edge.Edge]:
        return self._min_paths_dict[port_name][city_name]

    @functools.cache
    def connection_path(
            self,
            port_name: str,
            city_name: str,
    ) -> dict[mapping.coordinate.Coordinate, PathComponent]:
        """
        Returns the coordinates and path components from the port to the city.
        """
        edges = self._path(port_name, city_name)
        return {edge.coordinate: edge.path_component for edge in edges}

    @functools.cached_property
    def unused_edges(self) -> set[Edge]:
        """Returns all edges of the graph which are untouched by paths."""
        return set(Paths._create_edges(self.graph.graph.edges)) - self._used_edges()

    def _used_edges(self) -> set[Edge]:
        return {
            edge
            for city_to_edge_list in self._min_paths_dict.values()
            for edge_list in city_to_edge_list.values()
            for edge in edge_list
        }

    @functools.cached_property
    def _min_paths_dict(self) -> dict[str, dict[str, list[Edge]]]:
        world_data = self.world_data

        tile_map = self.world_map.tile_map

        paths_dict = collections.defaultdict(dict)
        for port_name in world_data.port_names:
            port_edge_nodes = tile_map.coordinate_of(port_name).edge_nodes
            for city_name in world_data.city_names_from(
                    port_name=port_name,
            ):
                city_edge_nodes = tile_map.coordinate_of(city_name).edge_nodes
                node_paths = self._collate_paths(
                    port_edge_nodes=port_edge_nodes,
                    city_edge_nodes=city_edge_nodes,
                )
                valid_paths = []
                for min_node_path in node_paths:
                    min_edge_path = Paths._create_edges(
                        zip(min_node_path, min_node_path[1:])
                    )
                    if not Paths._invalid_path(path=min_edge_path):
                        valid_paths.append(min_edge_path)

                min_valid_path_length = min(
                    map(len, valid_paths),
                    default=[],
                )
                min_valid_paths = [
                    valid_path
                    for valid_path in valid_paths
                    if len(valid_path) == min_valid_path_length
                ]

                match len(min_valid_paths):
                    case 0:
                        min_path = []
                    case 1:
                        min_path = min_valid_paths[0]
                    case _:
                        logger.warning(
                            (
                                "More than one minimum path found from %s -> %s."
                                "Defaulting to the first."
                            ),
                            port_name,
                            city_name,
                        )
                        logger.debug("Minimum paths found: %s", min_valid_paths)
                        min_path = min_valid_paths[0]

                paths_dict[port_name][city_name] = min_path

        return paths_dict

    @functools.cached_property
    def _min_valid_paths_dict(self) -> dict[str, dict[str, list[list[Edge]]]]:
        world_data = self.world_data

        tile_map = self.world_map.tile_map

        paths_dict = collections.defaultdict(dict)
        for port_name in world_data.port_names:
            port_edge_nodes = tile_map.coordinate_of(port_name).edge_nodes
            for city_name in world_data.city_names_from(
                    port_name=port_name,
            ):
                city_edge_nodes = tile_map.coordinate_of(city_name).edge_nodes
                node_paths = self._collate_paths(
                    port_edge_nodes=port_edge_nodes,
                    city_edge_nodes=city_edge_nodes,
                )
                valid_paths = []
                for min_node_path in node_paths:
                    min_edge_path = Paths._create_edges(
                        zip(min_node_path, min_node_path[1:])
                    )
                    if not Paths._invalid_path(path=min_edge_path):
                        valid_paths.append(min_edge_path)

                min_valid_path_length = min(
                    map(len, valid_paths),
                    default=[],
                )
                min_valid_paths = [
                    valid_path
                    for valid_path in valid_paths
                    if len(valid_path) == min_valid_path_length
                ]

                paths_dict[port_name][city_name] = min_valid_paths

        return paths_dict

    def valid_min_paths(self, port_name: str, city_name: str, ) -> list[list[Edge]]:
        return self._min_valid_paths_dict[port_name][city_name]

    @functools.cache
    def _collate_paths(
            self,
            port_edge_nodes: frozenset[Node],
            city_edge_nodes: frozenset[Node],
    ) -> list[list[Node]]:
        all_paths = []
        for port_edge_node in port_edge_nodes:
            for city_edge_node in city_edge_nodes:
                try:
                    paths = self.graph.all_shortest_paths(
                        source_node=port_edge_node,
                        target_node=city_edge_node,
                    )
                    all_paths += paths
                except nx.NetworkXNoPath:
                    pass
        return all_paths

    @staticmethod
    def _invalid_path(path: list[Edge]) -> bool:
        if len(path) < 2:
            return False
        for edge_1, edge_2 in zip(path, path[1:]):
            if edge_1.coordinate == edge_2.coordinate:
                return True
        return False

    @staticmethod
    def _create_edges(
            edges: typing.Iterable[tuple[Node, Node]],
    ) -> list[Edge]:
        return [Edge(edge) for edge in edges]
