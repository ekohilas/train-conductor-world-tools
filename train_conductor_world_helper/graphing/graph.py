import typing

import networkx as nx

import graphing.node
import mapping.coordinate
import mapping.tile
import mapping.tile_map
from graphing.pathing.path_component import PathComponent


class Graph:
    """Represents the graph of the train conductor world mapping."""

    def __init__(
        self,
        track_map: mapping.tile_map.TileMap,
    ) -> None:
        self.track_map = track_map
        self._create_track_graph()

    def all_shortest_paths(
        self,
        source_node: graphing.node.Node,
        target_node: graphing.node.Node,
    ) -> typing.Iterable[list[graphing.node.Node]]:
        """Returns all the shortest paths from a source node to a target node."""
        return nx.all_shortest_paths(
            G=self.graph,
            source=source_node,
            target=target_node,
        )

    def _create_track_graph(self) -> None:
        self.graph = nx.Graph()
        self._add_nodes_on_edges()
        self._add_edges_for_tracks()

    def _add_nodes_on_edges(self) -> None:
        """
        Creates a graph similar to a grid of a width and height
            but where each edge of the grid is represented by a node.
        e.g.
        ┌─u─┐   n = ( 0,   0  )
        │   │   u = ( 0,  -0.5)
        l n r   r = ( 0.5, 0  )
        │   │   d = ( 0,   0.5)
        └─d─┘   l = (-0.5, 0  )
        """
        for x in range(self.track_map.width):
            for y in range(self.track_map.height):
                for node in mapping.coordinate.Coordinate(x=x, y=y).edge_nodes:
                    self.graph.add_node(node, pos=(x, y))

    def _add_edges_for_tracks(self) -> None:
        for tile in self.track_map:
            if tile.is_track:
                self._add_edges_for_track(track=tile)

    def _add_edges_for_track(
        self,
        track: mapping.tile.Tile,
    ) -> None:
        for path_component in track.path_component:
            self._add_edge_for_coordinate_and_path_component(
                coordinate=track.coordinate,
                path_component=path_component,
            )

    def _add_edge_for_coordinate_and_path_component(
        self,
        coordinate: mapping.coordinate.Coordinate,
        path_component: PathComponent,
    ) -> None:
        north = coordinate.north
        east = coordinate.east
        south = coordinate.south
        west = coordinate.west

        graph = self.graph
        match path_component:
            case PathComponent.VERTICAL:
                graph.add_edge(north, south)
            case PathComponent.HORIZONTAL:
                graph.add_edge(west, east)
            case PathComponent.UP_RIGHT:
                graph.add_edge(north, east)
            case PathComponent.DOWN_LEFT:
                graph.add_edge(south, west)
            case PathComponent.DOWN_RIGHT:
                graph.add_edge(south, east)
            case PathComponent.UP_LEFT:
                graph.add_edge(north, west)
            case _:
                raise ValueError(
                    f"Expected single path component but got {path_component}."
                )

    def draw_with_coordinates(self, clean=False):
        """A Debugging function to display the underlying graph network."""
        from matplotlib import pyplot as plt

        if clean:
            self.graph.remove_nodes_from(list(nx.isolates(self.graph)))
        pos = nx.get_node_attributes(self.graph, "pos")
        plt.gca().invert_yaxis()
        nx.draw(self.graph, pos, node_size=1)
        plt.show()

    def add_all_edges_to_grid_2d_graph(self) -> None:
        """
        A debugging function that adds all edges between the nodes created on the
        edges of the grid.
        """
        width = self.track_map.width
        height = self.track_map.height
        graph = self.graph

        for x in range(width):
            for y in range(height):
                coordinate = mapping.coordinate.Coordinate(x=x, y=y)

                north = coordinate.north
                east = coordinate.east
                south = coordinate.south
                west = coordinate.west

                graph.add_edge(west, north)
                graph.add_edge(west, east)
                graph.add_edge(west, south)

                graph.add_edge(north, south)
                graph.add_edge(east, north)
                graph.add_edge(east, south)
