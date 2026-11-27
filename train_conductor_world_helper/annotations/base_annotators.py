"""Holds the base annotators for creating tmx layers."""
import dataclasses
import typing

import mapping.coordinate
import tmx.layers

EMPTY_TILE_ID = 0


class LayerAnnotator:
    """Base layer annotator."""

    def create_layer(self) -> tmx.layers.Layer:
        """Creates and returns a layer."""
        raise NotImplementedError


@dataclasses.dataclass
class TileLayerAnnotator(LayerAnnotator):
    """Base annotator for layers with tiles."""

    width: int
    height: int
    layer_name: str

    def create_layer(self) -> tmx.layers.TileLayer:
        """Creates and returns a tile layer."""
        layer_data = self._create_data()
        layer = tmx.layers.TileLayer(
            name=self.layer_name,
            data=layer_data,
        )
        return layer

    def _create_data(self) -> list[list[int]]:
        return [
            [
                self._coordinate_to_tile_id(mapping.coordinate.Coordinate(x, y))
                for x in range(self.width)
            ]
            for y in range(self.height)
        ]

    def coordinate_to_tile_id(
        self,
        coordinate: mapping.coordinate.Coordinate,
    ) -> int:
        """Returns a tile id given a coordinate."""
        raise NotImplementedError

    def _coordinate_to_tile_id(
        self,
        coordinate: mapping.coordinate.Coordinate,
    ) -> int:
        try:
            return self.coordinate_to_tile_id(coordinate=coordinate)
        except KeyError:
            return EMPTY_TILE_ID


@dataclasses.dataclass
class GroupLayerAnnotator(LayerAnnotator):
    """Base annotator for layers with child layers."""

    width: int
    height: int
    layer_name: str

    def create_layer(self) -> tmx.layers.GroupLayer:
        """
        Returns a group layer containing the child layers from the given annotators.
        """
        layers = list(self._child_layers())
        layer = tmx.layers.GroupLayer(
            name=self.layer_name,
            layers=layers,
        )
        return layer

    def _child_layers(self) -> typing.Iterable[tmx.layers.Layer]:
        return (annotator.create_layer() for annotator in self.child_annotators())

    def child_annotators(self) -> typing.Iterable[LayerAnnotator]:
        """Returns a list of annotators on which `create_layer` is called."""
        raise NotImplementedError
