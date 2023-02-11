import logging
import os
from xml.etree import ElementTree as ET

import tmx.layers

NEXT_LAYER_ID_FIELD = "nextlayerid"

logger = logging.getLogger(__name__)


class TiledMap:
    """An Interface for a tmx xml file."""

    def __init__(
        self,
        filename: os.PathLike,
    ) -> None:
        self.filename = filename
        self.tree = ET.parse(self.filename)
        self.root = self.tree.getroot()
        self.width = int(self.root.get("width"))
        self.height = int(self.root.get("height"))

    def get_layer(
        self,
        name: str | None = None,
        layer_id: int | None = None,
    ) -> tmx.layers.Layer:
        """Returns the layer for a given name or id."""
        try:
            return tmx.layers.TileLayer.from_element(
                self._get_layer(
                    name=name,
                    layer_id=layer_id,
                )
            )
        except ValueError:
            return tmx.layers.GroupLayer.from_element(
                self._get_layer(
                    layer_type="group",
                    name=name,
                    layer_id=layer_id,
                )
            )

    def get_layer_data(
        self,
        *args,
        **kwargs,
    ) -> list[list[int]]:
        """Returns finds the requested layer and returns its layer data."""
        return tmx.layers.TileLayer.from_element(
            self._get_layer(
                *args,
                **kwargs,
            )
        ).data

    def _get_layer(
        self,
        layer_type: str = "layer",
        name: str | None = None,
        layer_id: int = None,
        parent: None = None,
    ) -> ET.Element:
        if parent is None:
            parent = self.root
        if layer_id is None and name is None:
            raise ValueError("name or id was not given.")
        for layer in parent.findall(layer_type):
            if layer.get("name") == name or layer.get("id") == str(layer_id):
                return layer
        raise ValueError(f"Layer with name `{name}` not found.")

    def add_layer(
        self,
        layer: tmx.layers.Layer,
    ) -> None:
        """Adds the layer to the tmx state."""
        self._add_layer(layer=layer)

    def _add_layer(
        self,
        layer: tmx.layers.Layer,
        parent: ET.Element | None = None,
    ) -> None:
        if isinstance(layer, tmx.layers.GroupLayer):
            self._add_group_layer(group_layer=layer, parent=parent)
        elif isinstance(layer, tmx.layers.TileLayer):
            layer_dimensions = layer.width, layer.height
            tmx_dimensions = self.width, self.height
            if layer_dimensions != tmx_dimensions:
                raise ValueError(
                    f"Mismatch in dimensions layer={layer_dimensions} tmx={tmx_dimensions}"
                )
            self._add_data_layer(layer=layer, parent=parent)
        else:
            raise ValueError(
                f"Argument {type(layer)} is not of type {tmx.layers.GroupLayer} or {tmx.layers.TileLayer}"
            )

    def _add_data_layer(
        self,
        layer: tmx.layers.TileLayer,
        parent: ET.Element | None = None,
    ) -> None:
        try:
            layer_to_edit = self._get_layer(
                name=layer.name, layer_id=layer.id, parent=parent
            )
        except ValueError:
            self._append_layer(
                layer=layer,
                parent=parent,
            )
        else:
            layer_to_edit.find("data").text = tmx.layers.TileLayer.to_csv_string(
                layer.data
            )

    def _append_layer(
        self,
        layer: tmx.layers.Layer,
        parent: ET.Element | None = None,
    ):
        if parent is None:
            parent = self.root

        next_layer_id = self._get_next_layer_id()
        layer.id = next_layer_id
        self.root.set(NEXT_LAYER_ID_FIELD, str(next_layer_id + 1))

        layer_to_add = layer.to_element()
        parent.append(layer_to_add)

        return layer_to_add

    def _add_group_layer(
        self,
        group_layer: tmx.layers.GroupLayer,
        parent: ET.Element | None,
    ) -> None:
        try:
            group_layer_to_edit = self._get_layer(
                layer_type="group",
                name=group_layer.name,
                layer_id=group_layer.id,
                parent=parent,
            )
        except ValueError:
            parent = self._append_layer(layer=group_layer, parent=parent)
            for layer in reversed(group_layer.layers):
                self._add_layer(
                    layer=layer,
                    parent=parent,
                )
        else:
            for layer in reversed(group_layer.layers):
                self._add_layer(
                    layer=layer,
                    parent=group_layer_to_edit,
                )

    def _get_next_layer_id(self):
        return int(self.root.get(NEXT_LAYER_ID_FIELD))

    def save(self) -> None:
        """Saves the current state to the tmx file."""
        logger.info("Saving to %s...", self.filename)
        self.tree.write(self.filename)
        logger.info("Saved!")

    def save_layers(self, *layers: tmx.layers.Layer) -> None:
        """Adds each layer and saves it to the tmx file."""
        for layer in layers:
            self.add_layer(layer)
        self.save()
