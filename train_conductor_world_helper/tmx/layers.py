#!/usr/bin/env python3
"""Represents a Python interface for a tmx file."""

import dataclasses
import logging
import xml.etree.ElementTree as ET

import validations

logger = logging.getLogger(__name__)


@dataclasses.dataclass(kw_only=True)
class Layer:
    """Base class of a tmx layer."""

    # TODO: Add to_element and from_element here to be inherited?
    name: str
    locked: bool = True
    id: int = None

    @classmethod
    def from_element(
        cls,
        element: ET.Element,
    ):
        """Returns the Element as a Layer."""
        return cls(
            id=int(element.get("id")),
            name=element.get("name"),
            locked=bool(element.get("locked")),
        )


@dataclasses.dataclass(kw_only=True)
class GroupLayer(Layer):
    """Class for keeping a tmx group layer."""

    layers: list[Layer]

    @classmethod
    def from_element(
        cls,
        element: ET.Element,
    ):
        """Returns the Element as a Layer."""
        layers = [
            # TODO: This won't work when there's a group within a group.
            TileLayer.from_element(layer_element)
            for layer_element in element.findall("layer")
        ]
        return cls(
            id=int(element.get("id")),
            name=element.get("name"),
            locked=bool(element.get("locked")),
            layers=layers,
        )

    def to_element(self) -> ET.Element:
        """Returns the Layer as an Element."""
        if self.id is None:
            raise ValueError("id was not set.")
        layer_element = ET.Element(
            "group",
            {
                "id": str(self.id),
                "name": str(self.name),
                "locked": "1" if self.locked else "0",
            },
        )
        return layer_element


@dataclasses.dataclass(kw_only=True)
class TileLayer(Layer):
    """Class for interfacing between tmx xml layers."""

    data: list[list[int]]
    width: int = None
    height: int = None

    def __post_init__(self):
        self.width = validations.validate_width(self.data)
        self.height = len(self.data)

    @classmethod
    def from_element(cls, element: ET.Element) -> "TileLayer":
        """Returns the Element as a Layer."""
        return cls(
            id=int(element.get("id")),
            name=element.get("name"),
            width=int(element.get("width")),
            height=int(element.get("height")),
            locked=bool(element.get("locked")),
            data=TileLayer._to_data(element.find("data").text),
        )

    def to_element(self) -> ET.Element:
        """Returns the Layer as an Element."""
        if self.id is None:
            raise ValueError("id was not set.")
        layer_element = ET.Element(
            "layer",
            {
                "id": str(self.id),
                "name": str(self.name),
                "width": str(self.width),
                "height": str(self.height),
                "locked": "1" if self.locked else "0",
            },
        )
        data_element = ET.Element("data", encoding="csv")
        data_element.text = TileLayer.to_csv_string(self.data)
        layer_element.append(data_element)
        return layer_element

    @staticmethod
    def _to_data(csv_data: str) -> list[list[int]]:
        return [list(map(int, line.split(","))) for line in csv_data.split(",\n")]

    @staticmethod
    def to_csv_string(
        grid: list[list[int]],
    ) -> str:
        """Converts a 2d grid to a csv string."""
        if not all(isinstance(item, int) for row in grid for item in row):
            raise TypeError(f"Found non int item in {grid}")
        return ",\n".join(",".join(map(str, row)) for row in grid)
