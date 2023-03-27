import dataclasses
import enum
import functools

from graphing.node import Node


class _CardinalDirection(enum.Enum):
    """Represents a cardinal direction and it's coordinate delta."""

    NORTH = (0, -1)
    EAST = (1, 0)
    SOUTH = (0, 1)
    WEST = (-1, 0)


@dataclasses.dataclass(frozen=True, order=True)
class Coordinate:
    """Represents a coordinate on the world mapping."""

    x: int
    y: int

    def __post_init__(self):
        # Ensures values are converted to ints.
        object.__setattr__(self, "x", int(self.x))
        object.__setattr__(self, "y", int(self.y))

    @functools.cached_property
    def north(self) -> Node:
        """Returns the north edge node of the coordinate."""
        return self._direction_to_node[_CardinalDirection.NORTH]

    @functools.cached_property
    def east(self) -> Node:
        """Returns the east edge node of the coordinate."""
        return self._direction_to_node[_CardinalDirection.EAST]

    @functools.cached_property
    def south(self) -> Node:
        """Returns the south edge node of the coordinate."""
        return self._direction_to_node[_CardinalDirection.SOUTH]

    @functools.cached_property
    def west(self) -> Node:
        """Returns the west edge node of the coordinate."""
        return self._direction_to_node[_CardinalDirection.WEST]

    @functools.cached_property
    def edge_nodes(self) -> frozenset[Node]:
        """Returns nodes along the edges of the coordinate."""
        return frozenset(self._direction_to_node.values())

    @staticmethod
    def _neighboring_nodes(
        x: int | float,
        y: int | float,
        delta: float | int = 1,
    ) -> list[(_CardinalDirection, Node)]:
        neighboring_nodes = []
        for direction in _CardinalDirection:
            x_offset, y_offset = direction.value
            neighboring_nodes.append(
                (
                    direction,
                    Node(
                        x=x + x_offset * delta,
                        y=y + y_offset * delta,
                    ),
                )
            )
        return neighboring_nodes

    @functools.cached_property
    def _direction_to_node(self) -> dict[_CardinalDirection, Node]:
        """
        Given a coordinate, returns the coordinates a delta away in each cardinal
        direction.
        """
        delta = 0.5
        direction_to_node = {}
        for direction in _CardinalDirection:
            x_offset, y_offset = direction.value
            direction_to_node[direction] = Node(
                x=self.x + x_offset * delta,
                y=self.y + y_offset * delta,
            )
        return direction_to_node

    @functools.cached_property
    def neighbor_nodes(self) -> set[Node]:
        """
        Returns the neighbouring coordinates for each cardinal direction.
        """
        return set(
            node
            for _, node in Coordinate._neighboring_nodes(
                x=self.x,
                y=self.y,
            )
        )

    def __str__(self):
        return f"({self.x}, {self.y})"
