import dataclasses
import functools

from graphing.node import Node
from graphing.pathing.path_component import PathComponent
from mapping.coordinate import Coordinate


@dataclasses.dataclass(frozen=True, order=True)
class Edge:
    """Represents an edge that connects two nodes from the graph."""

    from_node: Node
    to_node: Node

    def __init__(self, tuple_: tuple[Node, Node]):
        from_node, to_node = tuple_
        if not isinstance(from_node, Node):
            raise TypeError(f"{from_node} is not of type {Node}")
        if not isinstance(to_node, Node):
            raise TypeError(f"{to_node} is not of type {Node}")
        if from_node > to_node:
            from_node, to_node = to_node, from_node

        object.__setattr__(self, "from_node", from_node)
        object.__setattr__(self, "to_node", to_node)

    @functools.cached_property
    def coordinate(self) -> Coordinate:
        """Returns the calculated coordinate of the edge."""
        from_node, to_node = self.from_node, self.to_node
        from_node_x, from_node_y = from_node.x, from_node.y
        to_node_x, to_node_y = to_node.x, to_node.y

        if from_node_y == to_node_y:
            x = (from_node_x + to_node_x) / 2
            y = from_node_y
        elif from_node_x == to_node_x:
            x = from_node_x
            y = (from_node_y + to_node_y) / 2
        else:
            x = from_node_x if from_node_x.is_integer() else to_node_x
            y = from_node_y if from_node_y.is_integer() else to_node_y
        return Coordinate(x=x, y=y)

    @functools.cached_property
    def path_component(self) -> PathComponent:
        """Calculates and returns the path component given the two nodes of the edge."""
        from_node, to_node = self.from_node, self.to_node

        assert from_node < to_node, "Expected edge nodes to be ordered"

        from_node_x, from_node_y = from_node.x, from_node.y
        to_node_x, to_node_y = to_node.x, to_node.y
        coordinate_x, coordinate_y = self.coordinate.x, self.coordinate.y

        # ┌─┐
        # f t
        # └─┘
        if from_node_y == to_node_y:
            return PathComponent.HORIZONTAL

        # ┌f┐
        # │ │
        # └t┘
        if from_node_x == to_node_x:
            return PathComponent.VERTICAL

        if from_node_x < coordinate_x:
            # ┌t┐
            # fc│
            # └─┘
            if to_node_y < coordinate_y:
                return PathComponent.UP_LEFT
            # ┌─┐
            # fc│
            # └t┘
            return PathComponent.DOWN_LEFT

        # ┌f┐
        # │ct
        # └─┘
        if from_node_y < coordinate_y:
            return PathComponent.UP_RIGHT

        # ┌─┐
        # │ct
        # └f┘
        return PathComponent.DOWN_RIGHT

    def __str__(self):
        return f"{self.from_node}->{self.to_node}"
