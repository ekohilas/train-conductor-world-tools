import dataclasses


@dataclasses.dataclass(frozen=True, order=True)
class Node:
    """Represents a coordinate on the graph."""

    x: float
    y: float

    def __init__(self, x, y):
        # Ensures values are converted to floats.
        object.__setattr__(self, "x", float(x))
        object.__setattr__(self, "y", float(y))

    def __str__(self):
        return f"({self.x}, {self.y})"
