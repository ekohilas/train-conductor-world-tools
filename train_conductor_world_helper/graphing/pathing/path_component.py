import enum
import functools
import operator


class PathComponent(enum.Flag):
    """Represents the shape of a connection edge."""

    NONE = 0
    VERTICAL = enum.auto()
    HORIZONTAL = enum.auto()
    UP_RIGHT = enum.auto()
    DOWN_LEFT = enum.auto()
    DOWN_RIGHT = enum.auto()
    UP_LEFT = enum.auto()

    @classmethod
    def from_dict(cls, dictionary: dict[str, bool]):
        """Returns a PathComponent made up of one or more PathComponents."""
        return functools.reduce(
            operator.or_,
            (
                path_component
                for path_component in cls
                if dictionary.get(path_component.name.lower(), False)
            ),
            cls.NONE,
        )
