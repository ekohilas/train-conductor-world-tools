import sys

from tmx.tiled_map import TiledMap


def main():
    """Provides a command line interface for a tmx file."""
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <map.tmx>")
        raise SystemExit

    filename = sys.argv[1]
    tmx = TiledMap(filename)
    #    tmx.save()
    print(tmx)


if __name__ == "__main__":
    main()
