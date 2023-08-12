#!/usr/bin/env python3

"""Represents the command line interface for the helper."""

import logging
import pathlib

import click

import helper
import updater

DATA_DIR = pathlib.Path("./data/")
DEFAULT_DISTANCES_FILENAME = DATA_DIR / "distances.json"
DEFAULT_TILES_FILENAME = DATA_DIR / "tiles.json"
DEFAULT_TMX_FILENAME = DATA_DIR / "train-conductor-world.tmx"
DEFAULT_AUTO_UPDATE = True
DEFAULT_LOGGING_LEVEL = logging.INFO


@click.command()
@click.option(
    "--distances-path",
    help="Path to distances json file.",
    default=DEFAULT_DISTANCES_FILENAME,
)
@click.option(
    "--tmx-path",
    help="Path to mapping tmx file.",
    default=DEFAULT_TMX_FILENAME,
)
@click.option(
    "--tiles-path",
    help="Path to tile json file.",
    default=DEFAULT_TILES_FILENAME,
)
@click.option(
    "--auto-update/--no-auto-update",
    help="Whether to update the tmx file on changes.",
    default=DEFAULT_AUTO_UPDATE,
)
@click.option(
    "--verbose",
    is_flag=True,
    help="Enables verbose debug logging output.",
    default=False,
)
def main(
    tmx_path: pathlib.Path,
    tiles_path: pathlib.Path,
    distances_path: pathlib.Path,
    auto_update: bool,
    verbose: bool,
) -> None:
    """The main entry point for the helper."""
    logging_level = logging.DEBUG if verbose else DEFAULT_LOGGING_LEVEL
    logging.basicConfig(level=logging_level)

    train_conductor_world_helper = helper.Helper(
        tmx_path=tmx_path,
        distances_path=distances_path,
        tiles_path=tiles_path,
    )

    def update_function():
        train_conductor_world_helper.update_map()

    if auto_update:
        updater.poll_and_call_on_updates(
            filename=tmx_path,
            callable_on_update=update_function,
        )
    else:
        update_function()


if __name__ == "__main__":
    main()
