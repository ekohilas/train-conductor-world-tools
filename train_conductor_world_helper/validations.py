"""Holds the validation functions for the train conductor world mapping."""
import logging

import data

logger = logging.getLogger(__name__)


def validate_track_placements(
    world_map: "mapping.map.World",
) -> bool:
    """Returns whether all track placements are valid on the world mapping."""
    check_passed = True

    for track_tile, map_tile in world_map.overlaying_tiles:
        if not track_tile.placeable_on(map_tile):
            logger.error(
                "%s %s track at coordinate %s can't be placed on %s",
                track_tile.abbreviation,
                track_tile.type,
                track_tile.coordinate,
                map_tile,
            )
            check_passed = False

    if check_passed:
        logger.info("All track placements are valid. You are awesome!")
    return check_passed


def validate_distances(
    world_data: data.Data,
    pathing: "graphing.paths.Paths",
) -> bool:
    """Returns whether all the connection distances are of the expected length."""
    logger.info("Checking all distances...")
    check_passed = True
    for port_name, city_name in world_data.port_to_city_name_pairs:
        actual_distance = pathing.distance_between(
            port_name=port_name,
            city_name=city_name,
        )
        expected_distance = world_data.distance_between(
            port_name=port_name,
            city_name=city_name,
        )
        if actual_distance != expected_distance:
            check_passed = False
            if actual_distance == 0:
                logger.warning("%s -> %s is not connected.", port_name, city_name)
            else:
                logger.warning(
                    "%s -> %s distance is non minimum.\tExpected %s but was %s.",
                    port_name,
                    city_name,
                    expected_distance,
                    actual_distance,
                )
    if check_passed:
        logger.info("All distance tests passed. You are awesome!")
    return check_passed


def validate_width(grid: list[list[int]]) -> int:
    """Gets the width of a grid while ensuring all rows are of the same length."""
    widths = list(map(len, grid))
    for row, (width, next_width) in enumerate(zip(widths, widths[1:])):
        if width != next_width:
            raise ValueError(
                f"Length of row {row + 1} was different ({width} != {next_width})"
            )
    return width
