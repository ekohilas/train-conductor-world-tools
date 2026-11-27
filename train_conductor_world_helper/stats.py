"""Holds the stats functions for the train conductor world mapping."""
import collections
import logging

import graphing.pathing.paths
import mapping.world

logger = logging.getLogger(__name__)


def output_track_coordinates_count(
    world_map: mapping.world.World,
) -> None:
    """Calculates the count of all tracks and their environmental coordinates."""
    counters = collections.defaultdict(collections.Counter)
    for track_tile, map_tile in world_map.overlaying_tiles:
        map_tile_name = map_tile.name
        track_tile_name = track_tile.abbreviation

        counters[map_tile_name][track_tile_name] += 1

    for map_tile_name, counter in counters.items():
        _print_counter(map_tile_name, counter)

    total_counter = sum(counters.values(), start=collections.Counter())
    _print_counter("Totals", total_counter)


def _print_counter(
    counter_name: str,
    counter: collections.Counter,
) -> None:
    total = len(list(counter.elements()))
    logger.info("%s (%s):", counter_name, total)
    for key, count in counter.most_common():
        logger.info("%s: %s", key, count)


def count_tracks(
    world_map: mapping.world.World,
) -> int:
    """Counts the number of tracks in the world mapping."""
    count = len(world_map.track_map)
    logger.info("Found %s tracks.", count)
    return count


def find_unused_edges(
    pathing: graphing.pathing.paths.Paths,
) -> int:
    """Outputs the unused edges in the track mapping."""
    logger.info("Looking for unused edges...")

    unvisited_edges = pathing.unused_edges
    unvisited_edges_dict = collections.defaultdict(set)

    number_of_unvisited_edges = len(unvisited_edges)
    if number_of_unvisited_edges == 0:
        logger.info("No unused edges found, awesome!")
        return number_of_unvisited_edges

    logger.warning("Found %s unused edges:", number_of_unvisited_edges)
    for unvisited_edge in unvisited_edges:
        node = unvisited_edge.coordinate
        unvisited_edges_dict[node].add(unvisited_edge)
    for node, edges in sorted(unvisited_edges_dict.items()):
        logger.warning(node)
        for edge in edges:
            path_component = edge.path_component
            logger.warning("\t%s %s", path_component, edge)
    return number_of_unvisited_edges
