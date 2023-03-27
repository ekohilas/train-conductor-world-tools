"""
Contains classes to store data of the train conductor world mapping.
"""
import collections
import functools
import json
import os

from graphing.pathing.path_component import PathComponent

CELL_ID_REFERENCE = "tmx_id"


class Data:
    """
    Reads, calculates, and stores data of the train conductor world mapping.
    """

    def __init__(
            self,
            distances_filename: os.PathLike,
            tiles_filename: os.PathLike,
            port_limit: int,
    ):
        distances_json_dict = self._read_json(json_filename=distances_filename)
        self._port_to_city_distance = self._create_port_to_city_distance_dict(
            distances_json=distances_json_dict,
            port_limit=port_limit,
        )

        tiles_list = self._read_json(json_filename=tiles_filename)
        self._connection_to_tile_id = self._create_connection_to_tile_id(
            tiles_list=tiles_list,
        )
        self._id_to_tile = self._create_id_to_tile_dict(tiles_list=tiles_list)

    def port_names_of(
            self,
            city_name: str,
    ) -> list[str]:
        """
        Returns the names of the ports that are to be connected to the given city name.
        """
        return self._port_names_of_city_names[city_name]

    def distance_between(
            self,
            port_name: str,
            city_name: str,
    ) -> int:
        """
        Returns the minimum expected distance between the given port and city.
        """
        return self._port_to_city_distance[port_name][city_name]

    def city_names_from(
            self,
            port_name: str,
    ) -> list[str]:
        """Returns a list of city names expected to be connected to the given port."""
        return self._city_names_from_port[port_name]

    def data_of(
            self,
            tile_id: int,
    ) -> dict:
        """Returns the tile data for a given tile id."""
        return self._id_to_tile[tile_id]

    def tile_id_from(
            self,
            city_name: str,
            connection_component: PathComponent,
    ) -> int:
        """
        Returns the tile id representing the connection component for the given city.
        """
        return self._connection_to_tile_id[(city_name, connection_component)]

    @functools.cached_property
    def city_names(self) -> list[str]:
        """
        Returns the train conductor world mapping city names that are to be connected.
        """
        return sorted(
            {
                city_name
                for port_name, city_to_distance_dict in
                self._port_to_city_distance.items()
                for city_name in city_to_distance_dict
            }
        )

    @functools.cached_property
    def port_names(self) -> list[str]:
        """Returns the train conductor world mapping port names."""
        return sorted(self._port_to_city_distance)

    @functools.cached_property
    def _port_names_of_city_names(
            self,
    ) -> dict[str, list[str]]:
        city_name_to_port_name_of_city_names = collections.defaultdict(list)
        for port_name, city_to_distance in self._port_to_city_distance.items():
            for city_name in sorted(
                    city_to_distance,
                    key=city_to_distance.get,
            ):
                city_name_to_port_name_of_city_names[city_name].append(port_name)
        return city_name_to_port_name_of_city_names

    @functools.cached_property
    def port_to_city_name_pairs(
            self,
    ) -> list[tuple[str, str]]:
        """Returns all the port and city names that are to be connected as pairs."""
        return [
            (port_name, city_name)
            for port_name, city_to_distance in self._port_to_city_distance.items()
            for city_name in city_to_distance
        ]

    @functools.cached_property
    def _city_names_from_port(
            self,
    ) -> dict[str, list[str]]:
        return {
            port_name: sorted(
                city_to_distance,
                key=city_to_distance.get,
            )
            for port_name, city_to_distance in self._port_to_city_distance.items()
        }

    @staticmethod
    def _create_id_to_tile_dict(
            tiles_list: list[dict[str, str | int | list[str] | float | bool]],
    ) -> dict[int, dict[str, str | int | list[str] | float | bool]]:
        return {
            int(tile_dict[CELL_ID_REFERENCE]): tile_dict for tile_dict in tiles_list
        }

    @staticmethod
    def _create_connection_to_tile_id(
            tiles_list: list[dict[str, str | int | list[str] | float | bool]],
    ) -> dict[tuple[str, PathComponent], int]:
        connection_to_tile_id = collections.defaultdict()
        for tile in tiles_list:
            if "type" not in tile:
                continue
            if tile["group"] != "Connection":
                continue
            city_name = tile["type"]
            connection_component = PathComponent.from_dict(dictionary=tile)
            tile_id = tile[CELL_ID_REFERENCE]
            connection_to_tile_id[(city_name, connection_component)] = tile_id
        return connection_to_tile_id

    @staticmethod
    def _read_json(
            json_filename: os.PathLike,
    ) -> (
            list[
                dict[str, str | int | bool]
                | dict[str, str | int | list[str] | float | bool]
                | dict[str, str | int | list[str] | bool]
                ]
            | dict[str, list[dict[str, str | int]]]
    ):
        with open(json_filename, encoding="utf8") as file:
            return json.load(file)

    @staticmethod
    def _create_port_to_city_distance_dict(
            distances_json: dict,
            port_limit: int,
    ) -> dict[str, dict[str, int]]:
        distance_dict = collections.defaultdict(dict)
        for port_name, distance_list in distances_json.items():
            for distance_object in distance_list[:port_limit]:
                city_name = distance_object["name"]
                distance_dict[port_name][city_name] = distance_object["distance"]
        return distance_dict
