import collections
import dataclasses

import data
import graphing.graph
import mapping.world
import tmx.tiled_map
import itertools


@dataclasses.dataclass
class Solver:
    tmx_path: str
    distances_path: str
    tiles_path: str

    def __post_init__(self):
        tiled_map = tmx.tiled_map.TiledMap(
            filename=self.tmx_path,
        )
        self.world_data = data.Data(
            distances_filename=self.distances_path,
            tiles_filename=self.tiles_path,
            port_limit=6,
        )
        map_grid = tiled_map.get_layer_data(name="map")
        track_grid = tiled_map.get_layer_data(name="tracks")
        self.world_map = mapping.world.World.from_matrices_and_data(
            map_matrix=map_grid,
            track_matrix=track_grid,
            world_data=self.world_data,
        )
        self.map_graph = graphing.graph.MapGraph(
            tile_map=self.world_map.tile_map,
        )

    def _city_powerset(self, port_name: str):
        city_names = self.world_data.city_names_from(port_name)
        return list(powerset(city_names))

    def _smallest_spanning_trees(
        self, port_name: str, city_names: list[str]
    ) -> list[list]:
        city_name_to_paths = {
            city_name: self.map_graph.all_paths(
                port_name=port_name, city_name=city_name
            )
            for city_name in city_names
        }
        city_name_combinations = itertools.combinations(
            city_name_to_paths, len(city_names)
        )
        trees = collections.defaultdict(list)
        for city_name_combination in city_name_combinations:
            city_paths = [
                city_name_to_paths[city_name] for city_name in city_name_combination
            ]
            path_combinations = itertools.product(*city_paths)
            for path_combination in path_combinations:
                merged_paths = set(
                    coordinate
                    for city_path in path_combination
                    for coordinate in city_path
                )
                trees[len(merged_paths)].append(merged_paths)
        return trees[min(trees)]

    def smallest_spanning_trees_of_size(
        self,
        port_name: str,
        size: int | None = None,
    ) -> list[set]:
        if size is None:
            city_combinations = [self.world_data.city_names_from(port_name)]
        else:
            city_combinations = [
                set
                for set in self._city_powerset(port_name=port_name)
                if len(set) == size
            ]
        for city_combination in city_combinations:
            for tree in self._smallest_spanning_trees(
                port_name=port_name, city_names=city_combination
            ):
                print(city_combination, sorted(tree))


import copy
import itertools
import matplotlib.pyplot as plt
import networkx as nx


def powerset(iterable):
    s = list(iterable)
    return itertools.chain.from_iterable(
        itertools.combinations(s, r) for r in range(len(s) + 1)
    )


# The Dreyfus-Wagner algorithm for the Steiner tree problem in graphs is
# built around a theorem: That for a vertex u and a set X of terminals, there
# exists a vertex v and a subset X' of X such that an optimal Steiner tree on
# (X U u) is the union of a shortest path from v to u, an optimal Steiner tree
# of (X' U v), and an optimal Steiner tree of (X \ X' U v).
#
# The algorithm thus works by trying every v and every X' and taking the one
# that results in minimum length. The results are memoized, thus replicating
# the equivalent dynamic programming algorithm that builds the results from
# the smallest subsets upward.
#
# Its running time is O(n^2 3^n), so it is practical  on at most a couple of
# dozen terminals.


# return a list containing all proper subsets of s (each represented as a list)
def _powerset(s):
    return (c for r in range(1, len(s)) for c in itertools.combinations(s, r))


# do the DW algorithm for the given Graph, set of terminals vertex u,
# all-pairs shortest paths dictionary, and memoization cache.
#
# memo has key (u, list of terminals) and value (v, subset, weight)
#
# TODO change those to named tuples?
def _dw_solve(G: nx.Graph, terminals, u, apsp, memo={}):
    # pmrint(f"_dw_solve {u=} {terminals=}")
    if (u, terminals) in memo:
        return memo[(u, terminals)][2]

    # show progress
    if len(terminals) >= len(G.graph["terminals"]) - 2:
        print(f"{u=} {terminals=}")

    maxweight = G.size(weight="weight")

    if len(terminals) == 1:
        bestv = None
        bestsubset = None
        bestweight = apsp[u][terminals[0]]
    else:
        assert len(terminals) > 1
        bestweight = maxweight
        for v in G.nodes:
            xvert_set = set(terminals)
            for x in _powerset(terminals):  # X'
                xset = set(x)
                xpset = xvert_set.difference(xset)  # X \ X'
                w1 = apsp[u][v]
                if w1 >= bestweight:  # already greater than best seen
                    continue
                w2 = _dw_solve(G, tuple(sorted(list(xset))), v, apsp, memo)
                if w1 + w2 >= bestweight:  # already greater than best seen
                    continue
                w3 = _dw_solve(G, tuple(sorted(list(xpset))), v, apsp, memo)
                w = w1 + w2 + w3
                if w < bestweight:
                    bestv = v
                    bestsubset = copy.copy(x)
                    bestweight = w

    assert bestweight < maxweight
    memo[(u, terminals)] = (bestv, bestsubset, bestweight)
    return bestweight


# add an edge (u,v) to H if the edge exists in G, otherwise add the edges
# comprising a shortest path from u to v in G
def _dw_add_path(G, u, v, H, terminals):
    if G.has_edge(u, v):
        if _can_add_edge(H, u, v, terminals):
            # weight = G[u][v]["weight"]
            weight = 1
            H.add_edge(u, v, weight=weight)
    else:
        paths = nx.algorithms.shortest_paths.all_shortest_paths(
            G, u, v, weight="weight"
        )
        for path in paths:
            if all(_can_add_edge(H, a, b, terminals) for a, b in zip(path, path[1:])):
                for a, b in zip(path, path[1:]):
                    weight = 1
                    H.add_edge(a, b, weight=weight)
                break


def _can_add_edge(H, u, v, terminals) -> bool:
    no_edge = not H.has_edge(u, v)
    is_terminal = v in terminals
    if not is_terminal:
        return no_edge
    not_already_connected = H.degree(v) == 0
    return no_edge and not_already_connected


# build the Steiner tree from the optimal decompositions stored in the
# memoization cache by _dw_solve.
def _dw_build_graph(T, terminals, u, G, memo, depth=0):
    indent = "  " * depth
    if len(terminals) == 1:
        w = 0
        if terminals[0] != u:
            w = _dw_add_path(G, terminals[0], u, T, terminals)
        return
    # bestv, bestsubset, _ = memo[(u, terminals)]
    bestv, bestsubset, bestw = memo[(u, terminals)]
    w = _dw_add_path(G, u, bestv, T, terminals)
    _dw_build_graph(T, bestsubset, bestv, G, memo, depth + 1)
    term_set = set(terminals)
    xpset = term_set.difference(bestsubset)
    _dw_build_graph(T, tuple(sorted(list(xpset))), bestv, G, memo, depth + 1)


# This is the only external function. It takes a graph and returns:
# - A NetworkX graph containing the optimal Steiner tree if weight_only = False
# - The total weight of the optimal Steiner tree if weight_only = True
def dreyfus_wagner(G: nx.Graph, weight_only=False):
    apsp = dict(nx.algorithms.shortest_paths.all_pairs_dijkstra_path_length(G))
    cache = {}
    terminals = sorted(g.graph["terminals"])
    u0 = terminals[0]
    t0 = tuple(terminals[1:])
    weight = _dw_solve(G, t0, u0, apsp, cache)

    if weight_only:
        return weight

    T = nx.Graph(Remark="Optimal Steiner tree via Dreyfus-Wagner")
    _dw_build_graph(T, tuple(terminals[1:]), terminals[0], G, cache)

    bestv, _, _ = cache[(u0, t0)]
    w = _dw_add_path(G, u0, bestv, T, terminals)

    return T


def do_steiner(g):
    print(g)
    print(g.graph)
    print(g.nodes)
    print(g.nodes.data())
    print(g.edges)
    print(g.graph["terminals"])

    T = dreyfus_wagner(g)
    print(T.size(weight="weight"))

    pos = graphing.graph.IdentityDict()
    plt.gca().invert_yaxis()
    nx.draw_networkx(T, pos, with_labels=True, node_size=1)
    plt.savefig("steiner.png")
    plt.show()


def steiner():
    global g, coordinate
    solver.map_graph.draw_with_coordinates()
    g = solver.map_graph.graph
    port_name = "Rotterdam"
    city_names = solver.world_data.city_names_from(port_name)
    city_nodes = []
    for city_name in city_names:
        coordinate = solver.world_map.tile_map.coordinate_of(city_name)
        city_nodes.append((coordinate.x, coordinate.y))
    port_coordinate = solver.map_graph.tile_map.coordinate_of(port_name)
    terminals = [(port_coordinate.x, port_coordinate.y)] + city_nodes
    g.graph["terminals"] = city_nodes
    do_steiner(g)


if __name__ == "__main__":
    solver = Solver(
        tmx_path="./data/train-conductor-world.tmx",
        tiles_path="./data/tiles.json",
        distances_path="./data/distances.json",
    )
    # steiner()
    port_name = "Rotterdam"
    solver.smallest_spanning_trees_of_size(port_name=port_name)
