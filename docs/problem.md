# Train Network Problem (frozen definition)

This file is the single source of truth for the problem. The Python verifier
(`network_solver/verify.py`) and the Lean definitions (`lean/TrainNetwork/Problem.lean`)
encode exactly this definition. Changing the problem means changing all three together.

## Input

An instance consists of:

- A rectangular grid of `W × H` cells, `(x, y)` with `0 ≤ x < W`, `0 ≤ y < H`. Two cells
  are **adjacent** when they differ by 1 in exactly one coordinate (4-neighbourhood).
- A set `B` of **blocked** cells (clouds).
- A set `P` of **ports** and a disjoint set `C` of **cities**. Each sits on its own
  non-blocked cell. Together they are the **terminals** `T = P ∪ C`.
- An integer `k ≥ 1` (the real instance uses `k = 9`).

Every other cell (not blocked, not a terminal) is **free**: it may hold a track tile.

Sizes: the theory treats `W`, `H`, `|P|` and `|C|` as unbounded. A result may instead
assume `|P| ≤ 10` and `|C| ≤ 40` when it says so explicitly. The practical benchmark is
`W, H ≤ 100`.

## Grid distance

For a port `p` and a city `c`, `d(p, c)` is the number of steps in a shortest
4-neighbour walk from `p` to `c` whose intermediate cells are all free. Paths never pass
through blocked cells or through any terminal other than their two endpoints.
`d(p, c) = ∞` if no such walk exists.

## Required pairs

For each port `p`, order the cities by `d(p, ·)`. Let `t_p` be the `k`-th smallest value.
It must be finite, otherwise the instance has no solution.

- Every city `c` with `d(p, c) < t_p` is **required** for `p`.
- Among the cities with `d(p, c) = t_p` (the **tie group**), exactly
  `k − #{c : d(p, c) < t_p}` must be **chosen**. Which ones is part of the solution, not
  the input.

## Solution

A solution is:

- a **network** `N`: a set of undirected edges, each joining two adjacent, non-blocked
  cells;
- for each port, its set of chosen cities (required cities plus the tie-group choice).

The **track tiles** of `N` are the free cells touched by at least one edge of `N`.

## Feasibility

A solution is feasible iff:

1. **Degree:** every free cell has at most 3 incident edges in `N`. A track tile is
   straight, a corner, or a T-junction. Every T-junction allows all three turns, and
   there are no crossings. Terminals may use all 4 sides.
2. **Selection:** for every port, the chosen cities are exactly the required ones plus
   the right number from its tie group.
3. **Connectivity:** for every port `p` and every chosen city `c`, `N` contains a walk
   from `p` to `c` whose intermediate cells are all free.

Let `dist_N(p, c)` be the length of the shortest such walk in `N`. Then
`dist_N(p, c) ≥ d(p, c)` always holds.

## Objective

Minimise, **lexicographically**:

1. **Total excess:** `Σ over ports p, chosen cities c of (dist_N(p, c) − d(p, c))`.
2. **Tile count:** the number of track tiles of `N`.

Edges between two terminals are allowed but are never needed. Edges cost nothing beyond
the tiles they touch.

## Decision version (for complexity statements)

*Given an instance and integers `X`, `K`: is there a feasible solution with total excess
`≤ X` and at most `K` track tiles?*

**Input size** is `N = W · H`: the instance is encoded as a dense grid, one symbol per
cell (free / blocked / port / city), plus `k`. A sparse binary encoding (coordinates of
blocked cells in binary) is deliberately *not* used. With it, an instance with few
clouds has size `O(log W)` while an optimal network can need `Θ(W)` tiles, so
"polynomial" would be meaningless.

"Faster than exponential" means running time `2^{o(N)}`. "Polynomial" means `N^{O(1)}`.
When a result assumes `|P| ≤ 10` and `|C| ≤ 40`, the polynomial's degree may depend on
those constants but not on `N`.

## Why the rules are the way they are

- No crossing tile exists. On the real map, Stuttgart→Paris has a single straight
  shortest path along row 27, and every shortest path of Marseille→Mons runs straight up
  column 21 through the same cell. So degree ≤ 3 with exact shortest paths is infeasible.
  Allowing excess length resolves this. A two-T "jog" costs Marseille→Mons +2. See
  `docs/crossing-conflict.html`.
- Distances are measured around clouds and other terminals, not by Manhattan distance.
- Water and mountain cells are free: the "better track" can be placed on anything except
  clouds, cities and ports.

## Reference data

- `data/instances/europe.json`: the real map (49 × 55, 6 ports, 23 cities, 1149 blocked
  cells, `k = 9`), extracted with `python -m network_solver extract`.
- `python -m network_solver solve <instance>`: exact CP-SAT baseline (a two-phase
  lexicographic solve with a slack certificate; see the docstring of
  `network_solver/cpsat.py`).
- `python -m network_solver verify <instance> <solution>`: independent feasibility and
  cost checker.
