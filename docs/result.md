# Result: the goal was **not** reached

**Claim asked for** (`lean/TrainNetwork/Goal.lean`): with at most 10 ports and at most
40 cities, the Train Network Problem of `docs/problem.md` can be solved optimally in
time polynomial in `N = W · H`.

**Outcome.** We did not find such an algorithm and we did not prove the claim.
`lean/TrainNetwork/Answer.lean` does not exist, so `Goal.lean` does not compile, and
`lean/TrainNetwork.lean` deliberately does not import it. Nothing in this repository
should be read as a proof of `goal_polytime`.

We also did not disprove the claim. We do not know whether it is true. Section 4
explains what blocks a proof and why we think the claim is out of reach of current
techniques, but that is an assessment, not a theorem.

What this repository does contain:

| | Statement | Status |
|---|---|---|
| T0 | An executable exhaustive solver returns an optimal solution, or `none` exactly when no feasible solution exists. No bound on ports or cities is needed. It is exponential and makes no running-time claim. | **Machine-checked in Lean** (§5) |
| T1 | With `m` chosen pairs, some optimal network has at most `m(m−1)` T-junction tiles, and the problem reduces to `N^{O(m²)}` instances of a routing problem **R** with `O(m²)` paths. | Paper proof (§3) |
| C2 | For bounded terminals, *feasibility* is decidable in polynomial time. This uses the Robertson–Seymour disjoint-paths theorem as a black box. | Paper proof (§3), not formalised |
| C3 | With `c` crossroads (free cells with four open neighbours) the *optimum* is computable in time `4^c · N^{O(m²)}`: polynomial for bounded terminals when `c = O(log N)`. | Paper proof (§3), not formalised |
| T4 | The search algorithm of `network_solver/exact.py` is exact. Its worst case is exponential. | Paper proof (§6), tested against CP-SAT on 296 random instances |

The second frozen theorem, `goal_polytime`, is open in every form: we have no
polynomial bound for any exact algorithm, in Lean or on paper.

---

## 1. The statement that was asked

```lean
theorem goal_correct (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I

theorem goal_polytime :
    ∃ q : Polynomial ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (Answer.solve I).time ≤ q.eval I.size
```

Here `Answer.solve : Instance → TimeM (Option Solution)` must charge every primitive
step with a `tick` (the auditing rule of `Cost.lean`). Lean does not check that rule.
A function that wraps an exhaustive search in `pure` has `time = 0` and would make both
theorems type-check. We did not do that: our exhaustive solver is a plain function
outside `TimeM`, and we claim no running time for it.

## 2. Notation and three lemmas

Fix an instance. The *grid graph* `G` has the open (in-bounds, non-blocked) cells as
vertices and the pairs of adjacent open cells as edges. A *valid walk* from `s` to `t`
is a walk in `G` whose intermediate cells are all free. `d(s, t)` is the length of a
shortest one. A *selection* `S = (S_p)` assigns to every port a set of `k` cities that
is a nearest choice (`IsNearestChoice`). The pairs `(p, c)` with `c ∈ S_p` are the
*chosen pairs*, and `m = |P| · k ≤ 400` is their number. A network is a set of edges of
`G`. A *crossroads* is a free cell with four open neighbours. A network satisfies the
degree rule iff it misses at least one of the four grid edges at every crossroads; no
other cell can violate the rule.

The grid is bipartite, so all walks between two given cells have the same parity. Every
pair's excess is therefore even.

**Path systems.** A *path system* for a selection `S` is a family `𝒲 = (W_pc)` of
simple valid paths, one from `p` to `c` for every chosen pair. Its *union* `U(𝒲)` is
the set of edges used. It is *admissible* if `U(𝒲)` has at most 3 edges at every free
cell. Its *nominal cost* is the pair
`(Σ_pc (|W_pc| − d(p, c)), number of free cells on U(𝒲))`, compared lexicographically.

**Lemma A (path systems).**
(a) If `𝒲` is admissible then `(U(𝒲), S)` is feasible and its cost is at most the
nominal cost of `𝒲`.
(b) For every feasible `(N, S)` there is an admissible `𝒲` for `S` with `U(𝒲) ⊆ N` and
nominal cost at most the cost of `(N, S)`.
Hence the optimum equals the minimum nominal cost of an admissible path system, and
the instance is infeasible iff there is none.

*Proof.* (a) The edges of `U` are grid edges, the degree rule holds by admissibility,
and `W_pc` is a walk in `U` with free interior, so `dist_U(p, c) ≤ |W_pc|`. Network
walks are grid walks, so `dist_U ≥ d` and each excess term is at most `|W_pc| − d`. The
track tiles of `U` are exactly the free cells on the paths.
(b) Let `W_pc` be a shortest valid walk in `N`. It exists because `dist_N(p, c)` is
finite, and it is a simple path. Then `U ⊆ N` inherits the degree rule, the nominal
excess equals the excess of `(N, S)`, and the tiles of `U` are tiles of `N`. ∎

**Lemma B (canonical systems).** In Lemma A(b) the system can be chosen *canonical*:
for any two of its paths, the set of cells they share is the vertex set of a single
common sub-path of both (possibly empty, or a single terminal). The union of a
canonical admissible system has at most `m(m − 1)` free cells of degree 3.

*Proof.* Give the edges of `N` distinct weights `1 + ε_e` with `ε_e > 0` so small and
generic that different edge sets have different total weights and that a shorter walk
is always lighter. Let `W_pc` be the lightest valid walk from `p` to `c` in `N`; it is
a shortest one, and it is unique.
Take two of these paths `W` and `W'` with a common cell. Let `u` and `v` be the first
and the last cell of `W` that lie on `W'`. Write `W[u, v]` and `W'[u, v]` for the
sub-paths between `u` and `v`. Their interior cells are interior cells of `W`,
respectively `W'`, hence free. So replacing `W[u, v]` by `W'[u, v]` inside `W` gives a
valid walk from `p` to `c`: its interior consists of interior cells of `W`, of `u` and
`v` if they are interior to `W`, and of interior cells of `W'[u, v]`, all free. By
minimality of `W`, `W[u, v]` is not heavier than `W'[u, v]`. The symmetric argument
gives the converse, so the two have the same weight, hence the same edge set. So
`W[u, v] = W'[u, v]`, and by the choice of `u` and `v` every common cell lies on it.
For the count, let `x` be a free cell with exactly three edges `a, b, c` of `U`. A free
cell is interior to every path through it, so each such path uses two of the three
edges, and since all three are used there are two paths through `x` that use different
pairs. They share exactly one edge at `x`, so `x` is an end of their common sub-path.
Each of the `m(m−1)/2` pairs of paths has at most two such ends. ∎

**Lemma C (T-orientations).** Let `D` be a set of grid edges, and let `T_D` be the
union, over the ports, of one breadth-first tree of valid walks in `G − D` to the
required cities and to the nearest reachable tied cities. If some port cannot reach
enough cities in `G − D`, no feasible network is contained in `G − D`. If `T_D` obeys
the degree rule, it is feasible. Otherwise `T_D` uses all four edges at some crossroads
`x`, none of these edges is in `D`, and every feasible network contained in `G − D` is
contained in `G − (D ∪ {e})` for one of the four edges `e` at `x`.

*Proof.* A feasible network inside `G − D` connects every port to `k` cities forming a
nearest choice, which is impossible if fewer are reachable in `G − D`. The tree paths
are valid walks, so `T_D` is feasible when it obeys the degree rule. The last claim is
the degree rule at `x`. ∎

Branching on the four edges at `x` is therefore a complete search for feasibility. It
terminates because `D` grows. It can take `4^c` steps, where `c` is the number of
crossroads.

## 3. What bounding the terminals buys

### Theorem 1 (bounded skeleton)

A *skeleton* consists of
- a selection `S`;
- a set `J` of at most `m(m − 1)` free cells (*junctions*);
- a loopless multigraph `K` on the terminals and `J`, with degree at most 3 at every
  junction and at most 4 at every terminal;
- for every chosen pair `(p, c)` a path `π_pc` from `p` to `c` in `K` whose inner
  vertices are junctions.

Give each edge `f` of `K` the weight `w_f` = number of chosen pairs whose `π` uses `f`.
A *realisation* of the skeleton is a family of simple grid paths `Q_f`, one for each
edge `f = ab` of `K`, from `a` to `b`, whose interior cells are free cells outside `J`,
and which are pairwise internally disjoint. Its cost is

    ( Σ_f w_f · |Q_f|  −  Σ_pc d(p, c) ,   |J| + Σ_f (|Q_f| − 1) ).

**Theorem 1.** The instance is feasible iff some skeleton has a realisation. If it is,
the optimum equals the minimum cost of a realisation of a skeleton.

*Proof.* A realisation gives the network `U = ∪ Q_f`. Interior cells have degree 2 and
junctions have degree at most 3, so the degree rule holds. Following `π_pc` gives a
valid walk of length `Σ_{f ∈ π_pc} |Q_f|`, and the free cells of `U` are the junctions
of positive degree and the interiors of the `Q_f`. So `(U, S)` is feasible with cost at
most the cost of the realisation.
Conversely take a canonical optimal system (Lemmas A and B) and let `J` be the free
cells of degree 3 in its union `U`. Every free cell of `U` is interior to some path, so
it has degree 2 or 3. Hence `U` decomposes into paths through degree-2 free cells
joining cells of `T ∪ J`: these are the `Q_f`. None is a closed loop, because each lies
on a simple path `W_pc`. Each `W_pc` is a concatenation of some `Q_f`, which defines
`π_pc`. The cost of this realisation is the nominal cost of the system. ∎

The number of skeletons is at most `2^{400} · (N + 1)^{m(m−1)} · g(m)` for a function
`g` of `m` alone. So the bounded number of terminals reduces the problem to polynomially many
instances of the following problem with a *bounded number of paths*:

> **Routing problem R.** Given the grid with its blocked cells, `L = O(m²)` pairs of
> cells `(a_f, b_f)` (endpoints may coincide between pairs) and positive integer
> weights `w_f ≤ m`: find pairwise internally disjoint paths `Q_f` from `a_f` to `b_f`
> through free cells, minimising `(Σ w_f |Q_f|, Σ |Q_f|)` lexicographically, or report
> that none exist.

### Corollary 2 (feasibility is polynomial, on paper)

For at most 10 ports and 40 cities, whether a feasible solution exists can be decided
in time polynomial in `N`.

*Proof.* By Theorem 1 it suffices to decide, for each of the `N^{O(m²)}` skeletons,
whether a realisation exists. Guess, for every edge `f` of `K`, whether `Q_f` is a
single grid edge, has one interior cell, or else its first and last interior cells
(`O(N²)` choices per edge, in fact at most 16). What remains is to find vertex-disjoint
paths between `L` prescribed pairs of distinct cells in the graph of free cells outside
`J`. This is the disjoint paths problem with a fixed number of pairs, which is solvable
in `O(n³)` time (Robertson and Seymour, *Graph Minors XIII*, 1995). ∎

This corollary is **not** formalised. Formalising it would require a verified
fixed-parameter disjoint-paths algorithm. We know of no elementary polynomial algorithm
for the feasibility question. `network_solver.families.plus_instance` (one port, three
cities) shows that feasibility is a genuine global question: all grid distances are
finite, yet no network exists.

### Corollary 3 (few crossroads)

If the instance has `c` crossroads, the optimum is computable in time
`4^c · N^{O(m²)}`. In particular it is computable in polynomial time, for bounded
terminals, when no free cell has four open neighbours, or more generally when
`c = O(log N)`.

*Proof.* First let `c = 0`. Every network obeys the degree rule, so the network of all
grid edges is feasible whenever a selection exists, and the optimal excess is 0. In a
canonical optimal system every `W_pc` is then a shortest valid walk of the *grid*, so
every segment `Q_f` is a shortest valid path between its ends, of length
`d(a_f, b_f)`. Conversely, for any skeleton with `Σ_{f ∈ π_pc} d(a_f, b_f) = d(p, c)`
for all chosen pairs, the union of *arbitrary* shortest valid paths `Q_f` is a feasible
network of excess 0 with at most `|J| + Σ_f (d(a_f, b_f) − 1)` tiles; disjointness is
not needed. So the optimum is `(0, min |J| + Σ_f (d(a_f, b_f) − 1))` over these
skeletons, and all the distances involved come from `N` breadth-first searches.
For general `c`, a set `D` that contains exactly one grid edge at every crossroads is
called a *complete orientation*; there are at most `4^c`. Every network obeys the
degree rule iff it lies in `G − D` for some complete orientation `D` (§2). For a fixed
`D` repeat the argument above inside `G − D`, with the valid-walk distance `d_D` of
`G − D` in place of `d` for the segments and for the walks, but with the original `d`
in the definition of the selections and of the excess: the least excess of a network
inside `G − D` is `X(D) = min_S Σ_pc (d_D(p, c) − d(p, c))`, attained by `G − D` itself,
and the least tile count among the networks inside `G − D` of excess `X(D)` is found by
enumerating the selections that attain `X(D)` and the skeletons whose segments have
length `d_D`. The optimum is the lexicographic minimum over `D`: an optimal network lies
in some `G − D*`, and then `X(D*)` equals the optimal excess. ∎

Corollary 3 isolates the difficulty. Without the degree rule, bounded terminals do give
polynomial time. With it, the segments of an optimal network are no longer shortest
paths of the grid. They are shortest only among paths that avoid the rest of the
network, and that is problem R. On a map with open regions `c` is of order `N`
(`europe.json` has 1333 crossroads), so the corollary does not help there.

## 4. What it does not buy

### 4.1 Three things that stay unbounded

All three families are in `network_solver/families.py` and are checked by
`tests/test_exact.py` with both solvers.

- **Feasibility is not automatic.** `plus_instance()`: 1 port, 3 cities, `k = 3`.
  Infeasible although every `d(p, c)` is finite.
- **Detours are unbounded.** `ring_instance(n)`: 2 ports, 2 cities, `k = 2`, grid side
  `2n + 5`. The optimal excess is `6n + 6` (checked for `n = 3, 4, 6, 8`).
  `trident_instance(n)`: 1 port, 3 cities, `k = 3`, same map, optimal excess `4n + 2`.
  With a space-filling by-pass instead of a ring the excess would be `Θ(N)`. So no
  corridor of bounded width around the shortest paths contains an optimal network.
- **Networks are large.** `snake_instance(n)`: 1 port, 1 city. The only network has
  `Θ(N)` tiles.

### 4.2 Where the natural proof breaks

The natural argument is: "there are `O(m²)` junctions; guess them; join them by
shortest paths". Theorem 1 makes the first two steps correct. The third is wrong.
In `ring_instance(n)` the optimal network joins a junction on the north arm to a
junction on the south arm by the by-pass, of length about `4n`. The shortest valid path
between these two cells runs through the centre and has length about `2n`. Using it
gives the centre four edges. A segment of an optimal network is a shortest path only in
the grid minus the other segments, and the other segments are `Θ(N)` cells that are not
known in advance.

The same map with one port and three cities (`trident_instance(n)`, optimal excess
`4n + 2`) defeats dynamic programming over "walk trees" with Dreyfus–Wagner style
states `(cell, set of cities)`. Such a relaxation lets a branch walk one step up the
north arm and come back through the centre, which uses the fourth edge at the centre.
It would report excess 2, which no network attains. We did not implement this
relaxation; the value 2 is computed by hand.

### 4.3 Status of problem R

R with all weights 1 is the *shortest disjoint paths* problem (min-sum) with a fixed
number of pairs, on a grid with holes, that is, on an arbitrary planar graph of maximum
degree 4 with subdivided edges. To our knowledge:

- For 2 pairs it is solvable in randomised polynomial time in general undirected graphs
  (Björklund and Husfeldt, *Shortest two disjoint paths in polynomial time*).
- For 3 or more pairs its complexity is open, even on planar graphs. Polynomial
  algorithms are known when the terminals lie on one or two faces (Kobayashi and
  Sommer; Colin de Verdière and Schrijver; Datta et al.).
- On the full grid *without* holes it is fixed-parameter tractable (Mari, Mukherjee,
  Pilipczuk and Sankowski, *Shortest Disjoint Paths on a Grid*, SODA 2024). The
  authors list grids with holes, and a polynomial algorithm for 3 pairs on planar
  graphs, as open.
- If every path must be a shortest path the problem is polynomial for fixed `k`
  (Lochet; Bentert et al.) and fixed-parameter tractable on planar graphs (Pilipczuk,
  Stamoulis and Włodarczyk, 2025). This matches the excess-0 case only.

Sources: [Mari et al., poster with open problems](https://www.lirmm.fr/mathieu-mari/assets/files/posters/HALG24.pdf),
[Mari et al., SODA 2024 (dblp)](https://dblp.org/rec/conf/soda/MariMS24),
[Pilipczuk, Stamoulis, Włodarczyk, arXiv 2505.03353](https://arxiv.org/pdf/2505.03353),
[Borradaile, Nayyeri, Zafarani, arXiv 1507.05980](https://ar5iv.arxiv.org/html/1507.05980),
[Kobayashi and Sommer, METR 2009-38](https://www.keisu.t.u-tokyo.ac.jp/data/2009/METR09-38.pdf).

So the route "Theorem 1, then solve R" needs an algorithm that is not known. We want to
be precise about what this does and does not show:

- It does **not** show that the goal is as hard as shortest disjoint paths. We found no
  reduction from R, or from any problem known to be hard or open, to the Train Network
  Problem with bounded terminals. The obstacle is that a network may carry any number
  of pairs on one edge at no cost, so two paths can never be forced to be disjoint;
  only the union matters. The Train problem might be easier than R.
- It does **not** show NP-hardness. The standard two-path gadget reductions fail for
  the same reason, and the excess-0 case is very likely polynomial.
- It does show that every proof strategy we could think of ends in a shortest-disjoint-
  paths question on a planar graph with holes, where homotopy classes with respect to
  the holes cannot be enumerated and no exchange argument is available.

### 4.4 Why the Lean goal is out of reach even for the parts that are true

`goal_correct` together with `goal_polytime` requires, as a special case, a
polynomial-time decision of feasibility that is verified in Lean. The only algorithm we
know for that (Corollary 2) uses the fixed-parameter disjoint-paths theorem, whose
proof and algorithm are far beyond what we can formalise here.

## 5. What is machine-checked (Lean)

Files: `lean/TrainNetwork/Brute/Basic.lean`, `Dist.lean`, `Solve.lean`, the generated
test file `Brute/CrossCheck.lean`, and the summary `lean/TrainNetwork/Partial.lean`.
They import only the frozen `Problem.lean` (and `Cost.lean` for the summary) and
Mathlib. There is no `sorry`, no `axiom`, no `@[implemented_by]` or `@[extern]`, and
the frozen files are untouched.

**Theorem T0** (`TrainNetwork.Brute.bruteSolve_correct`, restated as
`TrainNetwork.Partial.correct`).

```lean
def bruteSolve (I : Instance) : Option Solution

theorem bruteSolve_correct (I : Instance) :
    match bruteSolve I with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I
```

This is the statement of `goal_correct` with `(Answer.solve I).val` replaced by
`bruteSolve I`, and without the hypotheses on the number of ports and cities.

`bruteSolve` enumerates every subset of the grid edges (each edge in one fixed
orientation) and every assignment of a set of cities to each port, keeps the feasible
candidates, and returns one of minimum cost. Supporting results, all proved:

- `walkDistC_eq`: an executable layered search computes `Instance.walkDist`, the
  `sInf`-based distance of the frozen file, for any decidable relation whose targets
  are in bounds. The proof shows that a walk with a repeated cell can be shortened.
- `feasibleC_iff`, `costC_eq`: executable feasibility test and cost function, equal to
  `Solution.Feasible` and `Solution.cost`.
- `exists_candidate`: every feasible solution has a candidate with the same cost.
- `Partial.feasible_iff`: a feasible solution exists iff the solver returns `some`.

`Brute/CrossCheck.lean` is a test, not a proof. It is generated by
`scripts/lean_crosscheck.py` and contains 24 tiny instances. For each, a `#guard` runs
the verified solver in Lean and compares its `(excess, tiles)` with the optimum found
by the three Python solvers. All 24 agree, including two infeasible instances and one
with optimal excess 4. This ties the Lean reading of `docs/problem.md` to the Python
one that all other experiments use.

`bruteSolve` is a plain function. It is **not** written in `TimeM`, it charges no
ticks, and we make no formal running-time claim for it. Informally it examines
`2^{|E|} · 2^{|C|·|P|}` candidates, where `|E| ≤ 2N` is the number of grid edges. That
is exponential in `N`. It cannot be used as `Answer.solve`.

How to check:

```
cd lean && lake exe cache get && lake build
```

The build prints the axioms of `bruteSolve_correct` and `Partial.correct` (`propext`,
`Classical.choice`, `Quot.sound`) and the warning "GOAL NOT REACHED". `lake build
TrainNetwork.Goal` fails, because `TrainNetwork/Answer.lean` does not exist.

## 6. The exact search algorithm (Python) and its correctness

`network_solver/exact.py`. It does not use CP-SAT.

0. Compute the required and tied cities of each port. If a port reaches fewer than `k`
   cities, report infeasible.
1. *Feasibility.* Search over sets `D` of deleted edges as in Lemma C, starting from
   `D = ∅`. Either some `T_D` obeys the degree rule, which gives a feasible network of
   excess `E0`, or the search ends and the instance is infeasible.
2. *Optimisation.* For `X = 0, 2, 4, …`: for every selection `S`, enumerate by
   depth-first search the path systems for `S`, one pair after the other in a fixed
   order, extending the current path cell by cell. A partial system is abandoned when
   (i) the current path cannot reach its city within the remaining excess `X`, measured
   with the grid distance to the city;
   (ii) a free cell gets a fourth edge;
   (iii) the current path meets an earlier path in a cell after having left that path,
   or moves between two cells of an earlier path along an edge that path does not use;
   (iv) the number of free cells used reaches the best tile count found at this level.
   Stop at the first `X` for which a complete system is found, and return the union of
   the best system found at that level.

**Theorem 4.** The algorithm returns `None` iff the instance is infeasible, and
otherwise an optimal solution.

*Proof.* Step 1 is complete and sound by Lemma C. For step 2, call a system *good at
level `X`* if it is admissible, canonical and of nominal excess at most `X`. No prefix
of a good system is abandoned by (i)–(iii): excesses are non-negative and the remaining
length of a path is at least the grid distance to its city; degrees only grow; and
every sub-family of a canonical system is canonical, which is exactly what (iii) tests
against the earlier paths. Rule (iv) only discards systems that are not better than one
already found. So at level `X` the search finds a good system of minimum tile count if
a good system exists. Let `(X*, K*)` be the optimum. By Lemmas A and B there is a good
system of nominal cost `(X*, K*)`, and no admissible system has smaller nominal cost.
Nominal excesses are even. Hence no level below `X*` finds anything, level `X*` finds a
system with `K*` tiles, and by Lemma A(a) its union is a feasible network of cost at
most `(X*, K*)`. The loop reaches `X*` because `X* ≤ E0`. ∎

**Running time.** Exponential in the worst case, in both steps: step 1 can visit `4^c`
sets, and step 2 enumerates path systems. We have no polynomial bound, and the
measurements below show the blow-up.

`network_solver/brute.py` is the Python mirror of the Lean solver. It follows the Lean
definitions (`IsNearestChoice`, not `requirements`) and is usable up to about 13 grid
edges.

## 7. Experiments

All runs on one 4-core machine, Python 3.13, OR-tools 9.15.

**Agreement with the oracle** (`python -m pytest -q`):

- `tests/test_exact.py`: 296 random instances from `network_solver.generate`, sizes
  3×3 to 10×10, 1–3 ports, 2–7 cities, `k` from 1 to 4, blocked fractions 0 to 0.5.
  142 of the first 224 have blocked cells, 105 have a tie group with a real choice, 38
  have positive optimal excess and 3 are infeasible. `exact` and CP-SAT agree on all of
  them, and so do the hand-built families.
- `tests/test_brute.py`: 42 instances with at most 13 grid edges. `brute`, `exact` and
  CP-SAT agree on all of them.
- `lean/TrainNetwork/Brute/CrossCheck.lean`: 24 tiny instances on which the Lean
  solver, run inside Lean, agrees with the Python solvers (checked at build time).

**Scaling of `exact`.** On 15 random instances of size 10×10 and 12×12 with 4 ports, 8
cities and `k = 4` (16 pairs), 12 finished within 30 s (0.01 s to 11 s) and 3 did not.
CP-SAT needed at most 0.9 s on each. This is the exponential behaviour one expects.

**`data/instances/europe.json`** (49×55, 1546 open cells, 2933 grid edges, 1333
crossroads, 54 chosen pairs). The optimum is excess 2 and 210 tiles.

| Solver | Result | Wall time |
|---|---|---|
| CP-SAT (`python -m network_solver solve`, 4 workers) | run in progress (TBD-CPSAT) | TBD-CPSAT |
| `exact` (`python -m network_solver exact`) | run pending (TBD-EXACT) | TBD-EXACT |
| `brute` / Lean `bruteSolve` | not run: `2^2933` networks | — |

## 8. Differences between the Lean proof and the paper proof

- **Scope.** Lean proves only T0, the correctness of exhaustive search. Lemmas A, B, C,
  Theorem 1, Corollaries 2 and 3 and Theorem 4 are proved on paper only. In particular
  nothing about polynomial time, and nothing that uses the bound on terminals, is
  formalised.
- **No cost model.** The Lean solver is not in `TimeM`. The frozen cost model is not
  used anywhere in our Lean code except that `Partial.lean` imports it.
- **No terminal bound.** T0 holds for all instances; the hypotheses `ports.card ≤ 10`
  and `cities.card ≤ 40` do not appear.
- **Candidates.** Lean enumerates whole assignments port ↦ set of cities.
  `brute.py` minimises over the choice of each port separately. Both range over the
  same candidates and take the same minimum.
- **Distances.** Lean computes distances by layers of exact walk length up to `W·H`.
  Python uses breadth-first search.
- **Nearest choice.** Lean uses `IsNearestChoice` directly. `exact.py` and CP-SAT use
  `requirements` (required cities plus a subset of the tie group). The equivalence of
  the two is not formalised; it is tested by `tests/test_brute.py`.
- **Path systems.** `exact.py` searches canonical path systems (Lemmas A, B). The Lean
  solver searches edge sets and knows nothing about paths.
- **Edge orientation.** A Lean `Solution` is a set of ordered pairs read in both
  directions. The Lean solver only enumerates edges oriented right or down, and the
  proof shows that every feasible solution has such a twin with the same cost. Python
  edges are unordered.

## 9. Reproducing

```
pip install ortools pytest
python -m pytest -q                                          # all cross-checks
python -m network_solver solve data/instances/europe.json    # CP-SAT oracle
python -m network_solver exact data/instances/europe.json --time-limit 3600
cd lean && lake exe cache get && lake build                  # T0; Goal.lean is not built
```
