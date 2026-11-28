# Result: a quasi-polynomial algorithm for few terminals was **not** found

**The goal is not reached.** I did not find an algorithm that solves the Train Network
Problem optimally in time `2^{O(log^d N)}` for at most 10 ports and 40 cities, and I did
not prove that none exists. `lean/TrainNetwork/Goal.lean` does **not** build:
`goal_quasipoly` refers to `Answer.quasipoly`, which does not exist. Acceptance
criterion 1 therefore fails, and nothing in this repository should be read as a proof of
the goal.

This file states what was proved, what blocked the rest, and the strongest partial
results with their exact statements.

## 0. Summary

Throughout, `N = W·H` is the number of grid cells, `|P| ≤ 10`, `|C| ≤ 40`, and
`m = k·|P| ≤ 400` is the number of (port, chosen city) pairs.

| | Statement | Status |
|---|---|---|
| **Goal** | exact algorithm in time `2^{O(log^d N)}` | **not proved, not refuted** |
| A | `Answer.solve` (exhaustive search) returns an optimal solution, or `none` exactly when the instance is infeasible | **machine-checked** (Lean, `Answer.correct`; this is the statement of `Goal.goal_correct`) |
| A′ | `Answer.solve` runs in at most `2^{600·(N+1)}` steps of the frozen cost model | **machine-checked** (`Answer.exp_time`). Exponential, not quasi-polynomial |
| A″ | any candidate list that dominates every feasible solution yields a correct solver; if such lists of small candidates can be generated in quasi-polynomial time and have quasi-polynomial length, both statements of `Goal.lean` follow | **machine-checked** (`solveFrom_correct`, `quasipoly_of_generator`). A reduction of the goal, not a proof: no such generator is known |
| B | Theorem 1: the problem equals a routing problem on `m` simple paths with an additive cost | paper proof (§2) |
| C | Theorem 2: an exact frontier dynamic program running in time `2^{O(m·w·log w)}·N^{O(1)}` per tie choice, `w = min(W,H)`; for bounded terminals this is `2^{O(√N·log N)}` | paper proof (§4), Python implementation tested against CP-SAT. **Subexponential, not quasi-polynomial** |
| D | Theorem 3: some optimal network has at most `m(m−1)` free cells of degree 3; the problem reduces in `N^{O(1)}` time to a routing problem with a fixed pattern | paper proof (§5) |
| E | the residual routing problem contains min-sum disjoint paths with a fixed number of pairs on grid graphs with holes, for which no polynomial or quasi-polynomial algorithm is known | discussion (§6), not a hardness proof |

Exact running times achieved:

- Lean-verified algorithm (A): `2^{O(N)}`; proved bound `2^{600·(N+1)}` ticks.
- Best algorithm with a paper proof (C): `2^{O(m·w·log w)}·N^{O(1)}·2^{|P|·|C|}`, which is
  `2^{O(√N·log N)}` when `|P|` and `|C|` are bounded.

Runtimes on `data/instances/europe.json` (49 × 55, 6 ports, 23 cities, `k = 9`, so
`m = 54`), measured on the 4-core container used for this work: see §8.2. In short,
CP-SAT finds a solution of cost (excess 2, 210 tiles) but does not prove it optimal
within its 600 s limit, and neither of my two algorithms finishes on this instance.

Against the acceptance criteria of the task:

| Criterion | Met? |
|---|---|
| 1. `lake build` succeeds with `Goal.lean` | **No.** It fails at `goal_quasipoly`. `lake build TrainNetwork.Partial` succeeds, with only the three standard axioms and no `sorry` |
| 2. Every claimed algorithm is in `TimeM` and follows the auditing rule | Only Algorithm A (§3.4). Algorithm B is Python and paper only |
| 3. Self-contained proof of the claim in this file | The goal has no proof. The partial statements A–D are proved here or in Lean |
| 4. Python implementation, 200 random instances against CP-SAT, runtime on the real map | Yes for Algorithms A and B (§8), which do not achieve the goal |

## 1. Problem and notation

The problem is the frozen one of `docs/problem.md`. I use the following names.

- `G` is the grid graph on the *open* cells (in bounds, not blocked). A cell is *free*
  if it is open and not a terminal. `T = P ∪ C` are the terminals.
- A walk is *admissible* for a pair `(s, t)` if it goes from `s` to `t` and all its
  interior cells are free. `d(s, t)` is the length of a shortest admissible walk in `G`,
  and `dist_E(s, t)` the same inside an edge set `E ⊆ E(G)`.
- A *selection* `S = (S_p)_{p ∈ P}` gives every port a valid nearest choice of `k`
  cities. Its *demand set* is `D(S) = {(p, c) : c ∈ S_p}`, with `|D(S)| = m = k·|P|`.
- A solution `(E, S)` is feasible if every free cell has at most 3 distinct neighbours
  in `E` and `dist_E(p, c) < ∞` for all `(p, c) ∈ D(S)`. Its cost is the pair
  `(Σ_{(p,c) ∈ D(S)} (dist_E(p,c) − d(p,c)), #free cells touched by E)`, compared
  lexicographically.

## 2. Theorem 1: the routing formulation

A *routing* for a selection `S` is a family `R = (R_j)_{j ∈ D(S)}` where `R_j` is an
admissible walk in `G` for the pair `j`. Let `E(R)` be the set of grid edges traversed
by at least one walk. `R` is *admissible* if every free cell has at most 3 distinct
neighbours in `E(R)`. Its *formal cost* is

    φ(R) = ( Σ_j (|R_j| − d(j)),  #free cells touched by E(R) ).

**Theorem 1.**

1. If `R` is an admissible routing for `S`, then `(E(R), S)` is feasible and
   `cost(E(R), S) ≤ φ(R)`.
2. If `(E, S)` is feasible, there is an admissible routing `R` for `S`, consisting of
   simple paths, with `E(R) ⊆ E` and `φ(R) ≤ cost(E, S)`.

Hence the optimum equals `min_S min_R φ(R)`, the minimum may be restricted to routings
by simple paths, and for a minimising `R` the solution `(E(R), S)` is optimal.

*Proof.* (1) `E(R) ⊆ E(G)` satisfies the degree rule by assumption, and `R_j` is an
admissible walk inside `E(R)`, so `dist_{E(R)}(j) ≤ |R_j| < ∞`. The excess of
`(E(R), S)` is therefore at most the first component of `φ(R)`, and its tile count is
the second component by definition.

(2) For each `j` let `R_j` be a shortest admissible walk for `j` inside `E`. A shortest
walk repeats no cell, so it is a simple path. `E(R) ⊆ E`, so the degree rule still
holds, the first component of `φ(R)` is the excess of `(E, S)`, and the tiles of `E(R)`
are among the tiles of `E`. ∎

The CP-SAT model of `network_solver/cpsat.py` is this formulation (one unit flow per
pair, degree and tile constraints on the union). The cost `φ` is *additive*: it is a sum
over (path, edge) incidences plus a sum over cells. Algorithm B (§4) uses this.

## 3. Algorithm A: exhaustive search (machine-checked)

### 3.1 The algorithm

`Answer.solve` (`lean/TrainNetwork/Timed.lean`, `solveT`) does the following.

1. List the cells of the grid, the ordered pairs `(a, b)` of grid-adjacent open cells
   (the list `ge`, with both orientations of every grid edge), the ports and the cities.
2. For every sublist `E` of `ge` and every association list `ch` that gives each port a
   sublist of the city list, form the candidate `(E, ch)` and test it:
   - every pair of `E` joins two adjacent open cells;
   - every free endpoint of `E` has at most 3 distinct neighbours;
   - for every port `p`, the list `ch(p)` consists of cities, has exactly `k` distinct
     elements, each at finite grid distance from `p`, and no chosen city is farther from
     `p` than an unchosen one;
   - for every port `p`, every city of `ch(p)` is reachable from `p` in `E`.
3. For a feasible candidate compute the cost `(Σ (dist_E − d), #tiles)` in `ℕ × ℕ` and
   keep the lexicographically smallest one (the first such candidate in enumeration
   order).
4. Return the winner as a `Solution`, or `none` if no candidate was feasible.

Distances are computed by a layered search (`distL`): layer 0 is `{s}`; layer `i+1`
consists of the cells adjacent in `E` to a cell `x` of layer `i` such that `i = 0` or
`x` is free; the answer is the index of the first layer containing `t`, among layers
`0, …, 2|E|`, and `⊤` if there is none.

### 3.2 Correctness (`Answer.correct`)

> **Theorem A.** For every instance `I` (no bound on ports or cities is needed),
> `(Answer.solve I).val` is `some σ` with `σ` optimal, or `none` and `I` has no feasible
> solution.

The proof has four parts, which are also the file structure.

1. *Distances* (`Walks.lean`). `t` is in layer `n` iff there is an admissible walk from
   `s` to `t` with exactly `n` steps (`mem_layerL`, by induction on `n`; the step is
   `walkN_succ`). Every walk can be shortened to one that repeats no cell
   (`IsWalk.exists_nodup`), and every cell of a walk with at least one step is an
   endpoint of a pair of `E`, so if `t` is reachable it lies in a layer of index at most
   `2|E|` (`walkN_bound`). Hence the search computes `walkDist`
   (`walkDist_eq_optENat`).
2. *The test and the cost* (`Exec.lean`). The Boolean test holds iff the candidate, read
   as a `Solution`, is `Feasible` (`feasB_iff`), and then the computed pair equals
   `Solution.cost` (`cost_eq`).
3. *The search* (`Search.lean`). On any candidate list the search returns a feasible
   candidate that is at most as expensive as every feasible candidate of the list, and
   `none` iff the list has no feasible candidate (`best_good`). If the list dominates
   every feasible solution (`Complete`), the result meets the specification
   (`solveFrom_correct`). The exhaustive list is complete (`allCands_complete`): for a
   feasible `τ`, the candidate "pairs of `ge` that are in `τ.edges`, and for each port
   the cities that are in `τ.choice p`" has the same edge set as `τ` and the same choice
   at every port, and feasibility and cost depend on nothing else
   (`Solution.feasible_congr`, `Solution.cost_congr`).
4. *The timed program computes the same value* (`Timed.lean`, `solveT_val`).

### 3.3 Running time (`Answer.exp_time`)

> **Theorem A′.** If `|P| ≤ 10` and `|C| ≤ 40`, then
> `(Answer.solve I).time ≤ 2^(600·(W·H + 1))`.

*Proof* (`TimeBound.lean`). Let `n = W·H + 1` and `M = 32n`. There are at most
`2^{|ge|} ≤ 2^{4n}` edge lists and at most `(2^{|C|})^{|P|} ≤ 2^{400}` choice lists.
Every list handled while testing one candidate has length at most `M`, and each timed
function is bounded by a power of `M`: one layer step `≤ M^5`, one distance `≤ M^8`, the
selection test `≤ M^14`, the feasibility test `≤ M^18`, the cost `≤ M^16`, one candidate
`≤ M^19 + 4`. The preprocessing is polynomial in `M` plus `16·2^{|ge|}` for the sublists.
With `M ≤ 2^{n+5}` this gives `time ≤ 2^{23n+501} ≤ 2^{600n}`. ∎

This is exhaustive search, so the bound is exponential. It is **not** the bound of
`Goal.goal_quasipoly`.

### 3.4 Lean files and tick audit

| File | Content |
|---|---|
| `Walks.lean` | walks, layers, `walkDist_eq_optENat` |
| `Exec.lean` | executable test and cost, `feasB_iff`, `cost_eq` |
| `Search.lean` | `best`, `solveFrom_correct`, `allCands_complete`, `solvePure_correct` |
| `Timed.lean` | the `TimeM` program and `…_val` lemmas |
| `TimeBound.lean` | `solveT_time_le` |
| `Answer.lean` | `Answer.solve`, `Answer.correct`, `Answer.exp_time` (no `Answer.quasipoly`) |
| `Reduction.lean` | `solveWith`, `quasipoly_of_generator` (§3.5) |
| `Partial.lean` | the proved statements in the shape of `Goal.lean`, with `#print axioms` |

`lake build TrainNetwork.Partial` succeeds. `#print axioms` on `partial_correct`,
`partial_exp_time`, `partial_reduction` and `partial_goal_of_generator` shows only
`propext`, `Classical.choice`, `Quot.sound`. There is no `sorry`, `admit`, new `axiom`, `@[implemented_by]` or
`@[extern]`, and the frozen files are untouched. `lake build` (which includes
`Goal.lean`) fails with the single error
`Goal.lean:46:2: Unknown identifier 'Answer.quasipoly'`.

Charges, for the auditing rule of `Cost.lean`:

| Operation | Ticks |
|---|---|
| one iteration of `filterT`, `mapT`, `allT`, `foldlT`, `flatMapT`, `appendT`, `lengthT`, `sumT`, `dedupT`, `rangeT` | 3, plus the cost of the applied function (the recursive call, at most one list cell, at most one further operation) |
| one element scanned by `memT c` | `c + 2`; `c = 2` for cells (two comparisons of naturals) |
| `c ∈ I.blocked`, `c ∈ I.ports`, `c ∈ I.cities` | `I.size` each: a linear scan over fewer than `I.size` cells (`card_blocked_lt`, `card_ports_lt`, `card_cities_lt`) |
| `isOpenT`, `isFreeT`, `gridAdjT`, `nbr4T` | `size+2`, `3·size+4`, `2·size+24`, `16` |
| one call of `distT` | 4, plus the membership scan and the layer step |
| one entry scanned by `lookupT` | 4 |
| comparing two costs and allocating the result in `betterT` | 6 |
| building one candidate record | 1 |
| converting the winning edge list to a `Finset` | `|ge|² + 1` (removing duplicates is quadratic; the winner is a sublist of `ge`) |

The `choice` field of the returned solution is a closure and is not evaluated by the
solver.

### 3.5 What the goal reduces to (`quasipoly_of_generator`)

The test, the cost and the search do not depend on how the candidates are produced.
`Reduction.lean` defines `solveWith gen`, which searches the list produced by an
arbitrary timed generator `gen : Instance → TimeM (List Cand)`, and proves:

> **Theorem A″.** Let `gen`, `c₀`, `d₀` be such that for every instance `I` with at
> most 10 ports and 40 cities
> 1. every candidate of `(gen I).val` is small (its edge list and its choice lists have
>    length at most about `32·I.size`; see `Small`),
> 2. `(gen I).val` dominates every feasible solution of `I` (`Complete`),
> 3. `(gen I).time ≤ 2^(c₀·(log₂ I.size + 1)^d₀)` and
>    `(gen I).val.length ≤ 2^(c₀·(log₂ I.size + 1)^d₀)`.
>
> Then `solveWith gen` satisfies both statements of `Goal.lean`: it is correct, and
> `(solveWith gen I).time ≤ 2^((c₀+122)·(log₂ I.size + 1)^(d₀+1))`.

So the goal would follow from such a generator: a quasi-polynomially long list of
networks that is guaranteed to contain an optimal one. Nothing is lost by this
reformulation, since an exact quasi-polynomial algorithm would give the one-element list
containing its answer (this converse is not formalised). The exhaustive generator
satisfies 1 and 2, but its list has length `2^{Θ(N)}`. I do not know a generator
satisfying 3.

## 4. Algorithm B: a frontier dynamic program (paper proof, Python)

Algorithm B is exact and subexponential for bounded terminals. It is implemented in
`network_solver/frontier.py` and has a paper proof only.

### 4.1 The algorithm

Fix a selection `S` with pairs `j = 1, …, m`, `j = (p_j, c_j)`. By Theorem 1 it suffices
to minimise the additive cost `(Σ_j |R_j|, #free cells used)` over admissible routings
by simple paths.

Order the cells `v_1, …, v_N` row by row if `W ≤ H`, and column by column otherwise. Let
`w = min(W, H)`. After step `t` the cells `v_1, …, v_t` are *processed*, and the
*frontier* `F_t` is the set of grid edges with exactly one processed end. `|F_t| ≤ w + 1`.

For a simple path `R_j` and a step `t`, the edges of `R_j` with at least one processed
end form, among the processed cells, a set of disjoint subpaths (*fragments*). Each end
of a fragment is either a frontier edge (a *plug*) or one of `p_j`, `c_j`. The *trace*
of `R_j` at step `t` records which frontier edges are plugs, which two plugs belong to
the same fragment, and which plug belongs to the fragment containing `p_j` (tag `S`) and
which to the one containing `c_j` (tag `T`). A *state* is a tuple of `m` traces. There
are at most `(w + 4)^{w+1}` traces, so at most `(w+4)^{m(w+1)}` states per step.

The transition at cell `v = v_{t+1}` chooses, for every pair `j`, the set of edges of
`v` used by `R_j`, subject to:

- the edges from `v` to processed cells are used by `j` exactly when they are plugs of
  `j`;
- if `v` is blocked, or a terminal other than `p_j` and `c_j`, then `j` uses no edge;
- if `v ∈ {p_j, c_j}`, then `j` uses exactly one edge;
- if `v` is free, then `j` uses 0 or 2 edges, and at most 3 of the 4 edges of `v` are
  used by at least one pair;
- a new edge leads to an open cell that is free or an end of `j`;
- joining two plugs of the same fragment is forbidden (it would close a cycle); when the
  `S` fragment meets the `T` fragment the path is complete and must have no other plug.

The cost of a transition is the number of (pair, new edge) incidences, and one tile if
`v` is free and used. Each state keeps the lexicographically smallest cost. After
`v_N` the frontier is empty, and the state in which every path is complete holds the
optimum for `S`. The algorithm takes the best result over all selections.

### 4.2 Correctness and running time

**Theorem 2.** For a fixed selection `S`, the dynamic program computes
`min_R (Σ_j |R_j|, #free cells used)` over the admissible routings `R` by simple paths,
and reports "none" iff there is none. Its running time is
`(w+4)^{m(w+1)} · 3^m · N^{O(1)} = 2^{O(m·w·log w)} · N^{O(1)}`. Over all selections
the factor is at most `2^{|P|·|C|}`. Hence, for `|P| ≤ 10` and `|C| ≤ 40`, the Train
Network Problem is solved exactly in time `2^{O(√N · log N)}`.

*Proof.* Call a sequence of transitions from the initial state a *run*, and for a run
of length `t` let `F_j` be the set of edges it chose for pair `j`.

*Invariant.* For every run of length `t` ending in state `σ` with cost `(a, b)`:
(i) in `F_j`, every processed free cell has degree 0 or 2, the cells `p_j`, `c_j` have
degree 1 if processed, and every other processed cell has degree 0; (ii) `F_j` contains
no cycle, and the trace of `j` in `σ` describes the components of `F_j` among the
processed cells as stated above; (iii) `a = Σ_j |F_j|` and `b` is the number of
processed free cells used by some `F_j`; (iv) every processed free cell has at most 3
edges in `⋃_j F_j`. Each rule of the transition maintains one of these items; a cycle
could only arise by joining two plugs of one fragment, which is forbidden.

*Runs give routings.* For an accepting run of length `N`, (i) and (ii) say that `F_j`
is a graph without cycles in which `p_j` and `c_j` have degree 1 and all other cells
degree 0 or 2. Such a graph is a single simple path from `p_j` to `c_j`. Its interior
cells are free by (i). By (iv) the routing is admissible, and by (iii) its cost is
`(a, b)`.

*Routings give runs.* Let `R` be an admissible routing by simple paths. The choices
"edges of `R_j` at `v_{t+1}`" satisfy every transition rule: `R_j` uses one edge at its
ends, two at its interior cells, which are free, and none elsewhere; it has no cycle;
and when its two tagged fragments meet, all of `R_j` is processed. The resulting run is
accepting and has the cost of `R`.

Costs add up along runs, and the lexicographic order is compatible with addition, so
keeping the smallest cost per state gives the smallest cost of an accepting run. The
number of states per step is at most `(w+4)^{m(w+1)}` and each has at most `3^m`
transitions, which gives the running time. Finally `w ≤ √N`. ∎

### 4.3 Pruning in the implementation

`frontier.py` restricts the search without changing the result. With a slack `X`:

- **Corridors.** Pair `j` may use a cell `u` only if
  `d(p_j, u) + d(u, c_j) ≤ d(p_j, c_j) + X`. A simple path `R_j` through `u` has length
  at least `d(p_j, u) + d(u, c_j)`, so a routing of total excess at most `X` only uses
  corridor cells.
- **Edge budget.** A state is dropped if its edges so far plus a lower bound on the
  edges every path still needs exceed `Σ_j d(j) + X`. A routing of total excess at most
  `X` never exceeds this budget.
- **Completed paths.** A completed path starts no new fragment. Such a fragment could
  only ever close into a cycle.

So with slack `X` the program finds the best routing among a set of routings that
contains all those of total excess at most `X`. *Certificate:* if the best routing found
has excess `x ≤ X`, it is optimal, because any strictly better routing has excess at
most `x ≤ X` and would have been found. The outer loop starts with a small `X`, and
repeats with `X ← max(2X, x)` (or `2X` if nothing was found) until the certificate
holds. Once `X ≥ W·H` the corridors exclude no simple path. If still nothing is found,
the program runs once more without the edge budget, and reports the instance infeasible
if that also finds nothing. This is the same scheme as in `cpsat.py`. It adds a factor
`O(log N)` to the bound of Theorem 2.

The state space grows with the product of the corridors of all pairs, so the program is
practical only for few pairs on small grids (§8).

## 5. Theorem 3: optimal networks have boundedly many junctions

This section is a paper proof. It is not formalised in Lean and not used by either
algorithm; it is the basis of the discussion in §6.

### 5.1 Consistent shortest paths

Fix an optimal solution `(E*, S*)` and let `D = D(S*)`. Number the edges of `E*` as
`e_1, e_2, …` and put `ω(e_i) = 1 + 2^{-i}`. For a walk `R` let `ω(R)` be the sum of `ω`
over its steps. Then `|R| < ω(R) < |R| + 1` for every walk that repeats no edge, and
two distinct edge sets have distinct `ω`-sums.

For `j ∈ D` let `P_j` be an admissible walk for `j` inside `E*` of minimum `ω`. It
repeats no cell (cutting out a closed part keeps the walk admissible and lowers `ω`),
so it is a simple path, and `|P_j| = dist_{E*}(j)` because a path with fewer edges has
smaller `ω`. It is unique, because two distinct simple paths with the same ends have
distinct edge sets.

**Lemma 5.1.** Let `i ≠ j` and let `u ≠ v` be cells on both `P_i` and `P_j`. Then the
part of `P_i` between `u` and `v` equals the part of `P_j` between `u` and `v`.

*Proof.* Write `A = P_i[u,v]` and `B = P_j[u,v]`. Let `Q` be `P_i` with `A` replaced by
`B`. The interior cells of `Q` are interior cells of `P_i`, or interior cells of `B`
(which are interior cells of `P_j`), so they are free, and `Q` is an admissible walk for
`i` inside `E*`. By minimality `ω(P_i) ≤ ω(Q)`, that is `ω(A) ≤ ω(B)`. By symmetry
`ω(B) ≤ ω(A)`. So `ω(Q) = ω(P_i)`, and by uniqueness `Q = P_i`, that is `A = B`. ∎

**Corollary 5.2.** For `i ≠ j`, the cells common to `P_i` and `P_j` are exactly the
cells of one common subpath `P_i ∩ P_j` (possibly empty, possibly a single cell).

*Proof.* Let `u` and `v` be the first and the last cell of `P_i` that lie on `P_j`. By
Lemma 5.1 the whole of `P_i[u,v]` is a subpath of `P_j`, and by the choice of `u` and
`v` no other cell of `P_i` lies on `P_j`. ∎

### 5.2 Junctions

Let `E′ = ⋃_j E(P_j) ⊆ E*`. Then `(E′, S*)` is feasible, `dist_{E′}(j) = |P_j| =
dist_{E*}(j)` for every `j`, and the tiles of `E′` are among those of `E*`. So
`(E′, S*)` is optimal too. A free cell of degree 3 in `E′` is a *junction*.

**Lemma 5.3.** Every junction is an end of `P_i ∩ P_j` for some `i ≠ j`. So there are
at most `2·C(m, 2) = m(m−1)` junctions.

*Proof.* Let `x` be a junction. A free cell is not an end of any `P_j`, so every `P_j`
through `x` uses exactly two edges at `x`. As `x` has degree 3, two paths `P_i`, `P_j`
through `x` use different pairs of edges at `x`. If `x` were an interior cell of the
common subpath `P_i ∩ P_j`, both would use the two edges of that subpath at `x`. So
`x` is an end of it. Each pair `{i, j}` has at most two such ends. ∎

**Theorem 3.** Every feasible instance has an optimal solution `(E′, S*)` such that

1. `E′` is the union of `m` simple paths `P_j`, `j ∈ D(S*)`, where `P_j` is a shortest
   admissible walk for `j` inside `E′`, and any two of them meet in a common subpath;
2. every free cell touched by `E′` has degree 2 or 3 in `E′`, and at most `m(m−1)` of
   them have degree 3;
3. `E′` is a subdivision of a multigraph `H` whose vertices are the terminals and the
   junctions (at most `|P| + |C| + m(m−1)` vertices and
   `2(|P|+|C|) + 3m(m−1)/2` edges). The edges of `H` correspond to *segments*: grid
   paths through free cells of degree 2, pairwise internally disjoint.

*Proof.* (1) and the bound in (2) are shown above. Every free cell touched by `E′` is an
interior cell of some `P_j`, so its degree is at least 2, and at most 3 by feasibility.
For (3), follow the degree-2 free cells: a maximal chain of them ends at terminals or
junctions, and cannot close into a cycle, because each of its cells lies on a path
`P_j` that ends at terminals. The edge count is half the degree sum
`4(|P|+|C|) + 3m(m−1)`. ∎

### 5.3 Reduction to pattern routing

A *pattern* `Π` consists of a selection `S`; distinct free cells `b_1, …, b_r` with
`r ≤ m(m−1)`; a multigraph `H` on `T ∪ {b_1, …, b_r}` in which every `b_i` has degree
exactly 3; and for every `j = (p, c) ∈ D(S)` a path `ρ_j` in `H` from `p` to `c` whose
interior vertices are among the `b_i`. Put `w(e) = #{j : e ∈ ρ_j}`.

A *realisation* of `Π` gives every edge `e = uv` of `H` a grid path `π_e` from `u` to
`v` whose interior cells are free and are not vertices of `H`, such that the `π_e` are
pairwise internally disjoint and use pairwise distinct sets of grid edges. Its cost is

    ψ(π) = ( Σ_e w(e)·|π_e| − Σ_j d(j),   Σ_e (|π_e| − 1) + r ).

**Proposition 5.4.** The optimum equals the minimum of `ψ(π)` over all patterns `Π` and
all realisations `π` of `Π`. The number of patterns is at most
`2^{|P|·|C|} · (N+1)^{m(m−1)} · c`, where `c` depends only on `m` and `|P| + |C|`.

*Proof.* Given a realisation, let `E = ⋃_e E(π_e)`. A free cell has degree 2 (interior
of some `π_e`), 3 (some `b_i`) or 0 in `E`. For `j ∈ D(S)`, concatenating the `π_e`
along `ρ_j` gives an admissible walk `R_j`, since its interior cells are interior cells
of the `π_e` or cells `b_i`, all free. `Σ_j |R_j| = Σ_e w(e)|π_e|`, and the free cells
touched by `E` are the interior cells of the `π_e` and the `b_i`. By Theorem 1 the
solution `(E, S)` is feasible with cost at most `ψ(π)`. Conversely, the solution of
Theorem 3 is a realisation of the pattern formed by its junctions, its graph `H` and the
routes of the `P_j`, and its cost is `ψ` of that realisation. For the count: at most
`2^{|P||C|}` selections, at most `(N+1)^{m(m−1)}` choices of the cells `b_i`, and
boundedly many graphs and routes on a bounded vertex set. ∎

So, for bounded `|P|` and `|C|`, the Train Network Problem reduces in `N^{O(1)}` time
to `N^{O(1)}` instances of the following problem.

> **Pattern Routing (PR).** Given an instance and a pattern `Π`, find a realisation
> minimising `ψ` lexicographically, or report that there is none.

The weights satisfy `0 ≤ w(e) ≤ m`, so the first component of `ψ` is a weighted sum of
the path lengths with bounded integer weights, and the second is their unweighted sum.

**What PR contains.** If `r = 0`, `H` is a perfect matching on `2q` terminals and all
weights are 1, PR asks for `q` pairwise vertex-disjoint paths of minimum total length
between prescribed pairs of terminals, in the grid graph with holes formed by the free
cells and these terminals. That is the min-sum disjoint paths problem with `q ≤ 25`
pairs on grid graphs with holes.

This is a reduction *from* the Train Network Problem *to* PR. I have **no** reduction in
the other direction, so this is not a hardness result (see §6.2).

## 6. Why the quasi-polynomial goal was not reached

### 6.1 What would suffice

Either of the following would give the goal, and I could prove neither.

- A quasi-polynomial algorithm for PR on patterns of bounded size (by Proposition 5.4).
- A list of candidates of quasi-polynomial size, computable in quasi-polynomial time,
  that dominates every feasible solution (by the machine-checked
  `quasipoly_of_generator`, §3.5).

### 6.2 The obstacle

After Theorem 3, the combinatorial structure of an optimal network is bounded: the
selection, the junctions and the graph `H` can be guessed in polynomial time. What is
left is the *geometry* of the segments: `O(1)` grid paths with prescribed ends that must
stay internally disjoint and minimise a weighted sum of their lengths. Each segment is a
shortest path, but only in the grid *minus the other segments*, so the segments cannot
be chosen one at a time.

This is where the problem meets min-sum disjoint paths. For that problem with a fixed
number `q` of pairs, to my knowledge (literature check on 2026-11-28, references below):

- `q = 2` has a randomised polynomial algorithm on general undirected graphs
  [Björklund–Husfeldt];
- for `q ≥ 3` it is open whether a polynomial algorithm exists, even on planar graphs;
  known planar results need the terminals on one or two faces [Kobayashi–Sommer;
  Colin de Verdière–Schrijver; Borradaile–Nayyeri–Zafarani; Datta et al.];
- on the obstacle-free grid there is an FPT algorithm [Mari–Mukherjee–Pilipczuk–
  Sankowski], which does not cover blocked cells;
- I know of no quasi-polynomial algorithm for `q ≥ 3` on planar graphs or on grids with
  holes.

So the route "guess the pattern, then route it" ends at a problem that is open. The
Train Network Problem might still be easier than PR, because in it paths may merge
freely: two segments that compete for the same cells can share them, which is exactly
what disjoint-paths instances forbid. I could neither turn this freedom into an
algorithm nor show that it does not help. In particular I do **not** claim that the
Train Network Problem with bounded terminals is as hard as min-sum disjoint paths.

### 6.3 Approaches tried, and where each one breaks

1. **Guess the junctions, connect them by arbitrary grid-shortest paths.** This would be
   polynomial. It is wrong: a segment is shortest only in the complement of the other
   segments. In the 7 × 5 instance of
   `tests/test_structure_examples.py::test_segment_need_not_be_a_grid_shortest_path`
   (a plus-shaped corridor system with one bypass), three required connections need all
   four sides of the centre cell. The optimum has cost (8, 16): one port reaches its
   city by a 12-edge bypass although their grid distance is 4, and that segment touches
   nothing else. And when a pair of cells has many shortest paths, the right ones must be
   chosen jointly so that they stay disjoint.
2. **Midpoint recursion on the segments (Savitch).** Splitting each of the `O(1)`
   segments at its midpoint gives twice as many half-segments, which still have to be
   pairwise disjoint. Nothing becomes independent, so after `log N` levels one has
   guessed every cell.
3. **Recursion on balanced separators.** This needs a family of separators of
   quasi-polynomial size such that some optimal network crosses one of them only
   polylogarithmically often. Straight lines do not work: blocked cells can force a
   single connection through a serpentine corridor that crosses the middle column
   `Θ(H)` times. For separators made of shortest paths of the grid, the usual argument
   (two shortest paths meet in an interval) does not apply, because segments are not
   shortest paths of the grid. I found neither a suitable family nor a proof that none
   exists.
4. **Dynamic programming over subsets of pairs or over tokens**, as for Steiner trees
   and directed Steiner networks. These rely on the union of two partial solutions being
   a partial solution. Here the union of two feasible networks can have a free cell of
   degree 4, and this cannot always be repaired: in the 5 × 5 instance of
   `tests/test_network_solver.py::test_crossing_forces_excess` every solution has
   excess at least 2.
5. **A sweep with a frontier.** This works and is exact (Theorem 2, §4), but the
   frontier has `min(W, H)` cells, which gives `2^{O(√N log N)}` and not
   `2^{polylog N}`.

### 6.4 Two observations that may help

**Observation 6.1 (strict pairs do not conflict).** Let `(p_1, c_1)` and `(p_2, c_2)`
be pairs with `d(p_1, c_1) < d(p_1, c_2)` and `d(p_2, c_2) < d(p_2, c_1)`. Then no
shortest admissible walk for `(p_1, c_1)` in the grid shares a free cell with a shortest
admissible walk for `(p_2, c_2)`.

*Proof.* Suppose they share a free cell `z`. Admissible walks can be concatenated at a
free cell, so `d(p_1, c_2) ≤ d(p_1, z) + d(z, c_2)` and
`d(p_2, c_1) ≤ d(p_2, z) + d(z, c_1)`. As `z` lies on shortest walks,
`d(p_1, c_1) = d(p_1, z) + d(z, c_1)` and `d(p_2, c_2) = d(p_2, z) + d(z, c_2)`. Adding,
`d(p_1,c_2) + d(p_2,c_1) ≤ d(p_1,c_1) + d(p_2,c_2)`, which contradicts the two strict
inequalities. ∎

So two pairs can only get in each other's way if `c_2` is at least as close to `p_1` as
`c_1` is (then `p_1` serves `c_2` as well, or `c_2` is in its tie group), or the same
with the roles exchanged. This restricts the patterns but does not bound the work per
pattern.

**Conjecture 6.2 (bounded geodesic decomposition; unproved).** There is a function `f`
such that every feasible instance with `m` pairs has an optimal network that is the
union of at most `f(m)` pairwise internally disjoint paths, each of which is a shortest
admissible walk *of the grid* between its ends.

If this holds, then for bounded terminals the problem is solvable in **polynomial**
time: guess the selection, the at most `2f(m)` ends and the pattern (`N^{O(1)}`
guesses); the cost of a guess is determined by grid distances; and a guess is
realisable iff a certain instance of *Disjoint Shortest Paths* with `f(m)` pairs has a
solution, which is decidable in polynomial time for a fixed number of pairs [Lochet;
on planar graphs, Pilipczuk–Stamoulis–Włodarczyk]. I could not prove the conjecture.
Its content is that a segment is never "pressed" against other segments along a long
stretch that is not shortest in the grid, because merging with them would then be at
least as good. I have no proof and no counterexample, and it is not used anywhere else
in this report.

## 7. Differences between the Lean proof and the paper proofs

1. **Scope.** Lean proves only Theorems A, A′ and A″ (§3). Theorem A″ has no paper
   counterpart other than its statement in §3.5. Theorems 1, 2 and 3,
   Proposition 5.4 and Observation 6.1 have paper proofs only. Algorithm B (§4) exists
   only in Python.
2. **Size parameter.** Lean uses `I.size = W·H + 1`. The bound proved is
   `2^(600·I.size)`; the text writes `N = W·H`.
3. **Search space.** Lean enumerates sublists of the list of *ordered* adjacent pairs
   (both orientations of each grid edge, up to `2^{4N}` lists) and, for each port, *all*
   sublists of the city list. Invalid choices are rejected by the feasibility test.
   The Python mirror `network_solver/exhaustive.py` enumerates unordered edge subsets
   and only valid tie choices, so it tries fewer candidates and returns the same cost.
4. **Distances.** Lean computes each distance by a layered search without a visited
   set, with `2|E|` layers, and recomputes it for every query. Python uses a
   breadth-first search (`verify.check`).
5. **Redundant test.** The Lean feasibility test checks that every pair is
   grid-adjacent, although the exhaustive list guarantees it. This makes
   `solveFrom_correct` hold for arbitrary candidate lists.
6. **Hypotheses.** `Answer.correct` does not use the bounds on ports and cities.
   `Answer.exp_time` uses them (for the factor `2^{400}`); without them Lean proves no
   time bound.
7. **Constants.** The paper says `2^{O(N)}`; Lean proves the explicit, wasteful
   `2^(600·(N+1))`, by bounding every sub-routine by a power of `32(N+1)`.
8. **Cost model conventions.** See the table in §3.4: finset membership is charged
   `I.size`, the final list-to-finset conversion `|ge|² + 1`, and the returned `choice`
   function is a closure that the solver does not evaluate.
9. **Lemmas the paper takes for granted.** Lean proves explicitly that a walk can be
   shortened to one without repeated cells and that reachable cells are found within
   `2|E|` layers; the paper only says "a shortest walk repeats no cell".
10. **Ties between optimal solutions.** Lean returns the first optimal candidate in its
    enumeration order; the paper does not fix which optimum is returned.

## 8. Experiments

All measurements were made in the container used for this work (4 cores, 15 GB RAM,
Python 3.13, OR-Tools 9.15).

### 8.1 Agreement with the CP-SAT oracle

`tests/test_exact_algorithms.py` compares both Python implementations with
`network_solver.cpsat` on instances from `network_solver.generate.random_instance`. For
every instance the test requires the same feasibility verdict, requires CP-SAT to have
proved optimality, runs the solution through `verify.check`, and requires the same cost
`(excess, tiles)`.

| | Frontier (Algorithm B) | Exhaustive (Algorithm A in Python) |
|---|---|---|
| random instances | 504 | 84 |
| grid sizes | 26 different, from 3 × 3 to 12 × 9; 408 instances are at most 6 × 6 | 9 different, at most 16 grid edges |
| with blocked cells | 350 | 24 |
| with a tie at the `k`-th place | 149 | 13 |
| infeasible | 34 | 6 |
| positive optimal excess | 63 (largest 14) | 8 (largest 4) |
| disagreements with CP-SAT | 0 | 0 |

The exhaustive solver is also compared with the frontier solver on its 84 instances.
Hand-written cases cover the 5 × 5 crossing instance (excess 2), a port next to its city
(cost (0, 0)), plus-shaped corridors that are infeasible because the centre would need
degree 4, a tie choice that changes the optimum, and a wide instance that is swept along
its long side. The whole suite (`python -m pytest -q`) has 686 tests and takes about
55 s.

The Lean solver itself is not part of these tests. Its correctness is proved, and it was
run only on the 3 × 1 instance of `Goal.lean` (51 687 ticks).

### 8.2 Runtime on `data/instances/europe.json`

| Solver | Outcome | Time |
|---|---|---|
| CP-SAT, 4 workers, limit 600 s | feasible solution with excess 2 and 210 tiles. **Optimality not proved** (tile lower bound 104) | 600 s (limit reached) |
| CP-SAT, 3 workers, limit 1800 s | CPSAT30_OUTCOME | CPSAT30_TIME |
| Frontier (Algorithm B), `--max-states 2000000` | **did not finish.** Stopped at the state limit in the first round (slack 0, tie choice 1 of 8, 54 paths) at cell 554 of 2695, with 2 000 002 states | 21.3 s until it gave up |
| Exhaustive (Algorithm A) | **not run.** The grid has 2933 edges, so there are `2^2933` networks per tie choice; the program refuses | — |

So neither of my algorithms solves the real map. On it the frontier roughly doubles with
every cell of row 11, because 54 paths with independent positions multiply.

### 8.3 Where the frontier program is practical

Ten random instances per row (seeds 500–509, blocked fraction 0.15), with a limit of
300 000 states. These runs are not part of the test suite.

| Grid | Paths `m` | Finished | Hit the state limit | Longest finished run |
|---|---|---|---|---|
| 20 × 20 | 6 | 7 | 3 | 0.03 s |
| 30 × 30 | 6 | 6 | 4 | 5.7 s |
| 12 × 12 | 9 | 10 | 0 | 1.8 s |
| 20 × 20 | 9 | 6 | 4 | 0.5 s |
| 10 × 10 | 12 | 10 | 0 | 6.5 s |
| 6 × 6 | 15 | 8 | 2 | 7.3 s |

The cost is driven by the number of paths and by how much excess the optimum needs, as
the bound `2^{O(m·w·log w)}` suggests. Proving infeasibility is the worst case, because
it needs a sweep without the edge budget.

## 9. How to check this report

    # Lean: everything that is proved (succeeds)
    cd lean && lake exe cache get && lake build TrainNetwork.Partial

    # Lean: the frozen goal (fails at Goal.lean:46, Answer.quasipoly is not proved)
    cd lean && lake build

    # Python: all tests, including the comparisons with CP-SAT
    python -m pytest -q

    # Python: the two exact algorithms on one instance
    python -m network_solver.exhaustive INSTANCE.json
    python -m network_solver.frontier INSTANCE.json

    # CP-SAT oracle on the real map
    python -m network_solver solve data/instances/europe.json --time-limit 600

## References

Works cited in §6.2 and §6.4. The statements attributed to Bentert et al., Borradaile et
al., Mari et al. and Pilipczuk et al. were checked against the papers' abstracts or text
on 2026-11-28. The other entries are cited from memory and were not re-read.

- A. Björklund, T. Husfeldt. *Shortest two disjoint paths in polynomial time.* ICALP 2014.
- Y. Kobayashi, C. Sommer. *On shortest disjoint paths in planar graphs.* Discrete
  Optimization 7(4), 2010.
- É. Colin de Verdière, A. Schrijver. *Shortest vertex-disjoint two-face paths in planar
  graphs.* ACM Transactions on Algorithms 7(2), 2011.
- G. Borradaile, A. Nayyeri, F. Zafarani. *Towards single face shortest vertex-disjoint
  paths in undirected planar graphs.* ESA 2015. <https://arxiv.org/abs/1507.05980>
- S. Datta, S. Iyer, R. Kulkarni, A. Mukherjee. *Shortest k-disjoint paths via
  determinants.* FSTTCS 2018.
- M. Mari, A. Mukherjee, M. Pilipczuk, P. Sankowski. *Shortest disjoint paths on a grid.*
  SODA 2024. <https://hal-lirmm.ccsd.cnrs.fr/lirmm-04834909v1>
- M. Bentert, F. V. Fomin, P. A. Golovach, T. Korhonen, W. Lochet, F. Panolan,
  M. S. Ramanujan, S. Saurabh, K. Simonov. *Packing short cycles.* 2024.
  <https://arxiv.org/abs/2410.18878>. Its introduction states that for min-sum disjoint
  paths with more than two pairs "the complexity of the problem is a long-standing open
  problem" and that polynomial-time solvability for three pairs "remains open even on
  planar graphs".
- W. Lochet. *A polynomial time algorithm for the k-disjoint shortest paths problem.*
  SODA 2021. <https://arxiv.org/abs/1912.10486>
- M. Pilipczuk, G. Stamoulis, M. Włodarczyk. *Planar disjoint shortest paths is
  fixed-parameter tractable.* 2025. <https://arxiv.org/abs/2505.03353>
