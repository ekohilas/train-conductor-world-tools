# A `2^{O(√N log N)}` algorithm for the Train Network Problem with few ports

**Status: the goal is reached.**

- *Lean.* `cd lean && lake build` succeeds with `Goal.lean` imported; `goal_correct` and
  `goal_subexp` are proved with no axioms beyond `propext`, `Classical.choice` and
  `Quot.sound`, no `sorry`, and no change to the frozen files (section 8).
- *Paper.* Sections 1–7 are a self-contained proof of the same claim; section 10 lists
  every place where it differs from the Lean proof.
- *Python.* `network_solver/layerdp.py` implements the algorithm and agrees with the
  CP-SAT oracle on 431 random instances in the test suite (section 11).

| | |
|---|---|
| Claim | With at most 10 ports and 40 cities, the optimisation problem of `docs/problem.md` is solved exactly in time `2^{o(N)}`. |
| Best bound achieved | `time ≤ C · N^(a + b·min(W, H))` with explicit constants (`C = 2^420`, `a = 60`, `b = 90`), hence **`2^{O(√N · log N)}`**, because `min(W, H) ≤ √N`. Machine-checked as `Answer.solve_time_le`. |
| General form (paper only) | `2^{|P|·|C|} · N^{O(|P| · min(W, H))}` for `|P|` ports and `|C|` cities. |
| Technique | Network distances have *locally checkable certificates* (distance labels with predecessor pointers). Optimising over certificates is a shortest-path problem in a layered graph whose layers are grid columns (or rows), so a layer has at most `√N` cells. |

What is **not** claimed: the algorithm is not practical. The constants are astronomical
(the proved bound `2^420·N^(60 + 90·√N)` drops below `2^N` only for `N` around four million), the verified algorithm
enumerates all candidate layer states densely, and neither it nor the pruned Python
variant finishes on `data/instances/europe.json` (section 11.4). CP-SAT remains the
practical solver (on that instance it finds a verified solution within its 10-minute
limit, without proving it optimal). The result is a worst-case complexity statement.

Throughout, `N` is the Lean input size `Instance.size = W·H + 1` (the frozen
`Cost.lean`); the task statement's `N = W·H` differs by one, which changes nothing.
`M := W·H + 1 = N`, `m := min(W, H)`, `n := max(W, H)`, so `m² ≤ W·H < N`.

## 1. The theorem

**Theorem.** There is an algorithm `solve`, written in the cost model `TimeM` of
`lean/TrainNetwork/Cost.lean`, such that for every instance `I` with at most 10 ports and
at most 40 cities:

1. (*correctness*) `solve I` returns a feasible solution of minimum lexicographic cost
   `(total excess, number of track tiles)`, or `none` if and only if `I` has no feasible
   solution;
2. (*running time*) `time(solve I) ≤ C · N^(a + b·m)` for absolute constants `C, a, b`;
   consequently for every `ε > 0` there is `n₀` with `time(solve I) ≤ 2^{εN}` whenever
   `N ≥ n₀`.

Lean statements (`lean/TrainNetwork/Goal.lean`, frozen):

```lean
theorem goal_correct (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I

theorem goal_subexp :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      n₀ ≤ I.size → ((Answer.solve I).time : ℝ) ≤ (2 : ℝ) ^ (ε * I.size)
```

Part 1 does not use the bounds on ports and cities; only part 2 does.

## 2. Walks

Fix an instance. For a symmetric relation `R` on cells, a *walk* of length `d` from `s`
to `t` is a sequence `s = x₀, x₁, …, x_d = t` with `R(x_{i-1}, x_i)` whose interior cells
`x₁, …, x_{d-1}` are free. `dist_R(s, t)` is the least such `d` (`∞` if none). The grid
distance is `d(p, c) = dist_G(p, c)` for `G` = adjacency between open (in-bounds,
unblocked) cells; the network distance of a network `E` is `dist_E`.

**Lemma 1.** Write `Reach_R(s, d, x)` for "there is a walk of length exactly `d` from `s`
to `x`". Then

- (a) `Reach(s, 0, x)` iff `x = s`; and `Reach(s, d+1, x)` iff there is `y` with
  `Reach(s, d, y)`, `R(y, x)` and (`d = 0` or `y` free).
- (b) `Reach` is monotone in `R`; hence `dist_{R'} ≤ dist_R` when `R ⊆ R'`.
- (c) If `dist_R(s, x) = d + 1` there is `y` with `R(y, x)`, `dist_R(s, y) = d`, and
  `y = s` or `y` free.
- (d) If every `R`-step ends in the grid, `s` is in the grid and `dist_R(s, x) = d` is
  finite, then `d < W·H`.

*Proof.* (a) Split off the last step of the walk; its last-but-one cell is the start
(if `d = 0`) or an interior cell. (b) is immediate from (a). (c) Take a shortest walk and
its last-but-one cell `y`; `dist(s, y) ≤ d`, and a walk to `y` of length `d' < d` could be
extended by the step `y → x` (then `d ≥ 1`, so `y` is free), contradicting minimality.
(d) By (c), descending from `x`, there are cells at each distance `0, 1, …, d`; they are
`d + 1` distinct cells of the grid. ∎

## 3. Certificates

A **run** is given by a list of distinct port cells `p₀, …, p_{q-1}`, for each `j` a
finite set `D_j` of *demand* cells with reference values `g_j(c) ∈ ℕ`, and a degree cap
`β`. Two kinds of run are used:

- *main run* for a choice of cities: all ports of the instance, `D_j` = the cities
  chosen for `p_j`, `g_j(c) = d(p_j, c)`, `β = 3`;
- *distance run* for a pair `(p, c)`: the single port `p`, `D₀ = {c}`, `g₀(c) = 0`, `β = 4`.

Directions are `R, D, L, U` (right, down, left, up), `opp` swaps `R/L` and `D/U`. A cell
is a *source for `j`* if it is `p_j`, and *transit for `j`* if it is free or `p_j`.

A **labelling** `L` assigns to every grid cell `x` four edge bits `e_x(δ)` and, for each
`j < q`, an entry `L_j(x)` that is either `⊥` or a pair `(d, δ)` with `d ∈ ℕ` and `δ` a
direction. `L` is a **certificate** if for every grid cell `x`:

- **(U1)** `e_x(δ)` set ⇒ the `δ`-neighbour of `x` exists and both cells are open;
- **(U2)** `x` free ⇒ at most `β` edge bits are set;
- **(U3)** for each `j`: if `x` is the source for `j` then `L_j(x) = (0, ·)`; otherwise
  `L_j(x) = ⊥` or `L_j(x) = (d, δ)` with `d ≥ 1` and `e_x(δ)` set;
- **(U4)** `x ∈ D_j` ⇒ `L_j(x) ≠ ⊥`;

and for every grid cell `x` and its `δ`-neighbour `y` in the grid, `δ ∈ {R, D}`:

- **(B1)** `e_x(δ) = e_y(opp δ)`;
- **(B2)** if `L_j(x) = (d, δ)` and `x` is not the source for `j`, then `y` is transit for
  `j` and `L_j(y) = (d − 1, ·)`;
- **(B3)** if `L_j(y) = (d, opp δ)` and `y` is not the source for `j`, then `x` is transit
  for `j` and `L_j(x) = (d − 1, ·)`.

The **network** of `L` is `E(L) = {{x, x+R} : e_x(R)} ∪ {{x, x+D} : e_x(D)}`. Its
**cost** is `cost(L) = exc(L)·M + tiles(L)` where

- `exc(L) = Σ_j Σ_{c ∈ D_j, L_j(c) = (d,·)} max(d − g_j(c), 0)`,
- `tiles(L)` = the number of free cells with at least one edge bit set.

All constraints involve one cell or two adjacent cells, and the cost is a sum over cells.

**Lemma 2 (soundness).** Let `L` be a certificate and `E = E(L)`. Then:

1. `E` consists of grid edges between open cells, and `x, y` are adjacent in `E` iff `y`
   is the `δ`-neighbour of `x` and `e_x(δ)` is set, for some `δ`;
2. every free cell has at most `β` neighbours in `E`;
3. if `L_j(x) = (d, ·)` then `Reach_E(p_j, d, x)`; in particular `dist_E(p_j, x) ≤ d`,
   and by (U4) every demand cell is connected to its port;
4. the number of track tiles of `E` is at most `tiles(L)`.

*Proof.* (1) By (B1) the two bits of an edge agree, so the description of adjacency is
symmetric; (U1) makes every set bit a grid edge between open cells. (2) By (1) the
neighbours of `x` are among the `δ`-neighbours with `e_x(δ)` set; apply (U2).
(3) Induction on `d`. If `x = p_j` then `d = 0` by (U3) and the trivial walk works.
Otherwise (U3) gives `d ≥ 1` and a set bit `e_x(δ)`; by (U1) the `δ`-neighbour `y` is in
the grid; by (B2) (or (B3), depending on which of the two cells comes first) `y` is
transit for `j` and `L_j(y) = (d − 1, ·)`. By induction `Reach(p_j, d − 1, y)`. If `y` is
free, Lemma 1(a) extends the walk by the edge `y–x`. If `y = p_j`, (U3) at `y` forces
`d − 1 = 0`, and Lemma 1(a) applies again. (4) A track tile of `E` is a free cell incident
to an edge of `E`, so one of its bits is set by (1). ∎

**Lemma 3 (completeness).** Let `τ` be a set of grid edges between open cells in which
every free cell has at most `β` neighbours, and assume `dist_τ(p_j, c) < ∞` for all
`c ∈ D_j`. Define `L^τ` by: `e_x(δ)` is set iff `x` and its `δ`-neighbour are adjacent in
`τ`; `L^τ_j(x) = ⊥` if `dist_τ(p_j, x) = ∞`, and otherwise
`L^τ_j(x) = (dist_τ(p_j, x), δ)` where, for `x ≠ p_j`, `δ` is the direction of a cell `y`
as in Lemma 1(c) (for `x = p_j` the direction is arbitrary). Then `L^τ` is a certificate,
all its distances are `< W·H`, `tiles(L^τ) ≤` the number of track tiles of `τ`, and
`exc(L^τ) = Σ_j Σ_{c ∈ D_j} max(dist_τ(p_j, c) − g_j(c), 0)`.

*Proof.* (U1), (B1): `τ` is a set of grid edges. (U2): the set bits of a free `x`
correspond injectively to its neighbours in `τ`. (U3): `dist(p_j, p_j) = 0`; for
`x ≠ p_j` with finite distance, the distance is `≥ 1` and the chosen `y` is adjacent to
`x` in `τ`. (U4): the assumption. (B2)/(B3): if `L^τ_j(x) = (d, δ)` with `x ≠ p_j`, the
`δ`-neighbour is the chosen `y`, which has distance `d − 1` and is `p_j` or free, i.e.
transit. The distance bound is Lemma 1(d). A free cell with a set bit is incident to an
edge of `τ`, hence a track tile of `τ`. The formula for `exc` is the definition. ∎

**Corollary 4 (distance runs).** For a port `p` and a grid cell `c`, let `opt` be the
minimum cost of a certificate of the distance run for `(p, c)` with all distances `< M`
(`opt = ∞` if there is none). Then `d(p, c) = ⌊opt / M⌋` (and `d(p, c) = ∞` iff
`opt = ∞`).

*Proof.* Here `exc(L)` is the entry `d` of `c`, and `tiles(L) ≤ W·H < M`, so
`⌊cost(L)/M⌋ = exc(L)`. By Lemma 2(3) and Lemma 1(b) (`E(L) ⊆ G`), every certificate has
`exc(L) ≥ d(p, c)`. Conversely, if `d(p, c) < ∞`, apply Lemma 3 to `τ = G` (all grid
edges; every cell has at most 4 neighbours, so `β = 4` holds): `exc(L^G) = d(p, c)`.
Minimising `cost = exc·M + tiles` minimises `exc` first. ∎

## 4. The layered dynamic programme

**Lemma 5.** Let `k₀, …, k_{n-1}` be layers, `Σ` a finite list of candidate states,
`self(k, s) ∈ ℕ ∪ {⊥}` and `link(k, s, k', s') ∈ {true, false}`. Call an assignment
`s₀, …, s_{n-1} ∈ Σ` *valid* if `self(k_i, s_i) ≠ ⊥` for all `i` and
`link(k_i, s_i, k_{i+1}, s_{i+1})` for all `i < n − 1`; its cost is `Σ_i self(k_i, s_i)`.
A valid assignment of minimum cost (or the fact that none exists) can be computed with
at most `n·|Σ|` evaluations of `self`, `n·|Σ|²` evaluations of `link` and
`O(n·|Σ|²)` further steps.

*Proof.* For `i = n − 1, …, 0` compute a table `T_i` that contains, for every `s ∈ Σ` that
begins some valid assignment of the layers `i, …, n − 1`, the minimum cost of such an
assignment together with a witness. `T_{n-1}` lists the states with
`self(k_{n-1}, s) ≠ ⊥`. Given `T_{i+1}`, the entry of `s` in `T_i` is `self(k_i, s)` plus
the cheapest entry `s'` of `T_{i+1}` with `link(k_i, s, k_{i+1}, s')`, prefixed by `s`.
The invariant "every entry is a valid assignment with its stated cost, and every valid
assignment is dominated by the entry of its first state" is preserved; the answer is the
cheapest entry of `T₀`. ∎

**Application.** Assume first `H ≤ W` (otherwise exchange the roles of rows and columns).
Layer `i` is column `i` of the grid; it has `m = H` cells. A state is a list of `m`
labels. `self` checks (U1)–(U4) for the cells of the column and (B1)–(B3) between
vertically adjacent cells of the column, and returns the sum of the cell costs; `link`
checks (B1)–(B3) between horizontally adjacent cells of two consecutive columns. Valid
assignments are exactly the certificates whose labels come from the candidate label set,
and the cost of an assignment is `cost(L)`.

The candidate label set `Λ_q` consists of all labels with `q` entries whose distances are
`< M`: `|Λ_q| = 16·(4M + 1)^q`. By Lemma 3 and Lemma 1(d) restricting to `Λ_q` loses no
certificate of the form `L^τ`. The candidate states are all `|Λ_q|^m` lists.

## 5. The algorithm

`solve(I)`:

1. List the grid cells; list the ports and the cities by scanning the grid.
2. For every port `p` and city `c`, compute `d(p, c)` by a distance run (Corollary 4
   via Lemma 5).
3. For every port `p`, let `F_p` be the list of cities with finite `d(p, ·)`. Enumerate
   all sub-lists `S` of `F_p` and keep those that pass the test
   "`|S| = k` and for all `c ∈ S`, `c' ∈ F_p`: `c' ∈ S` or `d(p, c) ≤ d(p, c')`". These
   are exactly the valid choices of `p`. Form all combinations (one valid choice per
   port).
4. For every combination run the main run (Lemma 5, all ports, demands = the chosen
   cities with `g = d`, `β = 3`). Keep the combination and labelling of minimum cost.
5. If no run succeeded return `none`. Otherwise return the network `E(L)` of the best
   labelling together with its combination of choices.

## 6. Correctness

*The test of step 3.* A set `S` of cities is a valid choice for `p` (`IsNearestChoice`
in Lean: `k` cities, all reachable, none farther than an unchosen city) iff it is a
sub-list of `F_p` passing the test: unreachable cities are farther than everything, so
only comparisons inside `F_p` matter.

*Soundness of the output.* Let `L` be a certificate of the main run for a combination
`S = (S_p)`. By Lemma 2 the solution `(E(L), S)` is feasible: edges are grid edges,
the degree cap 3 holds, each `S_p` is a valid choice, and every chosen pair is connected.
Moreover `dist_{E(L)}(p_j, c) ≤ d` for the entry `(d, ·)` of a chosen city, so

`excess(E(L), S) = Σ (dist_{E(L)}(p_j, c) − d(p_j, c)) ≤ exc(L)` and `#tiles(E(L)) ≤ tiles(L)`. (★)

*Completeness.* Let `τ` be any feasible solution. Its choices form one of the
combinations of step 3. Lemma 3 (with `β = 3`) gives a certificate `L^τ` of the main run
for that combination, with labels in `Λ_q`, and

`exc(L^τ) ≤ excess(τ)` and `tiles(L^τ) ≤ #tiles(τ)`. (★★)

*Optimality.* If no run succeeds, (★★) shows that no feasible solution exists (and
conversely a successful run yields one). Otherwise let `L` (for `S`) be the labelling
returned in step 4 and `σ = (E(L), S)`. For any feasible `τ`, the run for `τ`'s
combination succeeds with cost at most `cost(L^τ)`, so

`exc(L)·M + tiles(L) = cost(L) ≤ cost(L^τ) = exc(L^τ)·M + tiles(L^τ)`.

Both tile counts are `≤ W·H < M`, hence `exc(L) ≤ exc(L^τ)`, and if these are equal then
`tiles(L) ≤ tiles(L^τ)`. With (★) and (★★):
`excess(σ) ≤ exc(L) ≤ exc(L^τ) ≤ excess(τ)`. If `excess(σ) = excess(τ)` the chain
collapses, so `exc(L) = exc(L^τ)` and
`#tiles(σ) ≤ tiles(L) ≤ tiles(L^τ) ≤ #tiles(τ)`. So `σ` is lexicographically at most `τ`. ∎

Note that no claim "certified cost = true cost" is needed: (★), (★★) and the minimality
of the DP sandwich the true cost of the output.

## 7. Running time

Let `q ≤ |P|` be the number of ports of a run. Per cell, the checks cost `O(q²)` steps
(`O(q)` entries, each found by walking a list of length `≤ q`), so `self` and `link`
cost `O(m·(m + q²))` steps on a layer of `m` cells. The number of candidate states is
`s_q = |Λ_q|^m = (16·(4M + 1)^q)^m`. By Lemma 5 one run costs

`O(n · s_q² · m·(m + q²))` plus `O(m·s_q)` for the enumeration and `O(n·m·N)` for the cell kinds,

i.e. `N^{O(q·m)}`. There are at most `|P|·|C|` distance runs (`q = 1`) and at most
`∏_p 2^{|F_p|} ≤ 2^{|P|·|C|}` main runs (`q = |P|`); steps 1, 3, 5 cost
`O(|P|·2^{|C|}·|C|³ + N²)` and are dominated. Hence

`time(solve) ≤ 2^{|P|·|C|} · N^{O(|P|·m)}`.

With `|P| ≤ 10`, `|C| ≤ 40` and `m ≤ √N` this is `2^{400}·N^{O(√N)} = 2^{O(√N·log N)}`,
which is `2^{o(N)}`: for every `ε > 0`, `C·N^{a + b·√N} ≤ 2^{εN}` once
`log₂C + (a + b·√N)·log₂N ≤ εN`, which holds for all large `N` because
`log N = O(N^{1/4})`. ∎

## 8. The Lean development

All files are under `lean/TrainNetwork/`. `Problem.lean`, `Cost.lean` and `Goal.lean`
are the frozen files and are unchanged.

| File | Content | Main statements |
|---|---|---|
| `Walks.lean` | Lemma 1: walks as an inductive relation `Reach` | `reach_iff_walk`, `walkDist_eq_coe_iff`, `walkDist_mono`, `exists_pred`, `walkDist_lt_cells` |
| `TimeBasic.lean` | timed list combinators (`tmapM`, `tfilterM`, `tsections`, `tsublists`, `tlookup`) | value and time lemmas for each |
| `LayerDP.lean` | Lemma 5: the abstract layered DP | `run_some`, `run_none`, `run_time_le` |
| `Cert.lean` | labels, cell kinds, the timed checks `unaryT`, `pairT`, `cellCostT`, `kindT` | `unaryT_val`, `pairT_val`, `cellCostT_val`, `kindOf_allow`, time lemmas |
| `Sound.lean` | Lemma 2 | `IsCert.netAdj_iff`, `IsCert.deg`, `IsCert.reach`, `IsCert.tiles_le`, `IsCert.excess_le` |
| `Complete.lean` | Lemma 3 | `certLab_ok`, `certLab_range`, `certLab_tiles`, `certLab_excess` |
| `GridDP.lean` | label enumeration, per-layer checks, layer assignments ⇄ labellings | `mem_labsT`, `valid_layOK`, `valid_tab`, `cost_of_valid` |
| `Run.lean` | one DP run on an instance (`dpRun`), both sweep directions | `dpRun_some`, `dpRun_none` |
| `Solve.lean` | the algorithm `Answer.solve` (section 5) | — |
| `Dist.lean` | Corollary 4 | `distT_spec` |
| `Correct.lean` | section 6 | `nearest_of_near`, `near_of_nearest`, `sound_family`, `complete_family`, **`Answer.correct`** |
| `Asymptotics.lean` | `C·N^(a+b·m) ≤ 2^{εN}` for large `N` when `m² ≤ N` | `pow_sqrt_subexp` |
| `TimeBound.lean` | section 7 | `dpRun_time_le`, **`Answer.solve_time_le`**, **`Answer.subexp`** |
| `Answer.lean` | imports the above (the file `Goal.lean` refers to) | — |
| `Examples.lean` | `#guard` tests: `solve` run on five small strips (feasible, infeasible, shared city, adjacent terminals, blocked) | — |

The specification of every `TimeM` program is its `.val`; there are no separate pure
copies of the algorithms, so what is timed is what is proved correct.

To check:

```
cd lean && lake exe cache get && lake build
```

`#print axioms` (run on `goal_correct`, `goal_subexp`, `Answer.solve_time_le`):

```
'TrainNetwork.goal_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TrainNetwork.goal_subexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TrainNetwork.Answer.solve_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#eval (Answer.solve tinyInstance).time` in `Goal.lean` evaluates to `82260`; the
returned network on that 3 × 1 instance is the path `(0,0)–(1,0)–(2,0)`.

## 9. Tick audit

Charging convention (stated at the top of `TimeBasic.lean`): the number passed to
`tick`/`tickN` at the start of a loop body or function is at least the number of
primitive operations the body performs itself: one per pattern match on a list, per
recursive call, per allocated list cell / tuple / record, per `ℕ` arithmetic operation or
comparison, and `i + 1` for a list access at index `i` (lists are linked lists; `getD`
walks). A cell comparison is two `ℕ` comparisons. Operations on values of bounded size
(Booleans, directions, the four edge bits) are free. Functions called from the body
charge for themselves. Library functions whose cost grows with the input are either
re-implemented with explicit recursion or charged with `tickN` at the bound stated
below; these are the places a reviewer has to take on inspection.

| Function (file) | Charge | Pays for |
|---|---|---|
| `tmapM`, `tfilterM` (`TimeBasic`) | 3 per element | match, recursive call, one list cell |
| `tsections` | 2 per list; 1 per produced cell; `|S|·|l| + |S| + 1` | match, recursive call; `a :: s`; `List.flatten` of `|S|` lists of length `|l|` |
| `tsublists` | 2 per element; 1 per produced cell; `|S| + 1` | match, recursive call; `a :: s`; `S ++ S'` (copies `S`) |
| `tlookup` | 4 per visited entry | match, recursive call, cell comparison |
| `bestLink` (`LayerDP`) | 3 per entry, +1 | match, recursive call, result tuple; cost comparison |
| `initT` | 2 per state, +3 | match, recursive call; entry `(s, c, [s]) :: rest` |
| `extendT` | 2 per state, +4 | match, recursive call; `c + c'`, `s :: w'`, entry tuple and cell |
| `tables`, `argminT`, `run` | 1–2 per layer / entry, +1 | match, recursive call; cost comparison |
| `entriesT` (`Cert`) | `2j + 6` at index `j` | recursive call, two list accesses at `j`, two comparisons |
| `unaryT` | `q + 8` | `List.length`, degree (3 additions), one comparison |
| `predsT` | `4j + 10` | recursive call, four list accesses at `j`, two additions, two comparisons |
| `pairT` | `q + 2` | `List.length` |
| `excT`, `cellCostT` | `2j + 6`; `q + 4` | accesses, subtraction, addition; `List.length`, multiplication, addition |
| `ppT` | 8 per port | match, recursive call, two cell comparisons, record, list cell |
| `kindT` | `10·scanCost + 16` | ten `IsOpen`/`IsFree` tests (`decide` on `Finset` membership: a linear scan, 3 steps per element; `scanCost = 3(|B| + |P| + |C|) + 4`), neighbour coordinates |
| `entryListT` (`GridDP`) | `16n + 16` | builds `4n + 1` entries with `List.range`, `map`, `flatMap` |
| `labsT` | `q + 1`; 1 per label; `17·|dss| + 1` | `List.replicate`; label record; `List.flatten` of `|dss|` lists of length 16 |
| `colSelfT` | `4j + 14` at cell `j` | recursive call, accesses `ks[j]`, `as[j]`, `ks[j+1]`, `as[j+1]`, additions, comparison |
| `colLinkT` | `4j + 8` | recursive call, four accesses at `j` |
| `gSelf`, `gLink` | `m + 1` | `List.length` |
| `dpRun` (`Run`) | `q + 6`; `m + 1`; `n + m + 2`; 1 per cell | length of the port list, comparison, `W·H + 1`; `List.replicate`; two `List.range`; the pair built by `emb` |
| `cellsT` (`Solve`) | `W + H + 2`; 1 per cell; `W·H + W + 3` | two `List.range`; pair; `List.flatten` |
| `scanT` | `3·|s| + 1` per cell | `decide (x ∈ s)` on a `Finset`: linear scan |
| `distT` | 4 + 4 | port/demand list; `W·H + 1`, division, result |
| `distsT` | 1 per city; `2·|cities| + 1` | pair; `List.filterMap` |
| `nearRowT`, `nearAllT`, `nearT` | `4·|S| + 4`; 2; `|S| + 2` | match, recursive call, `decide (e' ∈ S)` on a list of pairs (4 steps per element), comparison; `List.length` |
| `choicesT`, `bestT` | 1 per choice; 3 (+1) per combination | pair; match, recursive call, result tuple, cost comparison |
| `edgesT` | 1; `x.1 + x.2 + 16` per cell; `3·|cells| + 1` | comparison; label lookup (two list accesses), coordinates, at most six allocations, append; `List.flatten` |
| `choiceTableT`, `solve` | `2ℓ² + 2ℓ + 2`; `4·|es|² + |es| + 2` | `List.map` and `List.toFinset` (duplicate removal compares each pair at most once) |

The returned `Solution` contains a function `choice : Cell → Finset Cell`; `solve`
returns a closure that looks the port up in the table built by `choiceTableT`. Building
the closure is `O(1)`; evaluating it later is not part of `solve`'s running time.

## 10. Where the Lean proof and the paper proof differ

1. **Input size.** Lean uses `Instance.size = W·H + 1` (frozen `Cost.lean`), the paper
   text `N = W·H` in the problem statement. This document uses the Lean `N` throughout.
2. **Walks.** The frozen definition uses lists of cells (`IsWalk`). Lean first proves the
   equivalence with the inductive relation `Reach` (Lemma 1(a), `reach_iff_walk`) and
   never touches lists again.
3. **Grid distances by DP, not BFS.** Both the paper and Lean compute `d(p, c)` with a
   distance run (Corollary 4). A breadth-first search would be the natural choice and is
   what the Python code uses; the DP was chosen in Lean because its correctness follows
   from the same two lemmas. This does not affect the bound.
4. **Labels.** In Lean a label holds a *list* of entries; an index beyond the end of the
   list reads as `⊥`. Candidate labels have exactly `q` entries with distances `< M`
   (the paper needs only `< W·H`); Lean bounds their number by `16·(4M + 2)^q` instead of
   the exact `16·(4M + 1)^q`.
5. **Layer states and tables.** Lean enumerates all `|Λ|^m` lists of labels as candidate
   states for every layer (`List.sections`), and each table entry carries its witness
   (the list of states of the remaining layers). The paper does not fix these details.
6. **Sweep direction.** The paper says "assume `H ≤ W`". Lean treats both directions in
   one proof through the coordinate map `emb` (`Run.lean`), without transposing the
   instance.
7. **Cost.** Lean's DP minimises the single number `exc·M + tiles`; the lexicographic
   comparison of the frozen `Solution.cost` is derived at the very end (`Answer.correct`)
   exactly as in section 6.
8. **Lemma 3.** The paper states equalities for `exc(L^τ)` and the distance bound
   `< W·H`; Lean proves only the inequalities that are used (`certLab_excess`:
   `exc(L^τ) ≤ excess(τ)`; `certLab_tiles`; `certLab_range`). Subtractions `d − g` are
   truncated in both.
9. **Choices.** Lean enumerates all `2^{|F_p|}` sub-lists of the reachable cities and
   filters them with the test of step 3; it does not compute the threshold `t_p` or the
   tie group explicitly. The choice returned for a cell that is not a port is `∅`.
10. **Port order.** The paper takes the ports in any fixed order; Lean takes them in grid
    order (column by column), as produced by scanning the grid.
11. **Running time.** The paper gives `2^{|P||C|}·N^{O(|P|·m)}` for general `|P|`, `|C|`.
    Lean proves the bound only for `|P| ≤ 10`, `|C| ≤ 40`, with the explicit constants of
    `Answer.solve_time_le` (`C = 2^420`, `a = 60`, `b = 90`); these constants are deliberately generous and
    far from tight. The step from this bound to `2^{εN}` is `pow_sqrt_subexp`.
12. **Cost model.** The paper counts elementary steps informally. Lean counts `tick`s
    under the convention of section 9; in particular list accesses are charged linearly
    (no arrays are used), which costs polynomial factors only.
13. **Correctness needs no bounds.** `Answer.correct` holds for every instance; the
    hypotheses `|P| ≤ 10`, `|C| ≤ 40` of `goal_correct` are not used.
14. **Python.** The Python implementation (section 11) is not what is verified: its
    `verbatim` mode follows the certificate system above but generates layer states by
    search instead of dense enumeration, and its default `pruned` mode restricts the DP
    to canonical certificates. Its correctness rests on the arguments of section 11 and
    on testing, not on Lean.

## 11. Python implementation and experiments

Nothing in this section is machine-checked. The Lean theorems are about `Answer.solve`
of section 5; the Python code is a separate implementation of the same optimisation
over certificates, validated by testing against the CP-SAT oracle.

### 11.1 `network_solver/layerdp.py`

`solve(instance, mode=...)` (CLI: `python -m network_solver solve-dp INSTANCE`). Every
returned solution is checked with `network_solver.verify.check`, and the code asserts
that its verified cost equals the cost the DP computed.

- **`mode="verbatim"`** is the certificate system of section 3 and the layered DP of
  section 4, with no additional constraint. It differs from the Lean algorithm only in
  how the same quantities are computed: grid distances by BFS; choices as "required
  cities plus a subset of the tie group"; the self-valid states of a layer are generated
  by backtracking instead of enumerating all `|Λ|^m` lists and filtering; the minimum over
  the next table is taken over projections of states. It finishes only on tiny inputs
  (strips up to 11 × 1 with two ports, 3 × 3 with one port).
- **`mode="pruned"`** (default) optimises over *canonical* certificates only, processes
  the grid one cell at a time (a broken-profile version of the layer-to-layer step, with
  layers of `min(W, H)` cells), keeps a "predecessor still needed" flag instead of
  enumerating predecessor directions, and uses iterative deepening on an excess budget.

### 11.2 Why pruned mode is exact (paper argument)

*Canonical certificate.* Let `τ` be an optimal solution. For each port `p_j` take the BFS
tree of `τ` in which the parent of a cell is its first neighbour (in the order
`L, U, D, R`) that is joined to it in `τ`, is transit for `j`, and is one step closer to
`p_j`. Let `S_j` be the union of the tree paths from `p_j` to its chosen cities and
`N' = ⋃_j S_j`. Then `N' ⊆ τ` (degree caps hold, no more tiles) and the tree paths are
shortest in `τ`, so the chosen pairs have the same distances in `N'` as in `τ`: `N'` is
optimal too. Label `x ∈ S_j` with `(dist_τ(p_j, x), direction of its parent)` and all
other cells with `⊥` for `j`. This is a certificate for `N'` whose cost is the cost of
`N'`.

Every rule below is satisfied by the canonical certificate of an optimal solution, and
rules only remove certificates. So the pruned optimum is the cost of a genuine
certificate (hence `≥` the true optimum by Lemma 2) and `≤` the cost of the canonical
certificate (the true optimum). `g_j(x)` is the grid distance from `p_j` to `x`, and
`h(x, c)` the grid distance from `x` to `c`.

| Rule | Statement | Why the canonical certificate satisfies it |
|---|---|---|
| P1 corridor, budget `X` | an entry `d` of port `j` at `x` has `g_j(x) ≤ d ≤ max_c (d(p_j, c) + X − h(x, c))` over the chosen cities `c` of `j` (for a city cell: its own bound only) | `x` lies on the tree path to some chosen `c`, so `d + h(x, c) ≤ dist_τ(p_j, c) ≤ d(p_j, c) + X` whenever the total excess is `≤ X` |
| P2 Lipschitz | on a network edge `x–y` with both cells labelled for `j` and `x` transit: `d_j(y) ≤ d_j(x) + 1` | labels are exact distances in `τ` |
| P3 successor | a free cell labelled for `j` is the parent, for `j`, of one of its network neighbours | a free cell of `S_j` is interior to a tree path |
| P4 no junk | a cell with an edge bit has an entry; a city has an entry for `j` only if chosen for `j`; a port only for itself; every network edge joins a cell to its parent for some port | `N'` is the union of the trees `S_j`, whose leaves are chosen cities |
| P5 | a free cell with an edge bit has at least two | same |
| P6 excess cap | in a run with budget `X`, partial certificates with accumulated excess `> X` are dropped | excess terms are non-negative |
| P7 incumbent | partial certificates already at least as expensive as the best complete certificate of an earlier choice combination are dropped | costs only grow |
| P8 budget split | `Σ_j max_x η_j(x) ≤ X` over the frontier cells, where `η_j(x) = min_c (d + h(x, c) − d(p_j, c))` | the path through `x` has excess `≥ η_j(x)`, and different ports give different pairs |
| P9, P10 counting | per port: the number of frontier cells that still owe a child is at most the number of unprocessed chosen cities plus the number of frontier cells still lacking a parent, and symmetrically | injections along the tree `S_j` (spelled out in the module docstring) |

*Iterative deepening.* The run with budget `X` (for `X = 0, 2, 4, 8, …`, over all choice
combinations) is accepted if it returns a certificate of excess `≤ X`: then the optimal
excess is `≤ X`, the canonical certificate of an optimal solution passes P1, P6 and P8,
and the run's optimum is the global optimum. The last run, with `X ≥ W·H`, drops P6 and
P8; its corridor contains the canonical certificate of every feasible solution
(distances are `< W·H`), so if it finds nothing the instance is infeasible.

The full statements, including the lazy handling of predecessor directions, are in the
docstring of `network_solver/layerdp.py`.

### 11.3 Agreement with the CP-SAT oracle

`tests/test_layerdp.py`, run by `python -m pytest -q` (**509 tests pass in 66 s, 490 of them in this file**):

- **Pruned mode vs CP-SAT on 431 random instances** from `network_solver.generate`
  (the oracle must report a proven optimum or infeasibility). 24 grid shapes from 3 × 3 to
  16 × 12 (9 to 192 cells), including 9 × 1 and 1 × 9 strips; 1–3 ports, 2–5 cities, every
  `k`, blocked fraction 0, 0.1, 0.2, 0.3. Of these, 256 have blocked cells, 92 have a
  non-trivial tie group (more than one choice combination), 6 are infeasible, 33 have a
  positive optimal excess and 144 are taller than wide. The full lexicographic cost is
  compared, and the DP's solution is checked by the independent verifier. A summary test
  asserts these counts.
- **Verbatim mode vs pruned mode vs brute force** (enumeration of all edge subsets) on
  44 tiny random instances and two hand-made 3 × 3 cases, one of them infeasible.
- **Hand-made cases**: the plus-shaped crossing (excess 2); the same crossing inside
  width-1 cloud corridors (infeasible); a port adjacent to its city (cost `(0, 0)`); tie
  groups where the choice changes the cost; a port that reaches fewer than `k` cities;
  transposed instances; the time and memory guards; the CLI.

Two restrictions of the random test set, both because pruned mode is slow when it has to
go to a large budget (many pairs on few cells, or infeasibility): the generator does not
produce instances with `ports·k ≥ 12` on grids of at least 16 cells or `ports·k ≥ 9` on
grids of more than 60 cells, and one generated instance is excluded by hand (7 × 3,
infeasible, 9 pairs: CP-SAT refutes it at once, the DP needs more than 8 million states
for its final run).

An independent fuzz with other seeds, run once for this report and not part of the test
suite (18 shapes from 3 × 3 to 12 × 8 plus strips, same parameter ranges): of 300 generated
cases, 13 had no instance in which every port reaches `k` cities, 1 hit the DP's guard
(15 s / 2 million table entries) and was not compared, and the remaining 286 all agree
with CP-SAT (181 with blocked cells, 64 with a non-trivial tie group, 2 infeasible, 20
with positive optimal excess).

### 11.4 Runtime on `data/instances/europe.json`

49 × 55 grid, 6 ports, 23 cities, `k = 9`, 1149 blocked cells, 8 choice combinations.
Measured on the 4-core machine of this session.

| Solver | Result | Time |
|---|---|---|
| CP-SAT (`python -m network_solver solve`, default 600 s limit, 8 workers) | feasible, **not proven optimal**: excess 2, 210 tiles (tile lower bound 207); accepted by the verifier | 600 s (time limit reached) |
| Layered DP, pruned mode (`python -m network_solver.bench_layerdp europe`, limits: 1800 s, 5 million table entries, 8 GB) | **no result**: stopped by the table-size guard in the `X = 0` run of the first choice combination, in row 12 of 55 (cell 20 of 49); the table had reached 5,000,057 states, after 409,277 at the end of row 11 | 40 s until the guard fired |
| Layered DP, verbatim mode / the verified `Answer.solve` | not attempted: a single layer has `(16·(4·2696 + 1)^6)^49` candidate states | — |

So the DP does not solve the real map, and nothing in this work suggests it could with
more time: the frontier table grows by three orders of magnitude within one row. On this
instance CP-SAT is the only method here that produces a solution.

### 11.5 Where pruned mode does work

`python -m network_solver.bench_layerdp scaling` (random instances, 10 seeds per size,
10 s and 3 million table entries per instance, 3 parallel workers):

| Grid | 2 ports, 4 cities, `k = 2`, 10 % blocked | 3 ports, 5 cities, `k = 3`, 10 % blocked | 4 ports, 8 cities, `k = 4`, 20 % blocked |
|---|---|---|---|
| 6 × 6 | 10/10 | 10/10 | 3/10 |
| 8 × 8 | 10/10 | 10/10 | 6/10 |
| 10 × 10 | 10/10 | 10/10 | 8/10 |
| 15 × 15 | 10/10 | 9/10 | 5/10 |
| 20 × 15 | 10/10 | 10/10 | 8/10 |
| 20 × 20 | 10/10 | 9/10 | 6/10 |
| 30 × 20 | 10/10 | 9/10 | 8/10 |
| 30 × 30 | 10/10 | 8/10 | 9/10 |
| 40 × 30 | 10/10 | 5/10 | 8/10 |
| 40 × 40 | 10/10 | 3/10 | 1/10 |
| 50 × 50 | 9/10 | 6/10 | 3/10 |

(Entries: instances finished within the limits, out of 10. In the first column the
slowest finished instance took 0.8 s; in the other two the median of the finished
instances stays below 6 s and the largest table had about 1.3 million entries.)

Runtime is heavy-tailed. Pruned mode is fast when the optimal excess is small and the
shortest-path corridors are narrow, and it degrades sharply with the budget `X` it needs;
proving infeasibility needs the final run and is slow beyond about 20 cells with many
pairs. Verbatim mode: 11 × 1 with two ports within 1 s, 3 × 3 with one port within 4 s,
3 × 2 with two ports 1–8 s, 4 × 2 with two ports over two minutes.

## 12. Summary of what is and is not established

- **Machine-checked** (Lean, section 8): `Answer.solve` is correct on every instance and
  runs in time `2^420 · N^(60 + 90·min(W, H)) = 2^{O(√N log N)}` when there are at most 10
  ports and 40 cities; hence the frozen goal `2^{o(N)}`.
- **Paper proof** (sections 2–7): the same, plus the general bound
  `2^{|P||C|} · N^{O(|P|·min(W, H))}`.
- **Tested, not proved**: the Python implementation; in particular the pruning rules of
  section 11.2 rest on the arguments given there and on agreement with CP-SAT.
- **Not achieved / not claimed**: a practical algorithm. The DP does not finish on
  `europe.json`; the verified algorithm only runs on strips of a few cells; the constants
  in the bound are far from tight. Whether the problem with a bounded number of ports is
  solvable in time `2^{O(√N)}` or even polynomial time is left open here.
