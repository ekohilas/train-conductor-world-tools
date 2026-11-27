# The complexity of the Train Network Problem

## 0. Status: the goal is only half reached

**The goal of `lean/TrainNetwork/Goal.lean` is not reached.** That file asks for
polynomial-time many-one reductions in *both* directions between the decision version of
the Train Network Problem (`Decide I X K`, docs/problem.md) and a known problem, both
machine-checked. Only one direction is machine-checked here.

| Claim | Lean | Paper | Tests |
|---|---|---|---|
| Train ≤ₚ SAT (`toK`, `to_correct`, `to_poly`) | **proved**, standard axioms only | §4 | 210 random instances vs CP-SAT |
| SAT ≤ₚ Train (`fromK`, `from_correct`, `from_poly`) | **not proved, not even stated as code** | follows from §6 and the literature | — |
| Rectilinear Steiner Tree ≤ₚ Train (the new step of the hardness direction) | not formalised | §6 | 300 random point sets |

Consequences for the acceptance criteria:

1. `cd lean && lake build` succeeds, but **`Goal.lean` is not imported** by
   `lean/TrainNetwork.lean`, because `Answer.fromK`, `Answer.from_correct` and
   `Answer.from_poly` do not exist. Importing it makes the build fail. The forward half
   of `Goal.lean` (`goal_to_correct`, `goal_to_poly`) is restated verbatim and proved in
   `lean/TrainNetwork/GoalForward.lean`; `#print axioms` gives `propext`,
   `Classical.choice`, `Quot.sound` for both. No frozen file was edited.
2. The forward reduction is written in `TimeM` and every charge is documented (§5.2).
3. This file contains the paper proofs. The hardness direction is a paper proof only.
4. Python implementations and tests exist for both directions that were worked out (§7).

What the results say about the problem: **the decision version of the Train Network
Problem is NP-complete**, hence polynomial-time equivalent to SAT. Membership in NP is
machine-checked (it is the forward reduction). NP-hardness is proved on paper in §6, by a
reduction from the Rectilinear Steiner Tree problem, and it depends on one fact from the
literature that I could not re-read in this session (§6.1). §8 says what blocked the
Lean proof of the backward direction.

## 1. The known problem

**SATISFIABILITY (SAT).** *Instance:* a set `U` of variables and a collection `C` of
clauses over `U`. *Question:* is there a truth assignment for `U` that satisfies every
clause of `C`?

* Definition and NP-completeness: S. A. Cook, *The complexity of theorem-proving
  procedures*, Proc. 3rd ACM STOC (1971), 151–158. Cook proves that every problem in NP
  reduces to the satisfiability of propositional formulas (stated for tautologies of
  DNF formulas).
* The clause form above, and its NP-completeness under many-one reductions: R. M. Karp,
  *Reducibility among combinatorial problems*, in *Complexity of Computer Computations*
  (1972), 85–103, problem SATISFIABILITY. It is problem [LO1] in M. R. Garey and
  D. S. Johnson, *Computers and Intractability* (1979), which is the wording used above.

SAT is a genuinely different problem from the Train Network Problem: it has no grid, no
distances and no optimisation.

### 1.1 The Lean definition, symbol by symbol (`lean/TrainNetwork/Sat.lean`)

| Published definition | Lean |
|---|---|
| variable `u ∈ U` | a natural number (its index) |
| literal `u` or `ū` | `Lit := ℕ × Bool`; `(u, true)` is `u`, `(u, false)` is `ū` |
| clause: a set of literals, read as a disjunction | `Clause := List Lit` |
| collection `C` of clauses | `KInstance`, a structure with one field `clauses : List Clause` |
| truth assignment `t : U → {T, F}` | `a : ℕ → Bool` |
| literal true under `t` | `LTrue a l := a l.1 = l.2` |
| clause satisfied: some literal true | `CTrue a c := ∃ l ∈ c, LTrue a l` |
| `t` satisfies `C` | `Sat a φ := ∀ c ∈ φ, CTrue a c` |
| "is `C` satisfiable?" | `KYes φ := ∃ a, Sat a φ.clauses` |

`U` is not stored: it is the set of indices that occur. A list may repeat a literal or a
clause, which does not change satisfiability. The empty clause is unsatisfiable and the
empty formula is satisfiable, as in the published definition.

**Size.** `KInstance.size φ = Σ_{c ∈ φ} (1 + Σ_{l ∈ c} (1 + Nat.size l.1))`, where
`Nat.size n` is the number of binary digits of `n`. This is the length of the usual
encoding (a separator per clause, a sign and a binary index per literal) up to a constant
factor. Variable indices are counted in binary, so the measure is not inflated.

## 2. The Train Network Problem, in the form used below

Notation follows docs/problem.md and `Problem.lean`. `N = W·H` is the number of cells,
`P` the ports, `C` the cities, `d(p, c)` the grid distance (`gridDist`), `dist_N` the
network distance (`netDist`). `Decide I X K` holds iff some feasible solution has total
excess `≤ X` and at most `K` track tiles. The input size is `n = N + 1 + X + K`
(`I.size + X + K`), with `X` and `K` in unary, as in `Goal.lean`.

## 3. Theorems

**Theorem 1 (machine-checked).** There is a function `toK` computable in time polynomial
in `n` such that for every instance `I` and all `X, K`:
`Decide I X K` holds iff the CNF formula `toK I X K` is satisfiable. The formula has
`O(|P|·N² + |P|·|C|²·N + |P|·|C|·N·X + N·K)` clauses of at most 6 literals.

Lean: `TrainNetwork.Answer.to_correct`, `TrainNetwork.Answer.to_poly`, and the explicit
bound `toK_time_le : (toK I X K).time ≤ 200000000 * (I.size + X + K)^7`.

**Corollary 2.** The decision version of the Train Network Problem is in NP.

**Theorem 3 (paper proof, §6).** RECTILINEAR STEINER TREE with coordinates bounded by a
polynomial in the number of points reduces in polynomial time to the decision version of
the Train Network Problem. The produced instances have one port, no blocked cells,
`k = |C|`, and an excess bound that never binds.

**Corollary 4 (conditional on §6.1).** The decision version of the Train Network Problem
is NP-complete, and therefore polynomial-time many-one equivalent to SAT. It stays
NP-hard for one port, no clouds and `k = |C|`.

## 4. The reduction Train → SAT

### 4.1 Three lemmas

Fix a relation `R` on cells and a start cell `s`. Call a walk *admissible* if all its
intermediate cells are free (this is `IsWalk`).

**Lemma A (layered reachability; `Reach.lean`: `reach_iff_walk`, `walkDist_le_iff`).**
Define `reach_0(v) :⇔ v = s` and
`reach_{t+1}(v) :⇔ reach_t(v) ∨ ∃u. reach_t(u) ∧ (u = s ∨ u free) ∧ R u v`.
Then `reach_t(v)` iff there is an admissible walk from `s` to `v` of length `≤ t`, i.e.
iff `walkDist R s v ≤ t`.

*Proof.* A walk is `[s]` or `s :: m ++ [v]` with all of `m` free. (⇒) by induction on
`t`: extend a walk to `u` by the step `u → v`; if `u = s` use the walk `[s, v]` instead,
so that `s` never becomes an intermediate cell. (⇐) by induction on the walk from its
end: the last step leaves a cell `u` that is `s` or an intermediate, hence free, cell. ∎

**Lemma B (horizon; `reach_horizon`).** If `s` is in the grid and `R u v` implies that
`v` is in the grid, then `reach_t(v)` for some `t` implies `reach_{W·H}(v)`.

*Proof.* The sets `L_t = {v in the grid : reach_t(v)}` grow with `t`, and
`L_t = L_{t+1}` implies `L_{t+1} = L_{t+2}` because `L_{t+1}` is a function of `L_t`.
While the sequence is strictly growing, `|L_t| ≥ t + 1`. There are `W·H` cells, so it is
constant from `t = W·H` on. ∎

**Lemma C (sequential counter; `Sat.lean`: `atMost_sound`, `atMost_complete`).** Let
`it_0, …, it_{M-1}` be *items*, each a conjunction of literals, and `B ≥ 0`. With fresh
variables `s(i, j)`, `0 ≤ i ≤ M`, `0 ≤ j ≤ B`, let `atMost(B, items)` consist of, for
every `i < M` and `j ≤ B`,

* `¬s(i, j) ∨ s(i+1, j)`,
* `¬it_i ∨ s(i+1, 0)` if `j = 0`, and `¬it_i ∨ ¬s(i, j−1) ∨ s(i+1, j)` otherwise,

and the unit clause `¬s(M, B)`. (`¬it_i` is the clause of the negated literals of
`it_i`.) An assignment of the other variables extends to a model of `atMost(B, items)`
iff at most `B` items are true under it.

*Proof.* Read `s(i, j)` as "more than `j` of the first `i` items are true". By induction
on `i` the clauses force `s(i, j)` to be true whenever that statement holds, so
`¬s(M, B)` forbids `B + 1` true items. Conversely, giving every `s(i, j)` exactly that
meaning satisfies all clauses when at most `B` items are true. ∎

### 4.2 The formula

Let `T = W·H`. Cells range over the grid. For a cell `v`, `nbrs(v)` are its at most four
grid neighbours. Variables (the numbering is by nested Cantor pairing, `Encode.lean`):

| Variable | Intended meaning |
|---|---|
| `e{u,v}` for adjacent `u, v` | the network has the edge `u — v` |
| `tile(x)` | `x` is a track tile |
| `sel(p, c)` | port `p` chooses city `c` |
| `g(p, t, v)`, `0 ≤ t ≤ T` | `d(p, v) ≤ t` |
| `r(p, t, v)`, `0 ≤ t ≤ T` | `dist_N(p, v) ≤ t` |
| `y(p, t, v, u)` | `v` is reached within `t + 1` network steps, the last one from `u` |
| counter variables | as in Lemma C |

Clauses (`Formula.lean`; the Python generator `network_solver/sat.py` lists them in the
same order):

1. **Edges.** For every cell `v` and `u ∈ {right(v), below(v)}`: if `v` or `u` is not
   open, `¬e{v,u}`. Otherwise, `e{v,u} → tile(v)` if `v` is free and `e{v,u} → tile(u)`
   if `u` is free.
2. **Degree.** For every free cell `v` with `v.x ≥ 1` and `v.y ≥ 1`: not all four of
   `e{v, right}`, `e{v, below}`, `e{v, left}`, `e{v, above}`.
3. **Distance 0.** For every port `p` and cell `v`: `g(p, 0, p)`; for `v ≠ p`,
   `¬g(p, 0, v)` and `¬r(p, 0, v)`.
4. **Grid steps.** For every port `p`, `t < T`, cell `v`: with
   `S_G = {u ∈ nbrs(v) : (u = p ∨ u free) ∧ u, v open}`,
   `g(p, t+1, v) ↔ g(p, t, v) ∨ ⋁_{u ∈ S_G} g(p, t, u)` (as `2 + |S_G|` clauses).
5. **Network steps.** With `S_N = {u ∈ nbrs(v) : u = p ∨ u free}`:
   `r(p, t+1, v) → r(p, t, v) ∨ ⋁_{u ∈ S_N} y(p, t, v, u)`, and for `u ∈ S_N`:
   `y(p, t, v, u) → r(p, t, u)` and `y(p, t, v, u) → e{u,v}`.
6. **Reachability of chosen cities.** `sel(p, c) → g(p, T, c)` and
   `sel(p, c) → r(p, T, c)`.
7. **Nearest choice.** For all cities `c, c'` and `t ≤ T`:
   `sel(p, c) ∧ ¬sel(p, c') ∧ g(p, t, c') → g(p, t, c)`.
8. **Cardinality.** `atMost(k, {sel(p, c)}_c)` and `atMost(|C| − k, {¬sel(p, c)}_c)`.
9. **Excess.** `atMost(X, {sel(p, c) ∧ g(p, t, c) ∧ ¬r(p, t, c)}_{p, c, t < T})`.
10. **Tiles.** `atMost(K, {tile(x)}_x)`.

### 4.3 Correctness

**Soundness (a model gives a solution; `SoundMain.lean`: `enc_sound`).** Let `a` satisfy
the formula. Take the network with an edge `u — v` for every true `e{u,v}` whose lower
endpoint is in the grid, and `choice(p) = {c ∈ C : sel(p, c)}`.

* By (1), edges join grid-adjacent open cells; so network adjacency is exactly "adjacent,
  both open, `e` true". By (1) again, every free cell touched by an edge has `tile`
  true.
* A free cell has at most four neighbours in the grid, and by (2) not all four edges, so
  its degree is at most 3. If `v.x = 0` or `v.y = 0` it has at most three neighbours.
* By (3), (4) and induction on `t`: `g(p, t, v)` is true **iff** `reach_t(v)` for the
  grid relation, i.e. iff `d(p, v) ≤ t` (Lemma A). By (3), (5) and induction on `t`:
  `r(p, t, v)` true **implies** `dist_N(p, v) ≤ t`.
* Nearest choice. (8) and Lemma C give `|choice(p)| ≤ k` and `|C ∖ choice(p)| ≤ |C| − k`,
  hence `|choice(p)| = k`. (6) gives `d(p, c) ≤ T < ∞` for chosen `c`. For chosen `c`
  and unchosen `c'`, let `m` be any number with `d(p, c') ≤ m`. If `m ≤ T`, (7) at
  `t = m` gives `d(p, c) ≤ m`. If `m > T`, Lemma B gives `d(p, c') ≤ T` and (7) at
  `t = T` gives `d(p, c) ≤ T ≤ m`. So `d(p, c) ≤ d(p, c')`.
* Connectivity: (6) gives `dist_N(p, c) ≤ T` for chosen `c`.
* Excess. For a chosen pair let `dn = dist_N(p, c) ≤ T` and `dg = d(p, c)`. For every
  `t` with `dg ≤ t < dn` the item `(p, c, t)` of (9) is true: `g(p, t, c)` is true, and
  `r(p, t, c)` is false because it would imply `dn ≤ t`. So the pair has at least
  `dn − dg` true items, the total excess is at most the number of true items, and that
  is at most `X` by Lemma C.
* Tiles: every tile has `tile` true, so there are at most `K` of them by (10).

**Completeness (a solution gives a model; `Complete.lean`: `enc_complete`).** Let `σ` be
feasible with excess `≤ X` and at most `K` tiles. Give every variable its intended
meaning for `σ`: `e{u,v}` := the network joins `u` and `v`; `tile(x)` := `x` is a tile of
`σ`; `sel(p, c)` := `c ∈ choice(p)`; `g(p, t, v)` := `reach_t(v)` in the grid;
`r(p, t, v)` := `reach_t(v)` in the network; `y(p, t, v, u)` := `r(p, t, u)` and the
network joins `u` and `v`; counters as in Lemma C. Then:

* (1) holds because edges of a feasible network join open cells and their free endpoints
  are tiles. (2) holds because four network neighbours would contradict the degree
  bound. (3)–(5) hold by the definition of `reach`.
* (6): chosen cities have finite grid and network distance, hence distance `≤ T` by
  Lemma B (network edges stay inside the grid).
* (7) is the nearest-choice condition read through Lemma A.
* (8): `|choice(p)| = k`, and `choice(p) ⊆ C`.
* (9): the item `(p, c, t)` is true iff `c` is chosen and `d(p, c) ≤ t < dist_N(p, c)`.
  A chosen pair therefore has exactly `dist_N − d` true items, and the total is the
  excess, which is `≤ X`.
* (10): the true items are the tiles of `σ` in the grid.

Lemma C turns the three cardinality facts into models of the counter clauses. ∎

### 4.4 Running time and size

The generator consists of nested loops over cells (`N`), time steps (`T = N`), ports,
cities, and counter positions, with O(1) work and O(1) clauses of at most 6 literals in
the innermost body. Counting clauses family by family:

| Family | Clauses |
|---|---|
| (1)–(2) | `≤ 5N` |
| (3) | `≤ 2N` per port |
| (4)–(5) | `≤ 15·N·T` per port |
| (6) | `2|C|` per port |
| (7) | `|C|²(T + 1)` per port |
| (8) | `2|C|(k + 1) + 2|C|(|C| − k + 1) + 2` per port |
| (9) | `2|P||C|T(X + 1) + 1` |
| (10) | `2N(K + 1) + 1` |

In total `O(|P|N² + |P||C|²N + |P||C|NX + NK) = O(n⁴)` clauses. Variable indices are
nested pairings of numbers bounded by `n³`, so they have `O(log n)` bits. The reduction
runs in time linear in its output, `O(n⁴ log n)` bit operations.

The Lean proof establishes a cruder but fully explicit bound, `2·10⁸·n⁷` (§5.3).

## 5. The Lean formalisation of Theorem 1

### 5.1 Map of the files (`lean/TrainNetwork/`)

| File | Content |
|---|---|
| `Sat.lean` | SAT (`KInstance`, `size`, `KYes`), Lemma C |
| `Reach.lean` | Lemmas A and B |
| `Encode.lean` | variable numbering, Boolean cell tests, the lists of cells, ports, cities |
| `Formula.lean` | the formula `enc I X K` as a pure function, meaning of each clause family |
| `Sound.lean`, `Count.lean`, `SoundMain.lean` | soundness, `enc_sound` |
| `Complete.lean` | completeness, `enc_complete`, and `enc_correct` |
| `Gen.lean` | `toK` in `TimeM`; `toK_val : (toK I X K).val = ⟨enc I X K⟩` |
| `Bound.lean`, `BlockSize.lean`, `TimeBound.lean` | cost of loops, of blocks, of `toK` |
| `Forward.lean` | `to_correct`, `toK_time_le`, `to_poly` |
| `Answer.lean`, `GoalForward.lean` | packaging; the forward half of `Goal.lean`, verbatim |

No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`, no `@[extern]`, no
`native_decide`. `Problem.lean`, `Cost.lean`, `Goal.lean` and `docs/problem.md` are
unchanged. `toK` is executable: `GoalForward.lean` evaluates
`(toK tinyInstance 0 1).time` (13093 steps, 99 clauses).

### 5.2 Auditing the ticks

The header of `Gen.lean` lists every charge. In short:

* `forL` (the only loop combinator): one tick per iteration, one for the exit test, and
  `x.length` for every append `x ++ rest`. `counterM` recurses over the items with one
  tick each. `appendM` charges the length of its first argument.
* `rangeM n` charges `n + 1`; `cellsM` 1 per cell; `filterM` 2 per cell.
* Every clause is emitted by `block c φ`, with `φ` a list of at most 15 clauses of at
  most 6 literals computed by pure code from the loop variables. It charges the encoding
  length of `φ`, 32 per literal for the at most 28 arithmetic operations of its variable
  index, and a constant `c` for the bounded number of tests that select the block. The
  header counts the operations behind each constant (128, 4, 128, 4, 0, 16).
* A set lookup `c ∈ I.blocked` (or `I.ports`, `I.cities`) is one primitive operation,
  as the auditing rule allows ("finset access").

One thing a reviewer should know: the O(1) blocks are computed by pure Lean functions
and charged with `tickN` at a constant that I counted by hand; Lean does not check that
count. The loops, which are what makes the running time grow, are all explicit.

Noncomputable definitions (`Classical.choice`, the assignment built from a solution)
occur only in proofs.

### 5.3 Where the Lean proof and the paper proof differ

1. **Running-time bound.** Paper: `O(n⁴)` clauses, `O(n⁴ log n)` bits. Lean:
   `(toK I X K).time ≤ 2·10⁸ · n⁷` and the same bound for the output size. The Lean proof
   bounds every loop length by `n`, the excess item list by `n³`, and the bit length of
   every variable index by `32·(n³ + 3)` (`sz_pair`: a pairing at most doubles the bit
   length; indices are bounded by their value instead of by a logarithm).
2. **Size is bounded through time.** Lean proves `output size ≤ running time`
   (`toK_size_le_time`), because `block` charges the encoding length of what it emits.
   The paper bounds the size directly.
3. **Cost model.** The paper counts unit-cost steps asymptotically. Lean uses the
   explicit constants of §5.2.
4. **Walks.** The paper speaks of walks; Lean uses the frozen list-based `IsWalk` and the
   normal form `isWalk_iff`.
5. **Network adjacency.** In Lean the decoded solution contains an edge only if its
   lower endpoint is in the grid, and `netAdj_decSol` shows that under the edge clauses
   this is the relation "adjacent, both open, edge variable true". The paper states this
   in one sentence.
6. **`r` is one-sided.** Both proofs use only "`r(p, t, v)` true implies
   `dist_N(p, v) ≤ t`". In the completeness direction Lean sets `r` to the exact value.
7. **Counters.** Lean indexes counter variables by a tag, the item position and `j`, and
   proves that the counter variables of the model do not interfere with the other
   variables (`cnt_full_take`: variables of families 0–5 never have tag 6).
8. **Degenerate grids.** Lean needs `W, H ≥ 1` to bound `W` and `H` by `W·H`; this
   follows from `k ≥ 1` and `k ≤ |C|` (`inst_pos`). The paper does not mention it.
9. **Theorem 3 and Corollary 4 are not in Lean at all.**

## 6. NP-hardness: Rectilinear Steiner Tree → Train Network (paper proof)

### 6.1 The source problem, and what is taken from the literature

**RECTILINEAR STEINER TREE (RST).** *Instance:* a finite set `A ⊂ ℤ × ℤ` and an integer
`L`. *Question:* is there a tree composed of horizontal and vertical line segments that
contains every point of `A` and has total length at most `L`? Write `RST(A)` for the
minimum length.

* NP-completeness: M. R. Garey and D. S. Johnson, *The rectilinear Steiner tree problem
  is NP-complete*, SIAM J. Appl. Math. 32 (1977), 826–834. In *Computers and
  Intractability* it is the rectilinear case of [ND13] GEOMETRIC STEINER TREE.
* Hanan's theorem: M. Hanan, *On Steiner's problem with rectilinear distance*, SIAM J.
  Appl. Math. 14 (1966), 255–265. Some minimum tree lies on the *Hanan grid* of `A` (the
  horizontal and vertical lines through the points of `A`). Hence `RST(A)` is an integer
  and equals the minimum number of edges of a connected subgraph of the integer grid
  graph that contains `A`.
* Scaling: `RST(s·A) = s·RST(A)` for every integer `s ≥ 1`.

**The fact I could not re-check.** The reduction below produces a grid whose side is
proportional to the largest coordinate of `A`. With the dense encoding of
docs/problem.md it is polynomial only if the coordinates are bounded by a polynomial in
`|A|`. So Theorem 3 needs RST to be NP-complete *in the strong sense*. I recall that
[ND13] carries the comment "NP-complete in the strong sense", and that the 1977
construction places points at unit spacing along a rectilinear embedding of a planar
graph, which bounds the coordinates by the number of points. The network policy of this
session blocked the sources, and a web search confirmed the 1977 reference but not the
words "strong sense". **Corollary 4 depends on this fact.** Everything else in this
section is proved here.

### 6.2 The reduction

Let `A = {a_1, …, a_m}` with `m ≥ 2` distinct points, translated so that the smallest
coordinates are 0, and let `D` be the largest coordinate. If `L < 0` output any fixed
no-instance; replace `L` by `min(L, 2mD)` (a spanning tree is never longer). Let
`s = 4m + 1` and `φ(x, y) = (s·x + 2, s·y + 2)`. Output

* the grid `W × H` with `W = s·x_max + 5`, `H = s·y_max + 5`, no blocked cells;
* one port `φ(a_1)`; the cities `φ(a_2), …, φ(a_m)`; `k = m − 1`;
* `X = (m − 1)·W·H` and `K = s·L + 3m + 1`.

The grid has `O((mD)²)` cells and `X`, `K` are polynomial in `m + D`, so the reduction is
polynomial when `D` is polynomially bounded. Python: `network_solver/steiner.py`,
`rst_to_train`.

Call the points `φ(z)`, `z ∈ ℤ²`, *lattice points*. Two lattice points are at least
`s ≥ 9` apart, and every lattice point in the bounding box of `φ(A)` is at least 2 cells
from the border. The *block* of a lattice point is the 3 × 3 square around it. Blocks are
pairwise disjoint and not adjacent.

### 6.3 Correctness

Every city must be chosen, because `k = |C|`. All grid distances are finite: the grid
minus the cities is connected, since cities are isolated and away from the border. So
`IsNearestChoice` holds exactly for `choice(port) = C`. A network distance, when finite,
is less than `W·H`, so the total excess of any feasible solution is less than `X`: the
excess bound never binds.

**Claim 1. Every feasible solution has at least `s·RST(A) + 1 − m` tiles.**
For each city take a walk from the port in the network whose intermediate cells are
free. The union `U` of the cells of these walks is connected and contains the `m`
terminals; its other cells are free cells touched by network edges, i.e. tiles. A
spanning tree of `U` in the grid graph is a rectilinear Steiner tree of `φ(A)` with
`|U| − 1` unit edges, so `|U| − 1 ≥ RST(φ(A)) = s·RST(A)`, and the number of tiles is at
least `|U| − m`.

**Claim 2. There is a feasible solution with at most `s·RST(A) + 3m + 1` tiles.**
By Hanan's theorem take a minimum tree `T_0` for `A` on the Hanan grid, and let
`T = φ(T_0)`: a tree in the grid graph with `s·RST(A)` edges and `s·RST(A) + 1` cells,
`m` of them terminals. All its branch points, corners and terminals are lattice points,
and inside the block of a lattice point `q` it consists of `q` and of some of the four
cells next to `q` (its *arms*); the corner cells of the block are not in `T`. Modify `T`
independently inside blocks:

* *A city `q` with `d ≥ 2` arms.* A walk may not pass through a city. Go around the
  eight cells surrounding `q` clockwise and take the shortest arc that contains all arm
  cells. Add the cells and edges of that arc, delete the edges at `q`, and join `q` to
  the first cell of the arc. The arc adds at most 3 cells (`d = 2` opposite arms: 3;
  `d = 2` adjacent arms: 1; `d = 3`: 2; `d = 4`: 3). Arm cells now have degree at most 3
  (their arm, at most two arc neighbours; the first one has `q` instead of a second arc
  neighbour), new cells have degree 2, and `q` is a leaf.
* *A free cell `q` with 4 arms.* Delete the edge from `q` to its upper arm cell `u`, add
  the corner cell `c` between `u` and the right arm cell `r`, and the edges `u — c`,
  `c — r`. This adds 1 cell; `q` and `r` get degree 3, `u` and `c` degree 2.
* The port needs no change: a terminal may have 4 edges and every walk starts there.

The result is connected, every city is a leaf attached to a free cell, and every free
cell has degree at most 3. So the port reaches every city by a walk through free cells:
the solution is feasible. At most `m − 1` cities are repaired, at 3 cells each. A tree
with at most `m` leaves has at most `(m − 2)/2` vertices of degree 4. So at most
`3(m − 1) + (m − 2)/2 < 4m` cells are added, and the number of tiles is at most
`s·RST(A) + 1 − m + 4m`.

**Conclusion.** If `RST(A) ≤ L`, Claim 2 gives a solution with at most
`s·L + 3m + 1 = K` tiles: a yes-instance. If `RST(A) ≥ L + 1`, Claim 1 gives at least
`s·(L + 1) + 1 − m = K + (s − 4m) > K` tiles in every feasible solution: a no-instance. ∎

### 6.4 From Theorem 3 to "equivalent to SAT"

Train ≤ₚ SAT is Theorem 1. For SAT ≤ₚ Train: SAT ≤ₚ RST with polynomially bounded
coordinates by Garey and Johnson (1977) (subject to §6.1), and RST ≤ₚ Train by Theorem 3.
The composed reduction is **not** implemented as one program here, and nothing of it is
formalised.

## 7. Experiments

All of this is in the pytest suite (`python -m pytest -q`, 587 tests, about 2 minutes).

**Train → SAT** (`tests/test_sat_reduction.py`). 210 random instances from
`network_solver.generate.random_instance`: grids from 2 × 2 to 6 × 5, 1–3 ports, 1–5
cities, `k` from 1 to 5, blocked fractions 0–0.3; at least 50 with blocked cells and at
least 20 with a real tie choice (asserted by `test_instance_mix_is_varied`). For each
instance up to five queries `(X, K)` around the lexicographic optimum: the optimum
itself, one tile fewer, one unit of excess fewer, more excess with fewer tiles, and a
random pair. For every query the formula `to_sat(I, X, K)` is satisfiable iff the CP-SAT
oracle (`network_solver.decide.decide_cpsat`, built on `network_solver.cpsat`) answers
yes, and every model decodes to a network that `network_solver.verify` accepts within
the bounds. No disagreement.

**RST → Train** (`tests/test_steiner_reduction.py`). 300 random point sets (2–5 points
in boxes up to 5 × 5). Yes side: the network of Claim 2, built by `steiner.witness`,
passes the verifier with at most `K(RST(A))` tiles. No side: an independent
Dreyfus–Wagner computation on the full scaled grid (no Hanan grid) gives the lower bound
of Claim 1 and it exceeds `K(RST(A) − 1)`; the same computation confirms
`RST(s·A) = s·RST(A)`. The CP-SAT oracle agrees on the yes side for 25 small sets and on
both sides for collinear pairs. On two-dimensional sets the oracle cannot refute a
one-tile gap within minutes, so the no side is **not** checked against CP-SAT there.

**No round trip.** Train → SAT → Train was not run: the backward direction exists only
as RST → Train plus published reductions.

**Runtime on `data/instances/europe.json`** (49 × 55, 6 ports, 23 cities, `k = 9`), for
the query `(X, K) = (2, 210)`, the cost of the reference solution, on the 4-core
container of this session:

| | Time | Output |
|---|---|---|
| `to_sat` (CPython, clauses generated and counted, not stored) | 550 s | 432,120,212 clauses, 1,076,093,685 literals |
| CP-SAT, `python -m network_solver solve` (optimisation, 4 workers) | EUROPE_CPSAT | EUROPE_CPSAT_OUT |

The formula was not given to a SAT solver. The reduction is a proof of membership in NP,
not a practical algorithm: its time-expanded distance variables cost `Θ(|P|·N²)` clauses.

## 8. What blocked the backward direction, and what would finish the goal

Every instance of the Train Network Problem is a planar object, and SAT is not. A
reduction from SAT therefore has to contain a planarisation step: either the crossover
gadgets inside the published chain SAT → planar vertex cover → RST (Garey, Johnson and
Stockmeyer 1976; Garey and Johnson 1977), or new crossover gadgets inside the grid. I
did not find a direct reduction from SAT whose gadgets are simple enough to verify.
One obstacle is worth recording. If the routes of two pairs `(p, c)` and `(q, c')` cross
at a free cell `x`, then `p` can reach `c'` and `q` can reach `c` through `x`, and
comparing the two lengths shows that `c'` is at least as near to `p` as `c`, or `c` at
least as near to `q` as `c'`. So crossing routes always change the nearest-city sets, and
wires cannot simply cross.

What remains for `Goal.lean`:

1. `fromK : KInstance → TimeM (Instance × ℕ × ℕ)` for SAT, with `from_correct` and
   `from_poly`. Following §6 this means formalising Hanan's theorem, the reduction of
   §6.2, and the Garey–Johnson–Stockmeyer and Garey–Johnson reductions, including a
   rectilinear planar embedding. None of this is started.
2. Alternatively, a direct matrix-layout reduction from SAT with a verified crossover
   cell. I have no such gadget.

The strongest machine-checked statement is Theorem 1: `to_correct` and `to_poly` in
`lean/TrainNetwork/Forward.lean`.
