/-
The complete algorithm `Answer.solve`.

1. List the grid cells; list ports and cities by scanning the grid.
2. For every port `p` and city `c`, compute the grid distance `d(p, c)` with one run of
   the certificate DP (single port, single demand, degree cap 4, i.e. no degree
   constraint).
3. For every port, enumerate the valid nearest-city choices (sub-lists of its reachable
   cities that pass the `k`-nearest test); take all combinations over the ports.
4. For every combination run the certificate DP (all ports, degree cap 3) and keep the
   cheapest result.
5. Decode the winning labelling into a network and return it with its choice.
-/
import TrainNetwork.Run

namespace TrainNetwork

open TimeM

/-- All cells of the grid, column by column. -/
def cellsT (I : Instance) : TimeM (List Cell) := do
  -- the two `List.range`s, each computed once
  tickN (I.W + I.H + 2)
  let xs := List.range I.W
  let ys := List.range I.H
  let r ← tmapM (fun x => tmapM (fun y => do
    -- one pair
    tick
    pure (x, y)) ys) xs
  -- flattening `W` lists of total length `W * H`; one multiplication, one addition
  tickN (I.W * I.H + I.W + 3)
  pure r.flatten

/-- The elements of a finite set of cells among `cells`, in the order of `cells`. Each
membership test is a linear scan of the set (per element: one step and two `ℕ`
comparisons). -/
def scanT (s : Finset Cell) (cells : List Cell) : TimeM (List Cell) :=
  tfilterM (fun x => do
    tickN (3 * s.card + 1)
    pure (decide (x ∈ s))) cells

/-- The grid distance `d(p, c)` (`none` = unreachable), by one DP run without degree
constraint whose only demand is `(p, c)`, with reference distance `0`: the optimum cost
is `d(p, c) · M + (number of tiles)`, and the number of tiles is below `M`. -/
def distT (I : Instance) (p c : Cell) : TimeM (Option ℕ) := do
  -- the port/demand list: two list cells, two pairs
  tickN 4
  let r ← dpRun I [(p, [(c, 0)])] 4
  -- one multiplication, one addition, one division, one result
  tickN 4
  pure (r.map (fun e => e.1 / (I.W * I.H + 1)))

/-- The cities reachable from `p`, each with its grid distance. -/
def distsT (I : Instance) (cities : List Cell) (p : Cell) : TimeM (List (Cell × ℕ)) := do
  let ds ← tmapM (fun c => do
    let d ← distT I p c
    -- one pair
    tick
    pure (d.map (fun g => (c, g)))) cities
  -- dropping the unreachable cities: per element one step and at most one list cell
  tickN (2 * cities.length + 1)
  pure (ds.filterMap id)

/-- `∀ e' ∈ fin, e' ∈ S ∨ g ≤ e'.2`. -/
def nearRowT (S : List (Cell × ℕ)) (g : ℕ) : List (Cell × ℕ) → TimeM Bool
  | [] => pure true
  | e' :: fin => do
      -- pattern match, recursive call, one comparison, and a linear scan of `S` (per
      -- element: one step and three `ℕ` comparisons)
      tickN (4 * S.length + 4)
      let r ← nearRowT S g fin
      pure ((decide (e' ∈ S) || decide (g ≤ e'.2)) && r)

/-- `∀ e ∈ rest, ∀ e' ∈ fin, e' ∈ S ∨ e.2 ≤ e'.2`. -/
def nearAllT (S fin : List (Cell × ℕ)) : List (Cell × ℕ) → TimeM Bool
  | [] => pure true
  | e :: rest => do
      -- pattern match, recursive call
      tickN 2
      let a ← nearRowT S e.2 fin
      let r ← nearAllT S fin rest
      pure (a && r)

/-- Is `S` a valid choice of `k` nearest cities among the reachable cities `fin`:
`k` cities, none of them farther than an unchosen one? -/
def nearT (k : ℕ) (fin S : List (Cell × ℕ)) : TimeM Bool := do
  -- the length of `S`, one comparison
  tickN (S.length + 2)
  let r ← nearAllT S fin S
  pure (decide (S.length = k) && r)

/-- All valid choices of port `p`, each paired with `p`. -/
def choicesT (I : Instance) (cities : List Cell) (p : Cell) :
    TimeM (List (Cell × List (Cell × ℕ))) := do
  let fin ← distsT I cities p
  let subs ← tsublists fin
  let good ← tfilterM (nearT I.k fin) subs
  tmapM (fun S => do
    -- one pair
    tick
    pure (p, S)) good

/-- All combinations of valid choices, one per port. -/
def familiesT (I : Instance) (cities ports : List Cell) : TimeM (List PD) := do
  let V ← tmapM (choicesT I cities) ports
  tsections V

/-- The cheapest DP result over a list of choice combinations. -/
def bestT (I : Instance) : List PD → TimeM (Option (ℕ × PD × List (List Lab)))
  | [] => pure none
  | pd :: rest => do
      -- pattern match, recursive call, one result tuple
      tickN 3
      let r ← bestT I rest
      let cur ← dpRun I pd 3
      match cur with
      | none => pure r
      | some (c, w) =>
          match r with
          | none => pure (some (c, pd, w))
          | some (c', pd', w') => do
              -- one comparison
              tick
              if c ≤ c' then pure (some (c, pd, w)) else pure (some (c', pd', w'))

/-- The network edges described by a labelling: for every cell, its right and down
edges if the corresponding bits are set. -/
def edgesT (I : Instance) (w : List (List Lab)) (cells : List Cell) :
    TimeM (List (Cell × Cell)) := do
  -- one comparison
  tick
  let col := decide (I.H ≤ I.W)
  let r ← tmapM (fun x => do
    -- the label of `x`: two list accesses at indices `x.1`, `x.2` (`x.1 + x.2 + 2`
    -- steps); two additions; at most six allocated pairs and list cells; one append
    tickN (x.1 + x.2 + 16)
    let a := labOf col w x
    pure ((if a.eR then [(x, (x.1 + 1, x.2))] else []) ++
          (if a.eD then [(x, (x.1, x.2 + 1))] else []))) cells
  -- flattening `|cells|` lists of total length at most `2 · |cells|`
  tickN (3 * cells.length + 1)
  pure r.flatten

/-- The chosen cities of each port as finite sets. Mapping a list of length `ℓ` costs
`ℓ` list cells; removing duplicates compares every pair of cells at most once (two `ℕ`
comparisons each) and allocates at most `ℓ` list cells. -/
def choiceTableT (pd : PD) : TimeM (List (Cell × Finset Cell)) :=
  tmapM (fun e => do
    tickN (2 * e.2.length * e.2.length + 2 * e.2.length + 2)
    pure (e.1, (e.2.map Prod.fst).toFinset)) pd

namespace Answer

/-- The algorithm. -/
def solve (I : Instance) : TimeM (Option Solution) := do
  let cells ← cellsT I
  let ports ← scanT I.ports cells
  let cities ← scanT I.cities cells
  let fams ← familiesT I cities ports
  let best ← bestT I fams
  match best with
  | none => pure none
  | some (_, pd, w) => do
      let es ← edgesT I w cells
      -- turning the edge list into a finite set removes duplicates: every pair of edges
      -- is compared at most once (four `ℕ` comparisons each), at most `|es|` list cells
      tickN (4 * es.length * es.length + es.length + 2)
      let ch ← choiceTableT pd
      pure (some ⟨es.toFinset, fun p => ((tlookup p ch).val).getD ∅⟩)

end Answer

end TrainNetwork
