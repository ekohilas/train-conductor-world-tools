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
  -- the two `List.range`s
  tickN (I.W + I.H + 2)
  let r ← tmapM (fun x => tmapM (fun y => pure (x, y)) (List.range I.H)) (List.range I.W)
  -- flattening `W` lists of total length `W * H`
  tickN (I.W * I.H + I.W + 1)
  pure r.flatten

/-- The elements of a finite set of cells among `cells`, in the order of `cells`. Each
membership test is a linear scan of the set (two `ℕ` comparisons per element). -/
def scanT (s : Finset Cell) (cells : List Cell) : TimeM (List Cell) :=
  tfilterM (fun x => do
    tickN (2 * s.card + 1)
    pure (decide (x ∈ s))) cells

/-- The grid distance `d(p, c)` (`none` = unreachable), by one DP run without degree
constraint whose only demand is `(p, c)`, with reference distance `0`: the optimum cost
is `d(p, c) · M + (number of tiles)`, and the number of tiles is below `M`. -/
def distT (I : Instance) (p c : Cell) : TimeM (Option ℕ) := do
  let r ← dpRun I [(p, [(c, 0)])] 4
  -- one multiplication, one addition, one division
  tickN 3
  pure (r.map (fun e => e.1 / (I.W * I.H + 1)))

/-- The cities reachable from `p`, each with its grid distance. -/
def distsT (I : Instance) (cities : List Cell) (p : Cell) : TimeM (List (Cell × ℕ)) := do
  let ds ← tmapM (fun c => do
    let d ← distT I p c
    pure (d.map (fun g => (c, g)))) cities
  -- dropping the unreachable cities
  tickN (cities.length + 1)
  pure (ds.filterMap id)

/-- `∀ e' ∈ fin, e' ∈ S ∨ g ≤ e'.2`. -/
def nearRowT (S : List (Cell × ℕ)) (g : ℕ) : List (Cell × ℕ) → TimeM Bool
  | [] => pure true
  | e' :: fin => do
      -- a linear scan of `S` (three `ℕ` comparisons per element), one comparison
      tickN (3 * S.length + 4)
      let r ← nearRowT S g fin
      pure ((decide (e' ∈ S) || decide (g ≤ e'.2)) && r)

/-- `∀ e ∈ rest, ∀ e' ∈ fin, e' ∈ S ∨ e.2 ≤ e'.2`. -/
def nearAllT (S fin : List (Cell × ℕ)) : List (Cell × ℕ) → TimeM Bool
  | [] => pure true
  | e :: rest => do
      tick
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
  tmapM (fun S => pure (p, S)) good

/-- All combinations of valid choices, one per port. -/
def familiesT (I : Instance) (cities ports : List Cell) : TimeM (List PD) := do
  let V ← tmapM (choicesT I cities) ports
  tsections V

/-- The cheapest DP result over a list of choice combinations. -/
def bestT (I : Instance) : List PD → TimeM (Option (ℕ × PD × List (List Lab)))
  | [] => pure none
  | pd :: rest => do
      tick
      let r ← bestT I rest
      let cur ← dpRun I pd 3
      match cur with
      | none => pure r
      | some (c, w) =>
          match r with
          | none => pure (some (c, pd, w))
          | some (c', pd', w') => do
              tick
              if c ≤ c' then pure (some (c, pd, w)) else pure (some (c', pd', w'))

/-- The network edges described by a labelling: for every cell, its right and down
edges if the corresponding bits are set. -/
def edgesT (I : Instance) (w : List (List Lab)) (cells : List Cell) :
    TimeM (List (Cell × Cell)) := do
  let r ← tmapM (fun x => do
    -- two list accesses at indices `x.1`, `x.2`; two additions; at most two allocations
    tickN (x.1 + x.2 + 8)
    pure ((if (labOf (decide (I.H ≤ I.W)) w x).eR then [(x, (x.1 + 1, x.2))] else []) ++
          (if (labOf (decide (I.H ≤ I.W)) w x).eD then [(x, (x.1, x.2 + 1))] else []))) cells
  -- flattening lists of total length at most `2 · |cells|`
  tickN (3 * cells.length + 1)
  pure r.flatten

/-- The chosen cities of each port as finite sets (duplicate removal is quadratic). -/
def choiceTableT (pd : PD) : TimeM (List (Cell × Finset Cell)) :=
  tmapM (fun e => do
    tickN (e.2.length * e.2.length + e.2.length + 1)
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
      -- turning the edge list into a finite set removes duplicates: quadratic
      tickN (es.length * es.length + 1)
      let ch ← choiceTableT pd
      pure (some ⟨es.toFinset, fun p => ((tlookup p ch).val).getD ∅⟩)

end Answer

end TrainNetwork
