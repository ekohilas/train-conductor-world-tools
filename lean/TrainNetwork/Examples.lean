/-
Executable sanity checks of the verified algorithm on a few strips (grids of height 1),
where the dense enumeration is still fast. These are tests (`#guard` runs the compiled
code), not part of the proof.
-/
import TrainNetwork.Solve

namespace TrainNetwork.Examples

/-- `P . C C` on a 4 × 1 strip. With `k = 1` the near city is chosen. With `k = 2` the
far city would be needed, but it is only reachable through the near city, which walks
may not pass: no feasible solution. -/
def strip (k : ℕ) (hk : 0 < k) (hk2 : k ≤ 2) : Instance where
  W := 4
  H := 1
  blocked := ∅
  ports := {(0, 0)}
  cities := {(2, 0), (3, 0)}
  k := k
  k_pos := hk
  k_le_cities := by simpa using hk2
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide
  blocked_inBounds := by decide

#guard (Answer.solve (strip 1 (by decide) (by decide))).val.map
    (fun σ => (σ.edges, σ.choice (0, 0))) =
  some ({((0, 0), (1, 0)), ((1, 0), (2, 0))}, {(2, 0)})

#guard (Answer.solve (strip 2 (by decide) (by decide))).val.isNone

/-- `P . C . P` on a 5 × 1 strip: two ports sharing the middle city. -/
def twoPorts : Instance where
  W := 5
  H := 1
  blocked := ∅
  ports := {(0, 0), (4, 0)}
  cities := {(2, 0)}
  k := 1
  k_pos := by decide
  k_le_cities := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide
  blocked_inBounds := by decide

#guard (Answer.solve twoPorts).val.map
    (fun σ => (σ.edges, σ.choice (0, 0), σ.choice (4, 0))) =
  some ({((0, 0), (1, 0)), ((1, 0), (2, 0)), ((2, 0), (3, 0)), ((3, 0), (4, 0))},
    {(2, 0)}, {(2, 0)})

/-- `P C` on a 2 × 1 strip: port next to its city, a direct terminal edge, no tile. -/
def adjacent : Instance where
  W := 2
  H := 1
  blocked := ∅
  ports := {(0, 0)}
  cities := {(1, 0)}
  k := 1
  k_pos := by decide
  k_le_cities := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide
  blocked_inBounds := by decide

#guard (Answer.solve adjacent).val.map (fun σ => (σ.edges, σ.choice (0, 0))) =
  some ({((0, 0), (1, 0))}, {(1, 0)})

/-- `P # C` on a 3 × 1 strip with a blocked middle cell: the city is unreachable. -/
def blockedStrip : Instance where
  W := 3
  H := 1
  blocked := {(1, 0)}
  ports := {(0, 0)}
  cities := {(2, 0)}
  k := 1
  k_pos := by decide
  k_le_cities := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide
  blocked_inBounds := by decide

#guard (Answer.solve blockedStrip).val.isNone

end TrainNetwork.Examples
