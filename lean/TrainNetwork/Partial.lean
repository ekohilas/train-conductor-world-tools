/-
PARTIAL RESULT. This file does NOT prove the frozen goal of `TrainNetwork/Goal.lean`.

What is proved here (see docs/result.md, section 5):

* `Partial.correct`: the exhaustive solver `Brute.bruteSolve` returns an optimal solution,
  or `none` exactly when no feasible solution exists. This is the statement of
  `goal_correct` with `(Answer.solve I).val` replaced by `Partial.solve I`, and without
  the hypotheses on the number of ports and cities.

What is NOT proved, here or anywhere in this repository:

* `goal_polytime`. We have no polynomial-time algorithm. `Partial.solve` is exhaustive
  search over all sets of grid edges; it is exponential in `Instance.size`.
* `Partial.solve` is a plain function, not a `TimeM` computation. It charges no ticks and
  no running-time claim is made for it. Wrapping it in `pure` would give `time = 0` and
  make `goal_polytime` type-check, but that would violate the auditing rule of
  `Cost.lean`. It must not be used as `Answer.solve`, and `TrainNetwork/Answer.lean`
  deliberately does not exist.
-/
import TrainNetwork.Cost
import TrainNetwork.Brute.Solve
import TrainNetwork.Brute.CrossCheck

namespace TrainNetwork.Partial

/-- Exhaustive search over all sets of grid edges and all choices of cities.
Exponential. Not in `TimeM`. -/
def solve (I : Instance) : Option Solution := Brute.bruteSolve I

/-- `Partial.solve` returns an optimal solution, or `none` exactly when no feasible
solution exists. Holds for every instance. -/
theorem correct (I : Instance) :
    match solve I with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  Brute.bruteSolve_correct I

/-- Feasibility is decidable (by the same exhaustive search). -/
theorem feasible_iff (I : Instance) : (∃ σ : Solution, σ.Feasible I) ↔ (solve I).isSome := by
  have h := correct I
  cases hs : solve I with
  | none => rw [hs] at h; simpa using h
  | some σ => rw [hs] at h; simpa using ⟨σ, h.1⟩

/-- The instance used in `Goal.lean` to check executability (copied, since `Goal.lean`
cannot be imported). -/
def tinyInstance : Instance where
  W := 3
  H := 1
  blocked := ∅
  ports := {(0, 0)}
  cities := {(2, 0)}
  k := 1
  k_pos := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide

-- `Partial.solve` is executable: prints `some (some 0, 1)`, i.e. excess 0 and 1 tile.
#eval Brute.bruteCost tinyInstance

#print axioms correct

open Lean Elab Command in
run_cmd logWarning "GOAL NOT REACHED: TrainNetwork.Goal is not built. Only Partial.correct (exhaustive search, exponential, not in TimeM) is proved; goal_polytime is open. See docs/result.md."

end TrainNetwork.Partial
