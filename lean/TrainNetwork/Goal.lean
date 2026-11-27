/-
FROZEN GOAL. Do not edit. Provide the referenced definitions and lemmas in
`TrainNetwork/Answer.lean` (and any files it imports).

Claim: with at most 10 ports and at most 40 cities, the optimisation problem of
docs/problem.md is solvable in time polynomial in N = W·H. The polynomial may depend on
the constants 10 and 40, but not on the instance.
-/
import TrainNetwork.Answer

namespace TrainNetwork

/-- A tiny instance, used only to check that the answer is executable code. -/
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

-- Fails to build unless `Answer.solve` is executable code.
#eval (Answer.solve tinyInstance).time

/-- On instances within the bounds, `Answer.solve` returns an optimal solution, or
`none` exactly when no feasible solution exists. -/
theorem goal_correct (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  Answer.correct I hP hC

/-- `Answer.solve` runs in time polynomial in `N` on instances within the bounds. -/
theorem goal_polytime :
    ∃ q : Polynomial ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (Answer.solve I).time ≤ q.eval I.size :=
  Answer.polytime

end TrainNetwork
