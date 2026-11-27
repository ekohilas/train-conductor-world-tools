/-
FROZEN GOAL. Do not edit. Provide the referenced definitions and lemmas in
`TrainNetwork/Answer.lean` (and any files it imports).

Claim: the optimisation problem of docs/problem.md is solvable in time polynomial in
N = W·H, for unbounded numbers of ports and cities.
-/
import TrainNetwork.Answer

namespace TrainNetwork

-- TINY

-- Fails to build unless `Answer.solve` is executable code.
#eval (Answer.solve tinyInstance).time

/-- `Answer.solve` returns an optimal solution, or `none` exactly when no feasible
solution exists. -/
theorem goal_correct (I : Instance) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  Answer.correct I

/-- `Answer.solve` runs in time polynomial in `N`. -/
theorem goal_polytime :
    ∃ q : Polynomial ℕ, ∀ I : Instance, (Answer.solve I).time ≤ q.eval I.size :=
  Answer.polytime

end TrainNetwork
