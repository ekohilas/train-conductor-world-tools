/-
FROZEN GOAL. Do not edit. Provide the referenced definitions and lemmas in
`TrainNetwork/Answer.lean` (and any files it imports).

Claim: with at most 10 ports and at most 40 cities, the optimisation problem of
docs/problem.md is solvable in time 2^{o(N)}, where N = W·H. Exhaustive search over
networks takes 2^{Θ(N)}.
-/
import TrainNetwork.Answer

namespace TrainNetwork

-- TINY

-- Fails to build unless `Answer.solve` is executable code.
#eval (Answer.solve tinyInstance).time

/-- On instances within the bounds, `Answer.solve` returns an optimal solution, or
`none` exactly when no feasible solution exists. -/
theorem goal_correct (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  Answer.correct I hP hC

/-- Sub-exponential running time: for every `ε > 0`, on all large enough instances
within the bounds, the time is at most `2^(ε·N)`. -/
theorem goal_subexp :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      n₀ ≤ I.size → ((Answer.solve I).time : ℝ) ≤ (2 : ℝ) ^ (ε * I.size) :=
  Answer.subexp

end TrainNetwork
