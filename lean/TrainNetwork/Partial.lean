/-
What is actually proved (a PARTIAL result; `Goal.lean` is NOT proved).

This file mirrors `Goal.lean` with the quasi-polynomial bound replaced by the exponential
bound that holds for the exhaustive solver. Build it with

    lake build TrainNetwork.Partial

`Goal.lean` itself fails to build, because `Answer.quasipoly` does not exist.
-/
import TrainNetwork.Answer

namespace TrainNetwork.Partial

/-- The tiny instance of `Goal.lean`. -/
def tinyInstance : Instance where
  W := 3
  H := 1
  blocked := ∅
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

-- `Answer.solve` is executable code.
#eval (Answer.solve tinyInstance).time
#eval (Answer.solve tinyInstance).val.map (fun σ => (σ.edges, σ.choice (0, 0)))

/-- PROVED. Identical to `Goal.goal_correct`. -/
theorem partial_correct (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  Answer.correct I hP hC

/-- PROVED, but weaker than `Goal.goal_quasipoly`: the exponent is `c * N`, not
`c * (log₂ N + 1) ^ d`. -/
theorem partial_exp_time :
    ∃ c : ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (Answer.solve I).time ≤ 2 ^ (c * I.size) :=
  Answer.exp_time

/-- PROVED. Any candidate list that dominates every feasible solution gives a solver
meeting the specification of `Goal.goal_correct`. The open part of the goal is therefore
exactly: produce and search such a list in quasi-polynomial time. -/
theorem partial_reduction (I : Instance) (cs : List Cand) (h : Complete I cs) :
    match solveFrom I cs with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  solveFrom_correct I cs h

#print axioms partial_correct
#print axioms partial_exp_time
#print axioms partial_reduction

end TrainNetwork.Partial
