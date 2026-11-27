/-
The forward half of the frozen goal, restated verbatim from `Goal.lean` (theorems
`goal_to_correct` and `goal_to_poly`), and proved. The backward half of `Goal.lean`
(`goal_from_correct`, `goal_from_poly`) is NOT proved; see docs/result.md.
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
  k_le_cities := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide
  blocked_inBounds := by decide

-- Fail to build unless the forward reduction is executable code.
#eval (Answer.toK tinyInstance 0 1).time

/-- Forward reduction is correct. -/
theorem goal_to_correct (I : Instance) (X K : ℕ) :
    Decide I X K ↔ Answer.KYes (Answer.toK I X K).val :=
  Answer.to_correct I X K

/-- Forward reduction runs in polynomial time, with polynomially bounded output. The
numbers `X`, `K` count in unary, as they are bounded by a polynomial in `N` for any
meaningful query. -/
theorem goal_to_poly :
    ∃ q : Polynomial ℕ, ∀ (I : Instance) (X K : ℕ),
      (Answer.toK I X K).time ≤ q.eval (I.size + X + K) ∧
      (Answer.toK I X K).val.size ≤ q.eval (I.size + X + K) :=
  Answer.to_poly

end TrainNetwork
