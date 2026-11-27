/-
FROZEN GOAL. Do not edit. Provide the referenced definitions and lemmas in
`TrainNetwork/Answer.lean` (and any files it imports).

Claim: the decision version of docs/problem.md (`Decide I X K`) is polynomial-time
equivalent to an established problem from the literature (`Answer.KYes`). This is shown
by polynomial-time many-one reductions in both directions, so the two problems have the
same complexity.

The known problem must be a standard problem whose complexity is already established in
published work (cite it in docs/result.md). Its Lean definition must faithfully match
the published definition. A re-statement of the train network problem itself does not
count. The size measure `Answer.KInstance.size` must be the standard encoding length
for that problem, up to a polynomial.
-/
import TrainNetwork.Answer

namespace TrainNetwork

-- TINY

-- Fail to build unless the reductions are executable code.
#eval (Answer.toK tinyInstance 0 1).time
#eval (Answer.fromK (Answer.toK tinyInstance 0 1).val).time

/-- Forward reduction is correct. -/
theorem goal_to_correct (I : Instance) (X K : ℕ) :
    Decide I X K ↔ Answer.KYes (Answer.toK I X K).val :=
  Answer.to_correct I X K

/-- Backward reduction is correct. -/
theorem goal_from_correct (J : Answer.KInstance) :
    Answer.KYes J ↔
      Decide (Answer.fromK J).val.1 (Answer.fromK J).val.2.1 (Answer.fromK J).val.2.2 :=
  Answer.from_correct J

/-- Forward reduction runs in polynomial time, with polynomially bounded output. The
numbers `X`, `K` count in unary, as they are bounded by a polynomial in `N` for any
meaningful query. -/
theorem goal_to_poly :
    ∃ q : Polynomial ℕ, ∀ (I : Instance) (X K : ℕ),
      (Answer.toK I X K).time ≤ q.eval (I.size + X + K) ∧
      (Answer.toK I X K).val.size ≤ q.eval (I.size + X + K) :=
  Answer.to_poly

/-- Backward reduction runs in polynomial time, with polynomially bounded output. -/
theorem goal_from_poly :
    ∃ q : Polynomial ℕ, ∀ J : Answer.KInstance,
      (Answer.fromK J).time ≤ q.eval J.size ∧
      (Answer.fromK J).val.1.size + (Answer.fromK J).val.2.1 + (Answer.fromK J).val.2.2
        ≤ q.eval J.size :=
  Answer.from_poly

end TrainNetwork
