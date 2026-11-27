/-
The forward reduction, Train Network Problem → SAT: correctness and polynomial bounds.

These are the statements `to_correct` and `to_poly` required by `Goal.lean`.
-/
import TrainNetwork.Complete
import TrainNetwork.TimeBound

namespace TrainNetwork.Answer

open TrainNetwork TimeM

/-- Forward reduction is correct: `(I, X, K)` is a yes-instance of the Train Network
Problem iff the formula `toK I X K` is satisfiable. -/
theorem to_correct (I : Instance) (X K : ℕ) : Decide I X K ↔ KYes (toK I X K).val := by
  rw [toK_val]
  exact enc_correct I X K

theorem Q_le (n : ℕ) (hn : 1 ≤ n) : Q (n * (n * (n * 1)) + 3) ≤ 14633 * n ^ 3 := by
  unfold Q
  have e : n * (n * (n * 1)) = n ^ 3 := by ring
  rw [e]
  have : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  omega

/-- Explicit running-time bound for `toK`, in the input size `I.size + X + K`. -/
theorem toK_time_le (I : Instance) (X K : ℕ) :
    (toK I X K).time ≤ 200000000 * (I.size + X + K) ^ 7 := by
  have h := toKgen_time_raw I X K
  have hsz : I.size + X + K = I.W * I.H + 1 + X + K := rfl
  rw [hsz]
  have hn : 1 ≤ I.W * I.H + 1 + X + K := by omega
  generalize I.W * I.H + 1 + X + K = n at h hn ⊢
  have hq := Q_le n hn
  have h2 := bRaw_le n _ hn (Q_pos (n * (n * (n * 1)) + 3))
  have h3 : 13000 * n ^ 4 * Q (n * (n * (n * 1)) + 3) ≤ 13000 * n ^ 4 * (14633 * n ^ 3) :=
    Nat.mul_le_mul_left _ hq
  have e : 13000 * n ^ 4 * (14633 * n ^ 3) = 190229000 * n ^ 7 := by ring
  have h4 : 190229000 * n ^ 7 ≤ 200000000 * n ^ 7 := Nat.mul_le_mul_right _ (by norm_num)
  simp only [toK, bind_time, pure_time]
  omega

/-- Forward reduction runs in polynomial time, with polynomially bounded output. -/
theorem to_poly :
    ∃ q : Polynomial ℕ, ∀ (I : Instance) (X K : ℕ),
      (toK I X K).time ≤ q.eval (I.size + X + K) ∧
      (toK I X K).val.size ≤ q.eval (I.size + X + K) := by
  refine ⟨Polynomial.C 200000000 * Polynomial.X ^ 7, fun I X K => ?_⟩
  have h := toK_time_le I X K
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact ⟨h, le_trans (toK_size_le_time I X K) h⟩

end TrainNetwork.Answer
