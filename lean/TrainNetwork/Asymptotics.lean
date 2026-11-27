import Mathlib

namespace TrainNetwork

/-- `C · N^(a + b·m)` is `2^{o(N)}` as soon as `m² ≤ N`. -/
theorem pow_sqrt_subexp (C a b : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ N m : ℕ, n₀ ≤ N → m * m ≤ N →
      ((C * N ^ (a + b * m) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (N : ℝ)) := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ Real.log ((C : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) C])
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  -- the constant in front of `N^(3/4)`
  set K : ℝ := Real.log ((C : ℝ) + 1) + 4 * ((a : ℝ) + b) with hK
  have hK0 : 0 ≤ K := by positivity
  have hδ : 0 < ε * Real.log 2 := mul_pos hε hlog2
  -- threshold for the fourth root of `N`
  set T : ℝ := K / (ε * Real.log 2) + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ K / (ε * Real.log 2) := div_nonneg hK0 hδ.le
    linarith
  have hKT : K ≤ T * (ε * Real.log 2) := by
    have h1 : K / (ε * Real.log 2) * (ε * Real.log 2) = K := div_mul_cancel₀ K hδ.ne'
    nlinarith
  refine ⟨⌈T ^ 4⌉₊, ?_⟩
  intro N m hN hm
  have hNT : T ^ 4 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN1 : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ hT1) hNT
  have hNpos : (0 : ℝ) < N := by linarith
  -- `t` is the fourth root of `N`
  set t : ℝ := Real.sqrt (Real.sqrt N) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht4 : t ^ 4 = N := by
    have h : t ^ 4 = (t ^ 2) ^ 2 := by ring
    rw [h, ht2, Real.sq_sqrt hNpos.le]
  have hTt : T ≤ t := by
    refine not_lt.mp fun h => ?_
    have : t ^ 4 < T ^ 4 := pow_lt_pow_left₀ h ht0 (by norm_num)
    linarith
  have ht1 : 1 ≤ t := hT1.trans hTt
  have htpos : 0 < t := by linarith
  -- `m ≤ √N = t²`
  have hmt : (m : ℝ) ≤ t ^ 2 := by
    rw [ht2]
    apply Real.le_sqrt_of_sq_le
    have h : ((m * m : ℕ) : ℝ) ≤ N := by exact_mod_cast hm
    push_cast at h
    nlinarith
  -- `log N ≤ 4 t`
  have hlogN : Real.log N ≤ 4 * t := by
    have h := Real.log_le_sub_one_of_pos htpos
    rw [← ht4, Real.log_pow]
    push_cast
    linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  -- the key real inequality
  have key : Real.log ((C : ℝ) + 1) + ((a : ℝ) + b * m) * Real.log N
      ≤ Real.log 2 * (ε * N) := by
    have h1 : ((a : ℝ) + b * m) ≤ ((a : ℝ) + b) * t ^ 2 := by
      have : (b : ℝ) * m ≤ b * t ^ 2 := mul_le_mul_of_nonneg_left hmt hb0
      have : (a : ℝ) ≤ a * t ^ 2 := by nlinarith [one_le_pow₀ (n := 2) ht1]
      nlinarith
    have h2 : ((a : ℝ) + b * m) * Real.log N ≤ (((a : ℝ) + b) * t ^ 2) * (4 * t) :=
      mul_le_mul h1 hlogN hlogN0 (by positivity)
    have h3 : Real.log ((C : ℝ) + 1) ≤ Real.log ((C : ℝ) + 1) * t ^ 3 :=
      le_mul_of_one_le_right hC0 (one_le_pow₀ ht1)
    have h4 : K * t ^ 3 ≤ (t * (ε * Real.log 2)) * t ^ 3 :=
      mul_le_mul_of_nonneg_right
        (hKT.trans (mul_le_mul_of_nonneg_right hTt hδ.le)) (by positivity)
    calc Real.log ((C : ℝ) + 1) + ((a : ℝ) + b * m) * Real.log N
        ≤ Real.log ((C : ℝ) + 1) * t ^ 3 + (((a : ℝ) + b) * t ^ 2) * (4 * t) := add_le_add h3 h2
      _ = K * t ^ 3 := by rw [hK]; ring
      _ ≤ (t * (ε * Real.log 2)) * t ^ 3 := h4
      _ = Real.log 2 * (ε * t ^ 4) := by ring
      _ = Real.log 2 * (ε * N) := by rw [ht4]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  push_cast
  calc (C : ℝ) * (N : ℝ) ^ (a + b * m)
      ≤ ((C : ℝ) + 1) * (N : ℝ) ^ (a + b * m) := by
        gcongr
        linarith
    _ = Real.exp (Real.log ((C : ℝ) + 1) + ((a : ℝ) + b * m) * Real.log N) := by
        rw [Real.exp_add, Real.exp_log (by positivity), ← Real.rpow_natCast,
          Real.rpow_def_of_pos hNpos]
        push_cast
        ring_nf
    _ ≤ Real.exp (Real.log 2 * (ε * N)) := Real.exp_le_exp.mpr key

end TrainNetwork
