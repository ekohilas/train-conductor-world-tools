/-
A machine-checked reduction of the goal to a search-space question.

`solveWith gen` searches the candidate list produced by an arbitrary timed generator
`gen`. `quasipoly_of_generator` proves: if `gen` produces, in quasi-polynomial time, a
quasi-polynomially long list of small candidates that dominates every feasible
solution, then `solveWith gen` satisfies BOTH statements of `Goal.lean`.

No such generator is known. This file does NOT prove the goal; it states precisely
what is missing. For the exhaustive generator the list has length `2 ^ Θ(N)`.
-/
import TrainNetwork.TimeBound

namespace TrainNetwork

open TimeM

/-- Search the candidates produced by `gen` and return the cheapest feasible one.

The last step converts the winning edge list to a `Finset`; this is charged
`3 * n + n * n + 1` ticks, where `n` is the length of that list (3 per element to
measure it, and a quadratic number of comparisons to remove duplicates). -/
def solveWith (gen : Instance → TimeM (List Cand)) (I : Instance) :
    TimeM (Option Solution) := do
  let cells ← I.cellsT
  let ge ← I.gridEdgesT cells
  let ports ← I.portsT cells
  let cities ← I.citiesT cells
  let cs ← gen I
  let r ← foldlT (fun acc c => betterT I ge ports cities acc c) none cs
  let n ← lengthT (match r with
    | some (c, _) => c.edges
    | none => [])
  tickN (n * n + 1)
  pure (r.map (fun x => x.1.toSolution))

theorem solveWith_val (gen : Instance → TimeM (List Cand)) (I : Instance) :
    (solveWith gen I).val = solveFrom I (gen I).val := by
  simp only [solveWith, bind_val, pure_val, Instance.cellsT_val, Instance.gridEdgesT_val,
    Instance.portsT_val, Instance.citiesT_val, foldlT_val, betterT_val]
  rfl

/-- Correctness of `solveWith` on instances where the generated list is complete. -/
theorem solveWith_correct (gen : Instance → TimeM (List Cand)) (I : Instance)
    (h : Complete I (gen I).val) :
    match (solveWith gen I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I := by
  rw [solveWith_val]
  exact solveFrom_correct I _ h

/-- Running time of `solveWith`: the generator, plus a polynomial per candidate. -/
theorem solveWith_time_le (gen : Instance → TimeM (List Cand)) (I : Instance)
    (hsmall : ∀ c ∈ (gen I).val, Small (32 * I.size) c) :
    (solveWith gen I).time ≤
      (gen I).time + ((gen I).val.length + 1) * (32 * I.size) ^ 20 := by
  have hm : 32 * I.size ≤ 32 * I.size := le_rfl
  have h16 := m_ge hm
  have hWH := I.WH_lt_size
  have hcells : I.cellsL.length ≤ 32 * I.size := by
    rw [Instance.length_cellsL]
    omega
  have hge : 2 * I.gridEdgesL.length + 1 ≤ 32 * I.size := by
    have := @Instance.length_gridEdgesL_le I
    omega
  have hpl : I.portsL.length ≤ 32 * I.size := by
    rw [Instance.length_portsL]
    have := I.card_ports_lt
    omega
  have hcl : I.citiesL.length ≤ 32 * I.size := by
    rw [Instance.length_citiesL]
    have := I.card_cities_lt
    omega
  have t1 := I.cellsT_time_le hm
  have t2 := I.gridEdgesT_time_le hm I.cellsL hcells
  have t3 := I.portsT_time_le hm I.cellsL hcells
  have t4 := I.citiesT_time_le hm I.cellsL hcells
  have t5 : (foldlT (fun acc c => betterT I I.gridEdgesL I.portsL I.citiesL acc c) none
      (gen I).val).time ≤ (gen I).val.length * ((32 * I.size) ^ 19 + 3) :=
    foldlT_time_le _ _ _ none
      (fun b c hc => betterT_time_le hm _ hge _ _ hpl hcl b c (hsmall c hc))
  -- the winner is one of the candidates, so its edge list is short
  have hwin : (match best I (gen I).val with
      | some (c, _) => c.edges
      | none => []).length ≤ 32 * I.size := by
    have hg := best_good I (gen I).val
    cases hb : best I (gen I).val with
    | none => simp
    | some r =>
      obtain ⟨b, cb⟩ := r
      rw [hb] at hg
      have := (hsmall b hg.1).edges
      simp only
      omega
  have hfold : (gen I).val.foldl (fun b a => better I b a) none = best I (gen I).val := rfl
  simp only [solveWith, bind_time, Instance.cellsT_val, Instance.gridEdgesT_val,
    Instance.portsT_val, Instance.citiesT_val, foldlT_val, betterT_val, lengthT_time,
    lengthT_val, tickN_time, pure_time, hfold]
  set w := (match best I (gen I).val with
      | some (c, _) => c.edges
      | none => []).length with hw
  set M := 32 * I.size with hM
  -- polynomial pieces, all below `M ^ 19` or `M ^ 20`
  have p1 : M ^ 4 ≤ M ^ 19 := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : M ^ 3 ≤ M ^ 19 := Nat.pow_le_pow_right (by omega) (by omega)
  have pw : 3 * w + (w * w + 1) ≤ M ^ 19 := by
    have h1 : w * w ≤ M * M := Nat.mul_le_mul hwin hwin
    have h2 : M * M = M ^ 2 := by ring
    have h3 : 3 * w + 1 ≤ M ^ 2 := lin_le_sq h16 (by omega)
    have h4 : M ^ 2 + M ^ 2 ≤ M ^ 3 := lin_le_pow h16 (by omega)
    omega
  have p19 : (gen I).val.length * (M ^ 19 + 3) ≤ (gen I).val.length * M ^ 20 := by
    refine Nat.mul_le_mul_left _ ?_
    have := one_le_pow' h16 19
    exact lin_le_pow h16 (by omega)
  have p20 : 5 * M ^ 19 ≤ M ^ 20 := lin_le_pow h16 (by omega)
  have e : ((gen I).val.length + 1) * M ^ 20 = (gen I).val.length * M ^ 20 + M ^ 20 := by
    ring
  rw [e]
  omega

/-- **Reduction of the goal.** Suppose a generator `gen` produces, on every instance
within the bounds, a list of candidates that
* consists of small candidates (their lists have length at most `32 * size`),
* dominates every feasible solution (`Complete`),
* is produced in quasi-polynomial time and has quasi-polynomial length.
Then `solveWith gen` satisfies both statements of `Goal.lean`. -/
theorem quasipoly_of_generator (gen : Instance → TimeM (List Cand)) (c₀ d₀ : ℕ)
    (hsmall : ∀ I : Instance, ∀ c ∈ (gen I).val, Small (32 * I.size) c)
    (hcomplete : ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      Complete I (gen I).val)
    (htime : ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (gen I).time ≤ 2 ^ (c₀ * (Nat.log 2 I.size + 1) ^ d₀))
    (hlength : ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (gen I).val.length ≤ 2 ^ (c₀ * (Nat.log 2 I.size + 1) ^ d₀)) :
    (∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      match (solveWith gen I).val with
      | some σ => IsOptimal I σ
      | none => ¬ ∃ σ : Solution, σ.Feasible I) ∧
    ∃ c d : ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (solveWith gen I).time ≤ 2 ^ (c * (Nat.log 2 I.size + 1) ^ d) := by
  refine ⟨fun I hP hC => solveWith_correct gen I (hcomplete I hP hC), c₀ + 122, d₀ + 1, ?_⟩
  intro I hP hC
  set L := Nat.log 2 I.size + 1 with hL
  have hL1 : 1 ≤ L := Nat.succ_le_succ (Nat.zero_le _)
  have hn : I.size ≤ 2 ^ L := (Nat.lt_pow_succ_log_self (by norm_num) I.size).le
  -- `M ^ 20 ≤ 2 ^ (120 * L)`
  have hM : (32 * I.size) ^ 20 ≤ 2 ^ (120 * L) := by
    calc (32 * I.size) ^ 20 ≤ (2 ^ 5 * 2 ^ L) ^ 20 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul (by norm_num) hn) 20
      _ = 2 ^ (20 * (5 + L)) := by rw [← pow_add, ← pow_mul, mul_comm]
      _ ≤ 2 ^ (120 * L) := two_pow_mono (by omega)
  have ht := htime I hP hC
  have hl := hlength I hP hC
  rw [← hL] at ht hl
  set Q := 2 ^ (c₀ * L ^ d₀) with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have h1 : (solveWith gen I).time ≤ Q + (Q + 1) * 2 ^ (120 * L) :=
    (solveWith_time_le gen I (hsmall I)).trans
      (Nat.add_le_add ht (Nat.mul_le_mul (Nat.add_le_add_right hl 1) hM))
  have hB1 : 1 ≤ 2 ^ (120 * L) := Nat.one_le_two_pow
  have h2 : Q + (Q + 1) * 2 ^ (120 * L) ≤ 4 * (Q * 2 ^ (120 * L)) := by
    have h3 : Q ≤ Q * 2 ^ (120 * L) := Nat.le_mul_of_pos_right _ hB1
    have h4 : (Q + 1) * 2 ^ (120 * L) = Q * 2 ^ (120 * L) + 2 ^ (120 * L) := by ring
    have h5 : 2 ^ (120 * L) ≤ Q * 2 ^ (120 * L) := Nat.le_mul_of_pos_left _ hQ1
    omega
  have h3 : 4 * (Q * 2 ^ (120 * L)) = 2 ^ (2 + (c₀ * L ^ d₀ + 120 * L)) := by
    rw [pow_add, pow_add, ← hQ]
    norm_num
  have hpow : L ^ d₀ ≤ L ^ (d₀ + 1) := Nat.pow_le_pow_right hL1 (Nat.le_succ _)
  have hLp : L ≤ L ^ (d₀ + 1) := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (d₀ + 1) := Nat.pow_le_pow_right hL1 (by omega)
  have hexp : 2 + (c₀ * L ^ d₀ + 120 * L) ≤ (c₀ + 122) * L ^ (d₀ + 1) := by
    have a1 : c₀ * L ^ d₀ ≤ c₀ * L ^ (d₀ + 1) := Nat.mul_le_mul_left _ hpow
    have a2 : 120 * L ≤ 120 * L ^ (d₀ + 1) := Nat.mul_le_mul_left _ hLp
    have a3 : 1 ≤ L ^ (d₀ + 1) := Nat.one_le_pow _ _ hL1
    have e : (c₀ + 122) * L ^ (d₀ + 1) =
        c₀ * L ^ (d₀ + 1) + 120 * L ^ (d₀ + 1) + 2 * L ^ (d₀ + 1) := by ring
    omega
  calc (solveWith gen I).time ≤ Q + (Q + 1) * 2 ^ (120 * L) := h1
    _ ≤ 4 * (Q * 2 ^ (120 * L)) := h2
    _ = 2 ^ (2 + (c₀ * L ^ d₀ + 120 * L)) := h3
    _ ≤ 2 ^ ((c₀ + 122) * L ^ (d₀ + 1)) := two_pow_mono hexp

end TrainNetwork
