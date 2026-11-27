/-
Running time of `Answer.solve`.

Let `N = W · H + 1` be the input size and `m = min W H` the number of cells of a layer
of the sweep. With at most 10 ports and at most 40 cities:

* `dpRun_time_le`: one run of the certificate DP takes at most `N ^ (60 + 90 · m)` steps
  (there are at most `N ^ 45` labels per cell, hence at most `N ^ (45 · m)` layer states,
  and the layered DP is quadratic in the number of layer states);
* `Answer.solve_time_le`: the whole algorithm takes at most `2 ^ 420 · N ^ (60 + 90 · m)`
  steps (at most `(2 ^ 40 + 1) ^ 10` choice combinations, one DP run for each);
* `Answer.subexp`: since `m · m ≤ N`, this is `2 ^ O(√N · log N) = 2 ^ o(N)`.

The constants are generous; no attempt is made to make them tight. Bounds of the form
`a ≤ N ^ i` are combined with the small calculus `pw_*` below (using `2 ≤ N`).
-/
import TrainNetwork.Correct
import TrainNetwork.Asymptotics

namespace TrainNetwork

open TimeM

/-! ### A small calculus for bounds of the form `a ≤ N ^ i` -/

section Pw

variable {N : ℕ}

theorem pw_mono (hN : 2 ≤ N) {a i : ℕ} (k : ℕ) (ha : a ≤ N ^ i) (h : i ≤ k) : a ≤ N ^ k :=
  ha.trans (Nat.pow_le_pow_right (by omega) h)

theorem pw_mul (hN : 2 ≤ N) {a b i j : ℕ} (k : ℕ) (ha : a ≤ N ^ i) (hb : b ≤ N ^ j)
    (h : i + j ≤ k) : a * b ≤ N ^ k := by
  refine pw_mono hN k ?_ h
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

theorem pw_add (hN : 2 ≤ N) {a b i j : ℕ} (k : ℕ) (ha : a ≤ N ^ i) (hb : b ≤ N ^ j)
    (hi : i < k) (hj : j < k) : a + b ≤ N ^ k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 := pw_mono hN k ha (by omega)
  have h2 := pw_mono hN k hb (by omega)
  rw [pow_succ]
  nlinarith

theorem pw_const (hN : 2 ≤ N) {c : ℕ} (k : ℕ) (hc : c ≤ 2 ^ k) : c ≤ N ^ k :=
  hc.trans (Nat.pow_le_pow_left hN k)

theorem pw_pow (hN : 2 ≤ N) {a i : ℕ} (k e : ℕ) (ha : a ≤ N ^ i) (h : i * e ≤ k) :
    a ^ e ≤ N ^ k := by
  refine pw_mono hN k ?_ h
  rw [pow_mul]
  exact Nat.pow_le_pow_left ha e

theorem pw_self {a : ℕ} (ha : a ≤ N) : a ≤ N ^ 1 := by simpa using ha

/-- A sum of at most `2 ^ j` terms, each at most `N ^ i`. -/
theorem pw_sum (hN : 2 ≤ N) {s c i : ℕ} (k j : ℕ) (hs : s ≤ c * N ^ i) (hc : c ≤ 2 ^ j)
    (h : j + i ≤ k) : s ≤ N ^ k :=
  hs.trans (pw_mul hN k (pw_const hN j hc) le_rfl h)

end Pw

/-! ### Basic facts about instances -/

theorem card_le_of_inBounds (I : Instance) (s : Finset Cell)
    (h : ∀ x ∈ s, x.1 < I.W ∧ x.2 < I.H) : s.card ≤ I.W * I.H := by
  have hsub : s ⊆ Finset.range I.W ×ˢ Finset.range I.H := by
    intro x hx
    simp [Finset.mem_product, h x hx]
  calc s.card ≤ (Finset.range I.W ×ˢ Finset.range I.H).card := Finset.card_le_card hsub
    _ = I.W * I.H := by simp

theorem scanCost_le (I : Instance) : scanCost I ≤ 9 * (I.W * I.H) + 4 := by
  have h1 := card_le_of_inBounds I I.blocked I.blocked_inBounds
  have h2 := card_le_of_inBounds I I.ports I.ports_inBounds
  have h3 := card_le_of_inBounds I I.cities I.cities_inBounds
  unfold scanCost
  omega

theorem length_cellsT (I : Instance) : (cellsT I).val.length = I.W * I.H := by
  rw [cellsT_val]
  exact (List.length_product _ _).trans (by simp)

theorem length_portsL (I : Instance) : (portsL I).length = I.ports.card := by
  have h := List.toFinset_card_of_nodup (nodup_portsL I)
  rw [toFinset_portsL] at h
  exact h.symm

theorem length_citiesL (I : Instance) : (citiesL I).length = I.cities.card := by
  have h := List.toFinset_card_of_nodup (nodup_scanT I I.cities)
  rw [toFinset_scanT I.cities_inBounds] at h
  exact h.symm

theorem dims_pos (I : Instance) : 1 ≤ I.W ∧ 1 ≤ I.H := by
  have hpos : 0 < I.cities.card := lt_of_lt_of_le I.k_pos I.k_le_cities
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  have := I.cities_inBounds c hc
  omega

theorem size_ge_two (I : Instance) : 2 ≤ I.size := by
  obtain ⟨h1, h2⟩ := dims_pos I
  have : 1 ≤ I.W * I.H := Nat.mul_pos h1 h2
  unfold Instance.size
  omega

/-- Facts about the sweep direction: a layer is the short side. -/
theorem nm_facts (I : Instance) :
    mOf (decide (I.H ≤ I.W)) I.W I.H ≤ nOf (decide (I.H ≤ I.W)) I.W I.H ∧
    nOf (decide (I.H ≤ I.W)) I.W I.H * mOf (decide (I.H ≤ I.W)) I.W I.H = I.W * I.H ∧
    1 ≤ mOf (decide (I.H ≤ I.W)) I.W I.H := by
  obtain ⟨h1, h2⟩ := dims_pos I
  by_cases h : I.H ≤ I.W
  · rw [decide_eq_true h]
    exact ⟨h, rfl, h2⟩
  · rw [decide_eq_false h]
    exact ⟨by show I.W ≤ I.H; omega, Nat.mul_comm _ _, h1⟩

theorem mOf_sq_le (I : Instance) :
    mOf (decide (I.H ≤ I.W)) I.W I.H * mOf (decide (I.H ≤ I.W)) I.W I.H ≤ I.size := by
  obtain ⟨h1, h2, h3⟩ := nm_facts I
  have := Nat.mul_le_mul_right (mOf (decide (I.H ≤ I.W)) I.W I.H) h1
  unfold Instance.size
  omega

theorem mOf_le_size (I : Instance) : mOf (decide (I.H ≤ I.W)) I.W I.H ≤ I.size := by
  obtain ⟨h1, h2, h3⟩ := nm_facts I
  have := Nat.le_mul_of_pos_left (mOf (decide (I.H ≤ I.W)) I.W I.H) (lt_of_lt_of_le h3 h1)
  unfold Instance.size
  omega

theorem nOf_le_size (I : Instance) : nOf (decide (I.H ≤ I.W)) I.W I.H ≤ I.size := by
  obtain ⟨h1, h2, h3⟩ := nm_facts I
  have := Nat.le_mul_of_pos_right (nOf (decide (I.H ≤ I.W)) I.W I.H) h3
  unfold Instance.size
  omega


/-! ### One run of the certificate DP -/

theorem four_mul_add_two_le {N : ℕ} (hN : 2 ≤ N) : 4 * N + 2 ≤ N ^ 4 :=
  pw_add hN 4 (pw_mul hN 3 (pw_const hN 2 (by norm_num)) (pw_self le_rfl) (by omega))
    (pw_const hN 1 (by norm_num)) (by omega) (by omega)

theorem labs_length_succ_le {N : ℕ} (hN : 2 ≤ N) (q : ℕ) (hq : q ≤ 10) :
    (labsT q N).val.length + 1 ≤ N ^ 45 := by
  have h1 := length_labsT_le q N
  have h5 : (4 * N + 2) ^ q ≤ N ^ 40 :=
    (Nat.pow_le_pow_right (by omega) hq).trans
      (pw_pow hN 40 10 (four_mul_add_two_le hN) (by norm_num))
  have h6 : 16 * (4 * N + 2) ^ q ≤ N ^ 44 :=
    pw_mul hN 44 (pw_const hN 4 (by norm_num)) h5 (by omega)
  have h7 : 16 * (4 * N + 2) ^ q + 1 ≤ N ^ 45 :=
    pw_add hN 45 h6 (pw_const hN 0 (by norm_num)) (by omega) (by omega)
  exact (Nat.succ_le_succ h1).trans h7

theorem labsT_time_pw {N : ℕ} (hN : 2 ≤ N) (q : ℕ) (hq : q ≤ 10) :
    (labsT q N).time ≤ N ^ 50 := by
  have h := labsT_time_le q N
  have h5 : (4 * N + 2) ^ q ≤ N ^ 40 :=
    (Nat.pow_le_pow_right (by omega) hq).trans
      (pw_pow hN 40 10 (four_mul_add_two_le hN) (by norm_num))
  have h6 : (8 * q + 84) * (4 * N + 2) ^ q ≤ N ^ 48 :=
    pw_mul hN 48 (pw_const hN 8 (by omega)) h5 (by omega)
  have h7 : 16 * N + q + 18 ≤ N ^ 6 := by
    have h8 : 16 * N + q + 18 ≤ 32 * N := by omega
    have h9 : 32 * N ≤ N ^ 6 :=
      pw_mul hN 6 (pw_const hN 5 (by norm_num)) (pw_self le_rfl) (by omega)
    exact h8.trans h9
  exact h.trans (pw_add hN 50 h7 h6 (by omega) (by omega))

/-- The running time of `dpRun`, step by step. -/
theorem dpRun_time_eq (I : Instance) (pd : PD) (β : ℕ) :
    (dpRun I pd β).time =
      pd.length + 6 + ((labsT pd.length (I.W * I.H + 1)).time +
        (mOf (decide (I.H ≤ I.W)) I.W I.H + 1 +
          ((tsections (List.replicate (mOf (decide (I.H ≤ I.W)) I.W I.H)
              (labsT pd.length (I.W * I.H + 1)).val)).time +
            (nOf (decide (I.H ≤ I.W)) I.W I.H + mOf (decide (I.H ≤ I.W)) I.W I.H + 2 +
              ((tmapM (fun i => tmapM (fun j => do
                    tick
                    kindT I pd (emb (decide (I.H ≤ I.W)) i j))
                  (List.range (mOf (decide (I.H ≤ I.W)) I.W I.H)))
                (List.range (nOf (decide (I.H ≤ I.W)) I.W I.H))).time +
                (LayerDP.run (gSelf β (I.W * I.H + 1) (dWOf (decide (I.H ≤ I.W))))
                  (gLink (dAOf (decide (I.H ≤ I.W))))
                  (List.replicate (mOf (decide (I.H ≤ I.W)) I.W I.H)
                    (labsT pd.length (I.W * I.H + 1)).val).sections
                  (layersOf (nOf (decide (I.H ≤ I.W)) I.W I.H)
                    (mOf (decide (I.H ≤ I.W)) I.W I.H)
                    (fun i j => kindOf I pd (emb (decide (I.H ≤ I.W)) i j)))).time))))) := by
  simp only [dpRun, bind_time, tickN_time, tsections_val, tmapM_val]
  rfl

/-- Running time of one DP run with at most 10 ports and at most 40 demands per port:
at most `N ^ (60 + 90 · m)`, where `N = W · H + 1` is the input size and `m = min W H`
is the number of cells of a layer. -/
theorem dpRun_time_le (I : Instance) (pd : PD) (β : ℕ) (hq : pd.length ≤ 10)
    (hc : ∀ e ∈ pd, e.2.length ≤ 40) :
    (dpRun I pd β).time ≤ I.size ^ (60 + 90 * mOf (decide (I.H ≤ I.W)) I.W I.H) := by
  have hN : 2 ≤ I.W * I.H + 1 := size_ge_two I
  have hm : mOf (decide (I.H ≤ I.W)) I.W I.H ≤ I.W * I.H + 1 := mOf_le_size I
  have hn : nOf (decide (I.H ≤ I.W)) I.W I.H ≤ I.W * I.H + 1 := nOf_le_size I
  have hsc : scanCost I ≤ 9 * (I.W * I.H + 1) := by
    have := scanCost_le I
    omega
  show (dpRun I pd β).time ≤ (I.W * I.H + 1) ^ _
  rw [dpRun_time_eq]
  set N := I.W * I.H + 1 with hNdef
  set m := mOf (decide (I.H ≤ I.W)) I.W I.H with hmdef
  set n := nOf (decide (I.H ≤ I.W)) I.W I.H with hndef
  set labs := (labsT pd.length N).val with hlabs
  -- the labels and the layer states
  have hLab : labs.length + 1 ≤ N ^ 45 := labs_length_succ_le hN _ hq
  have tLab : (labsT pd.length N).time ≤ N ^ 50 := labsT_time_pw hN _ hq
  have hCn : (List.replicate m labs).sections.length ≤ N ^ (45 * m) := by
    have h := length_sections_le (List.replicate m labs)
    rw [prodSucc_replicate] at h
    exact h.trans (pw_pow hN _ m hLab le_rfl)
  have tSec : (tsections (List.replicate m labs)).time ≤ N ^ (4 + 45 * m) := by
    have h := tsections_time_le (List.replicate m labs)
    rw [prodSucc_replicate, List.length_replicate] at h
    have h2 : 8 * m * (labs.length + 1) ^ m ≤ N ^ (4 + 45 * m) :=
      pw_mul hN _
        (pw_mul hN 4 (pw_const hN 3 (by norm_num)) (pw_self hm) (by omega))
        (pw_pow hN (45 * m) m hLab le_rfl) (by omega)
    exact h.trans h2
  -- the kinds
  have hcK : 1 + (10 * scanCost I + 16 + pd.length * (4 * 40 + 8)) + 3 ≤ N ^ 13 := by
    have h1 : 1 + (10 * scanCost I + 16 + pd.length * (4 * 40 + 8)) + 3 ≤ 90 * N + 1700 := by
      omega
    have h2 : 90 * N + 1700 ≤ N ^ 13 :=
      pw_add hN 13
        (pw_mul hN 8 (pw_const hN 7 (by norm_num)) (pw_self le_rfl) (by omega))
        (pw_const hN 11 (by norm_num)) (by omega) (by omega)
    exact h1.trans h2
  have tLay : (tmapM (fun i => tmapM (fun j => do
        tick
        kindT I pd (emb (decide (I.H ≤ I.W)) i j))
      (List.range m)) (List.range n)).time ≤ N ^ 17 := by
    have hin : ∀ i ∈ List.range n,
        (tmapM (fun j => (do
            tick
            kindT I pd (emb (decide (I.H ≤ I.W)) i j) : TimeM Kind)) (List.range m)).time ≤
          m * (1 + (10 * scanCost I + 16 + pd.length * (4 * 40 + 8)) + 3) := by
      intro i _
      have h := tmapM_time_le (fun j => (do
            tick
            kindT I pd (emb (decide (I.H ≤ I.W)) i j) : TimeM Kind))
        (List.range m) (1 + (10 * scanCost I + 16 + pd.length * (4 * 40 + 8))) (by
          intro j _
          have := kindT_time I pd (emb (decide (I.H ≤ I.W)) i j) 40 hc
          simp only [bind_time, tick_time]
          omega)
      rwa [List.length_range] at h
    have h := tmapM_time_le _ (List.range n) _ hin
    rw [List.length_range] at h
    have h2 : n * (m * (1 + (10 * scanCost I + 16 + pd.length * (4 * 40 + 8)) + 3) + 3) ≤
        N ^ 17 :=
      pw_mul hN 17 (pw_self hn)
        (pw_add hN 15 (pw_mul hN 14 (pw_self hm) hcK (by omega)) (pw_const hN 2 (by norm_num))
          (by omega) (by omega)) (by omega)
    exact h.trans h2
  -- the layered DP
  have hlayers : ∀ k ∈ layersOf n m (fun i j => kindOf I pd (emb (decide (I.H ≤ I.W)) i j)),
      k.length = m ∧ ∀ k' ∈ k, k'.pp.length ≤ 10 := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hk
    refine ⟨by simp, ?_⟩
    intro k' hk'
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk'
    exact (kindOf_pp_length I pd _).le.trans hq
  have tRun := LayerDP.run_time_le
    (selfT := gSelf β N (dWOf (decide (I.H ≤ I.W)))) (linkT := gLink (dAOf (decide (I.H ≤ I.W))))
    (List.replicate m labs).sections
    (m + 1 + m * (4 * m + 14 + 3 * cellBound 10)) (m + 1 + m * (4 * m + 8 + cellBound 10))
    (layersOf n m (fun i j => kindOf I pd (emb (decide (I.H ≤ I.W)) i j)))
    (by
      intro k hk s _
      obtain ⟨hl, hpp⟩ := hlayers k hk
      have h := gSelf_time_le β N (dWOf (decide (I.H ≤ I.W))) k s 10 hpp
      rwa [hl] at h)
    (by
      intro k hk k' _ s _ s' _
      obtain ⟨hl, hpp⟩ := hlayers k hk
      have h := gLink_time_le (dAOf (decide (I.H ≤ I.W))) k s k' s' 10 hpp
      rwa [hl] at h)
  rw [layersOf_length] at tRun
  have hcb : cellBound 10 = 1008 := rfl
  rw [hcb] at tRun
  have hm1 : m + 1 ≤ N ^ 2 :=
    pw_add hN 2 (pw_self hm) (pw_const hN 0 (by norm_num)) (by omega) (by omega)
  have h4m : 4 * m ≤ N ^ 3 := pw_mul hN 3 (pw_const hN 2 (by norm_num)) (pw_self hm) (by omega)
  have hcS : m + 1 + m * (4 * m + 14 + 3 * 1008) ≤ N ^ 15 :=
    pw_add hN 15 hm1
      (pw_mul hN 14 (pw_self hm)
        (pw_add hN 13 (pw_add hN 5 h4m (pw_const hN 4 (by norm_num)) (by omega) (by omega))
          (pw_const hN 12 (by norm_num)) (by omega) (by omega)) (by omega))
      (by omega) (by omega)
  have hcL : m + 1 + m * (4 * m + 8 + 1008) + 4 ≤ N ^ 16 :=
    pw_add hN 16
      (pw_add hN 15 hm1
        (pw_mul hN 14 (pw_self hm)
          (pw_add hN 13 (pw_add hN 5 h4m (pw_const hN 4 (by norm_num)) (by omega) (by omega))
            (pw_const hN 12 (by norm_num)) (by omega) (by omega)) (by omega))
        (by omega) (by omega))
      (pw_const hN 2 (by norm_num)) (by omega) (by omega)
  have hRun : n * ((List.replicate m labs).sections.length *
      (m + 1 + m * (4 * m + 14 + 3 * 1008) + (List.replicate m labs).sections.length *
        (m + 1 + m * (4 * m + 8 + 1008) + 4) + 6) + 2) +
      3 * (List.replicate m labs).sections.length + 1 ≤ N ^ (23 + 90 * m) :=
    pw_add hN _
      (pw_add hN (22 + 90 * m)
        (pw_mul hN (21 + 90 * m) (pw_self hn)
          (pw_add hN (20 + 90 * m)
            (pw_mul hN (19 + 90 * m) hCn
              (pw_add hN (19 + 45 * m)
                (pw_add hN (18 + 45 * m) hcS (pw_mul hN (16 + 45 * m) hCn hcL (by omega))
                  (by omega) (by omega))
                (pw_const hN 3 (by norm_num)) (by omega) (by omega))
              (by omega))
            (pw_const hN 1 (by norm_num)) (by omega) (by omega))
          (by omega))
        (pw_mul hN (2 + 45 * m) (pw_const hN 2 (by norm_num)) hCn (by omega))
        (by omega) (by omega))
      (pw_const hN 0 (by norm_num)) (by omega) (by omega)
  -- summing up
  have e1 : pd.length + 6 ≤ N ^ (50 + 90 * m) := pw_mono hN _ (pw_const hN 4 (by omega)) (by omega)
  have e2 := pw_mono hN (50 + 90 * m) tLab (by omega)
  have e3 := pw_mono hN (50 + 90 * m) hm1 (by omega)
  have e4 := pw_mono hN (50 + 90 * m) tSec (by omega)
  have e5 : n + m + 2 ≤ N ^ (50 + 90 * m) :=
    pw_mono hN _ (pw_add hN 4 (pw_add hN 2 (pw_self hn) (pw_self hm) (by omega) (by omega))
      (pw_const hN 1 (by norm_num)) (by omega) (by omega)) (by omega)
  have e6 := pw_mono hN (50 + 90 * m) tLay (by omega)
  have e7 := pw_mono hN (50 + 90 * m) (tRun.trans hRun) (by omega)
  refine pw_sum hN _ 3 (c := 7) (i := 50 + 90 * m) ?_ (by norm_num) (by omega)
  omega


/-! ### The steps of `solve` other than the DP runs -/

theorem cellsT_time_le (I : Instance) :
    (cellsT I).time ≤ 5 * (I.W * I.H) + 5 * I.W + I.H + 5 := by
  have hin : ∀ x ∈ List.range I.W,
      (tmapM (fun y => (do
          tick
          pure (x, y) : TimeM Cell)) (List.range I.H)).time ≤ I.H * 4 := by
    intro x _
    have h := tmapM_time_le (fun y => (do
          tick
          pure (x, y) : TimeM Cell)) (List.range I.H) 1 (by simp)
    rwa [List.length_range] at h
  have h := tmapM_time_le _ (List.range I.W) _ hin
  rw [List.length_range] at h
  simp only [cellsT, bind_time, tickN_time, pure_time]
  have h2 : I.W * (I.H * 4 + 3) = 4 * (I.W * I.H) + 3 * I.W := by ring
  omega

theorem scanT_time_le (s : Finset Cell) (cells : List Cell) :
    (scanT s cells).time ≤ cells.length * (3 * s.card + 4) := by
  unfold scanT
  exact tfilterM_time_le _ cells (3 * s.card + 1) (fun a _ => by simp)

theorem distsT_time_le (I : Instance) (cities : List Cell) (p : Cell) (D : ℕ)
    (hD : ∀ c, (dpRun I [(p, [(c, 0)])] 4).time ≤ D) :
    (distsT I cities p).time ≤ cities.length * (D + 12) + (2 * cities.length + 1) := by
  have h := tmapM_time_le (fun c => (do
      let d ← distT I p c
      tick
      pure (d.map (fun g => (c, g))) : TimeM (Option (Cell × ℕ)))) cities (D + 9) (by
    intro c _
    have := hD c
    simp only [distT, bind_time, tickN_time, tick_time, pure_time]
    omega)
  have h5 : D + 9 + 3 = D + 12 := rfl
  rw [h5] at h
  simp only [distsT, bind_time, tickN_time, pure_time]
  omega

theorem length_distsT_le (I : Instance) (cities : List Cell) (p : Cell) :
    (distsT I cities p).val.length ≤ cities.length := by
  rw [distsT_val]
  exact List.length_filterMap_le _ _

theorem nearRowT_time (S : List (Cell × ℕ)) (g : ℕ) (fin : List (Cell × ℕ)) :
    (nearRowT S g fin).time = fin.length * (4 * S.length + 4) := by
  induction fin with
  | nil => simp [nearRowT]
  | cons e fin ih =>
      simp only [nearRowT, bind_time, tickN_time, pure_time, ih, List.length_cons]
      ring

theorem nearAllT_time (S fin rest : List (Cell × ℕ)) :
    (nearAllT S fin rest).time = rest.length * (2 + fin.length * (4 * S.length + 4)) := by
  induction rest with
  | nil => simp [nearAllT]
  | cons e rest ih =>
      simp only [nearAllT, bind_time, tickN_time, pure_time, ih, nearRowT_time,
        List.length_cons]
      ring

theorem nearT_time (k : ℕ) (fin S : List (Cell × ℕ)) :
    (nearT k fin S).time =
      S.length + 2 + S.length * (2 + fin.length * (4 * S.length + 4)) := by
  simp only [nearT, bind_time, tickN_time, pure_time, nearAllT_time]
  ring

theorem nearT_time_le (k : ℕ) (fin S : List (Cell × ℕ)) (hf : fin.length ≤ 40)
    (hS : S.length ≤ 40) : (nearT k fin S).time ≤ 262522 := by
  rw [nearT_time]
  have h1 : fin.length * (4 * S.length + 4) ≤ 40 * 164 := Nat.mul_le_mul hf (by omega)
  have h2 : S.length * (2 + fin.length * (4 * S.length + 4)) ≤ 40 * (2 + 40 * 164) :=
    Nat.mul_le_mul hS (by omega)
  omega

theorem length_choicesT_le (I : Instance) (cities : List Cell) (p : Cell)
    (hcit : cities.length ≤ 40) : (choicesT I cities p).val.length ≤ 2 ^ 40 := by
  have hfl : (distsT I cities p).val.length ≤ 40 := (length_distsT_le I cities p).trans hcit
  simp only [choicesT, bind_val, tmapM_val, tfilterM_val, tsublists_val, List.length_map]
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_sublists']
  exact Nat.pow_le_pow_right (by norm_num) hfl

theorem choicesT_time_le (I : Instance) (cities : List Cell) (p : Cell) (D : ℕ)
    (hcit : cities.length ≤ 40) (hD : ∀ c, (dpRun I [(p, [(c, 0)])] 4).time ≤ D) :
    (choicesT I cities p).time ≤ 40 * D + 2 ^ 60 := by
  have hfl : (distsT I cities p).val.length ≤ 40 := (length_distsT_le I cities p).trans hcit
  have t1 := distsT_time_le I cities p D hD
  have t2 := tsublists_time_le (distsT I cities p).val
  have hsub : (distsT I cities p).val.sublists'.length = 2 ^ (distsT I cities p).val.length :=
    List.length_sublists' _
  have hpow : 2 ^ (distsT I cities p).val.length ≤ 2 ^ 40 :=
    Nat.pow_le_pow_right (by norm_num) hfl
  have t3 := tfilterM_time_le (nearT I.k (distsT I cities p).val)
    (distsT I cities p).val.sublists' 262522 (by
      intro S hS
      exact nearT_time_le _ _ _ hfl ((List.mem_sublists'.mp hS).length_le.trans hfl))
  have hgood : ((distsT I cities p).val.sublists'.filter
      (fun S => (nearT I.k (distsT I cities p).val S).val)).length ≤ 2 ^ 40 :=
    (List.length_filter_le _ _).trans (hsub.le.trans hpow)
  have t4 := tmapM_time_le (fun S => (do
      tick
      pure (p, S) : TimeM (Cell × List (Cell × ℕ))))
    ((distsT I cities p).val.sublists'.filter
      (fun S => (nearT I.k (distsT I cities p).val S).val)) 1 (by simp)
  simp only [choicesT, bind_time, tsublists_val, tfilterM_val]
  rw [hsub] at t3
  have h1 : cities.length * (D + 12) ≤ 40 * (D + 12) := Nat.mul_le_mul_right _ hcit
  have h3 : 2 ^ (distsT I cities p).val.length * (262522 + 3) ≤ 2 ^ 40 * (262522 + 3) :=
    Nat.mul_le_mul_right _ hpow
  omega

theorem prodSucc_le {α : Type} (L : List (List α)) (c : ℕ) (h : ∀ l ∈ L, l.length ≤ c) :
    prodSucc L ≤ (c + 1) ^ L.length := by
  induction L with
  | nil => simp [prodSucc]
  | cons l L ih =>
      have h1 := h l (by simp)
      have h2 := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
      have hP : prodSucc (l :: L) = (l.length + 1) * prodSucc L := by simp [prodSucc]
      rw [hP, List.length_cons, pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul h2 (by omega)

theorem prodSucc_choices_le (I : Instance) (cities ports : List Cell)
    (hcit : cities.length ≤ 40) (hp : ports.length ≤ 10) :
    prodSucc (ports.map (fun p => (choicesT I cities p).val)) ≤ (2 ^ 40 + 1) ^ 10 := by
  have h := prodSucc_le (ports.map (fun p => (choicesT I cities p).val)) (2 ^ 40) (by
    intro l hl
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
    exact length_choicesT_le I cities p hcit)
  rw [List.length_map] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) hp)

theorem length_familiesT_le (I : Instance) (cities ports : List Cell)
    (hcit : cities.length ≤ 40) (hp : ports.length ≤ 10) :
    (familiesT I cities ports).val.length ≤ (2 ^ 40 + 1) ^ 10 := by
  simp only [familiesT, bind_val, tsections_val, tmapM_val]
  exact (length_sections_le _).trans (prodSucc_choices_le I cities ports hcit hp)

theorem familiesT_time_le (I : Instance) (cities ports : List Cell) (D : ℕ)
    (hcit : cities.length ≤ 40) (hp : ports.length ≤ 10)
    (hD : ∀ p c, (dpRun I [(p, [(c, 0)])] 4).time ≤ D) :
    (familiesT I cities ports).time ≤ 10 * (40 * D + 2 ^ 60 + 3) + 80 * (2 ^ 40 + 1) ^ 10 := by
  have t1 := tmapM_time_le (choicesT I cities) ports (40 * D + 2 ^ 60)
    (fun p _ => choicesT_time_le I cities p D hcit (hD p))
  have t2 := tsections_time_le (ports.map (fun p => (choicesT I cities p).val))
  rw [List.length_map] at t2
  have h1 := prodSucc_choices_le I cities ports hcit hp
  have h2 : 8 * ports.length * prodSucc (ports.map (fun p => (choicesT I cities p).val)) ≤
      8 * 10 * (2 ^ 40 + 1) ^ 10 := Nat.mul_le_mul (by omega) h1
  have h3 : ports.length * (40 * D + 2 ^ 60 + 3) ≤ 10 * (40 * D + 2 ^ 60 + 3) :=
    Nat.mul_le_mul_right _ hp
  simp only [familiesT, bind_time, tmapM_val]
  omega

theorem bestT_time_le (I : Instance) (D : ℕ) (fams : List PD)
    (h : ∀ pd ∈ fams, (dpRun I pd 3).time ≤ D) :
    (bestT I fams).time ≤ fams.length * (D + 4) := by
  induction fams with
  | nil => simp [bestT]
  | cons pd rest ih =>
      have h1 := h pd (by simp)
      have h2 := ih (fun pd' hpd' => h pd' (List.mem_cons_of_mem _ hpd'))
      simp only [bestT, bind_time, tickN_time, List.length_cons]
      cases hd : (dpRun I pd 3).val with
      | none => simp only [pure_time]; nlinarith
      | some e =>
          obtain ⟨c, w⟩ := e
          cases hr : (bestT I rest).val with
          | none => simp only [pure_time]; nlinarith
          | some e' =>
              obtain ⟨c', pd', w'⟩ := e'
              by_cases hc : c ≤ c' <;>
                simp only [bind_time, tick_time, hc, ite_true, ite_false, pure_time] <;> nlinarith

theorem length_edgeList_le (L : Cell → Lab) (cells : List Cell) :
    (edgeList L cells).length ≤ 2 * cells.length := by
  induction cells with
  | nil => simp [edgeList]
  | cons x cells ih =>
      have h : edgeList L (x :: cells) =
          ((if (L x).eR then [(x, (x.1 + 1, x.2))] else []) ++
            (if (L x).eD then [(x, (x.1, x.2 + 1))] else [])) ++ edgeList L cells := by
        simp [edgeList]
      rw [h, List.length_append, List.length_append, List.length_cons]
      cases (L x).eR <;> cases (L x).eD <;> simp <;> omega

theorem edgesT_time_le (I : Instance) (w : List (List Lab)) (cells : List Cell)
    (hc : ∀ x ∈ cells, x.1 < I.W ∧ x.2 < I.H) :
    (edgesT I w cells).time ≤ 1 + (cells.length * (I.W + I.H + 19) + (3 * cells.length + 1)) := by
  simp only [edgesT, bind_time, tick_time, tickN_time, pure_time, tmapM_val]
  refine Nat.add_le_add le_rfl (Nat.add_le_add (tmapM_time_le _ cells (I.W + I.H + 16) ?_) le_rfl)
  intro x hx
  have := hc x hx
  simp only [bind_time, tickN_time, pure_time]
  omega

theorem choiceTableT_time_le (pd : PD) (c : ℕ) (h : ∀ e ∈ pd, e.2.length ≤ c) :
    (choiceTableT pd).time ≤ pd.length * (2 * (c * c) + 2 * c + 5) := by
  unfold choiceTableT
  refine tmapM_time_le _ pd (2 * (c * c) + 2 * c + 2) ?_
  intro e he
  have h1 := h e he
  have h2 := Nat.mul_le_mul h1 h1
  have h3 : 2 * e.2.length * e.2.length = 2 * (e.2.length * e.2.length) := by ring
  simp only [bind_time, tickN_time, pure_time]
  omega

/-- Sizes of a choice combination when there are at most 10 ports and 40 cities. -/
theorem fam_lengths {I : Instance} (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40)
    {pd : PD} (h : pd ∈ famsOf I) : pd.length ≤ 10 ∧ ∀ e ∈ pd, e.2.length ≤ 40 := by
  obtain ⟨h1, h2⟩ := famsOf_spec h
  constructor
  · have h3 := congrArg List.length h1
    rw [List.length_map, length_portsL] at h3
    omega
  · intro e he
    have hs := (h2 e he).1.length_le
    have h3 := length_distsT_le I (citiesL I) e.1
    have h4 := length_citiesL I
    unfold finOf at hs
    omega


/-! ### The running time of `solve` -/

/-- The running time of `solve`, step by step; `X` bounds the decoding of the result. -/
theorem solve_time_split (I : Instance) (X : ℕ)
    (hX : ∀ c pd w, (bestT I (famsOf I)).val = some (c, pd, w) →
      (edgesT I w (cellsT I).val).time +
        (4 * (edgesT I w (cellsT I).val).val.length * (edgesT I w (cellsT I).val).val.length +
          (edgesT I w (cellsT I).val).val.length + 2 + (choiceTableT pd).time) ≤ X) :
    (Answer.solve I).time ≤ (cellsT I).time + ((scanT I.ports (cellsT I).val).time +
      ((scanT I.cities (cellsT I).val).time + ((familiesT I (citiesL I) (portsL I)).time +
        ((bestT I (famsOf I)).time + X)))) := by
  simp only [Answer.solve, bind_time]
  cases h : (bestT I (famsOf I)).val with
  | none =>
      simp only [famsOf, citiesL, portsL] at h ⊢
      rw [h]
      simp only [pure_time]
      omega
  | some e =>
      obtain ⟨c, pd, w⟩ := e
      have hx := hX c pd w h
      simp only [famsOf, citiesL, portsL] at h hx ⊢
      rw [h]
      simp only [bind_time, tickN_time, pure_time]
      omega

namespace Answer

/-- Explicit bound: with at most 10 ports and 40 cities the running time is at most
`2 ^ 420 · N ^ (60 + 90 · min(W, H))`, i.e. `2 ^ O(√N · log N)`. -/
theorem solve_time_le (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    (Answer.solve I).time ≤
      2 ^ 420 * I.size ^ (60 + 90 * mOf (decide (I.H ≤ I.W)) I.W I.H) := by
  obtain ⟨hW, hH⟩ := dims_pos I
  have hN : 2 ≤ I.size := size_ge_two I
  have hsz : I.size = I.W * I.H + 1 := rfl
  have hWH : I.W * I.H ≤ I.size := by omega
  have hWN : I.W ≤ I.size := (Nat.le_mul_of_pos_right I.W hH).trans hWH
  have hHN : I.H ≤ I.size := (Nat.le_mul_of_pos_left I.H hW).trans hWH
  have hpl : (portsL I).length ≤ 10 := by rw [length_portsL]; exact hP
  have hcl : (citiesL I).length ≤ 40 := by rw [length_citiesL]; exact hC
  set m := mOf (decide (I.H ≤ I.W)) I.W I.H with hmdef
  have hdp : ∀ (pd : PD) (β : ℕ), pd.length ≤ 10 → (∀ e ∈ pd, e.2.length ≤ 40) →
      (dpRun I pd β).time ≤ I.size ^ (60 + 90 * m) := fun pd β => dpRun_time_le I pd β
  set D := I.size ^ (60 + 90 * m) with hDdef
  have hD1 : 1 ≤ D := Nat.one_le_pow _ _ (by omega)
  have hdist : ∀ p c, (dpRun I [(p, [(c, 0)])] 4).time ≤ D :=
    fun p c => hdp _ 4 (by simp) (by simp)
  -- the cell list and the two scans
  have ta : (cellsT I).time ≤ D := by
    have h := cellsT_time_le I
    have h1 : 5 * (I.W * I.H) + 5 * I.W + I.H + 5 ≤ 16 * I.size := by omega
    have h2 : 16 * I.size ≤ I.size ^ 5 :=
      pw_mul hN 5 (pw_const hN 4 (by norm_num)) (pw_self le_rfl) (by omega)
    exact h.trans (h1.trans (pw_mono hN _ h2 (by omega)))
  have tb : (scanT I.ports (cellsT I).val).time ≤ D := by
    have h := scanT_time_le I.ports (cellsT I).val
    rw [length_cellsT] at h
    have h1 : I.W * I.H * (3 * I.ports.card + 4) ≤ I.size ^ 7 :=
      pw_mul hN 7 (pw_self hWH) (pw_const hN 6 (by omega)) (by omega)
    exact h.trans (pw_mono hN _ h1 (by omega))
  have tc : (scanT I.cities (cellsT I).val).time ≤ D := by
    have h := scanT_time_le I.cities (cellsT I).val
    rw [length_cellsT] at h
    have h1 : I.W * I.H * (3 * I.cities.card + 4) ≤ I.size ^ 8 :=
      pw_mul hN 8 (pw_self hWH) (pw_const hN 7 (by omega)) (by omega)
    exact h.trans (pw_mono hN _ h1 (by omega))
  -- enumerating the choice combinations, and one DP run for each of them
  have td := familiesT_time_le I (citiesL I) (portsL I) D hcl hpl hdist
  have hfl : (famsOf I).length ≤ (2 ^ 40 + 1) ^ 10 := length_familiesT_le I _ _ hcl hpl
  have te : (bestT I (famsOf I)).time ≤ (2 ^ 40 + 1) ^ 10 * (D + 4) :=
    (bestT_time_le I D (famsOf I) (fun pd hpd =>
      hdp pd 3 (fam_lengths hP hC hpd).1 (fam_lengths hP hC hpd).2)).trans
      (Nat.mul_le_mul_right _ hfl)
  -- decoding
  have key := solve_time_split I D (by
    intro c pd w hbest
    obtain ⟨hpd, -, -⟩ := bestT_some hbest
    obtain ⟨hl1, hl2⟩ := fam_lengths hP hC hpd
    have h1 := edgesT_time_le I w (cellsT I).val (fun x hx => mem_cellsT.mp hx)
    rw [length_cellsT] at h1
    have h2 : (edgesT I w (cellsT I).val).val.length ≤ 2 * (I.W * I.H) := by
      rw [edgesT_val, ← length_cellsT]
      exact length_edgeList_le _ _
    have h3 := choiceTableT_time_le pd 40 hl2
    have hE : (edgesT I w (cellsT I).val).val.length ≤ I.size ^ 2 :=
      h2.trans (pw_mul hN 2 (pw_const hN 1 (by norm_num)) (pw_self hWH) (by omega))
    have b1 : 1 + (I.W * I.H * (I.W + I.H + 19) + (3 * (I.W * I.H) + 1)) ≤ I.size ^ 10 :=
      pw_add hN 10 (pw_const hN 0 (by norm_num))
        (pw_add hN 9
          (pw_mul hN 8 (pw_self hWH)
            (pw_add hN 7 (pw_add hN 2 (pw_self hWN) (pw_self hHN) (by omega) (by omega))
              (pw_const hN 5 (by norm_num)) (by omega) (by omega)) (by omega))
          (pw_add hN 4 (pw_mul hN 3 (pw_const hN 2 (by norm_num)) (pw_self hWH) (by omega))
            (pw_const hN 0 (by norm_num)) (by omega) (by omega))
          (by omega) (by omega))
        (by omega) (by omega)
    have b2 : 4 * (edgesT I w (cellsT I).val).val.length *
        (edgesT I w (cellsT I).val).val.length +
        (edgesT I w (cellsT I).val).val.length + 2 ≤ I.size ^ 9 :=
      pw_add hN 9
        (pw_add hN 7
          (pw_mul hN 6 (pw_mul hN 4 (pw_const hN 2 (by norm_num)) hE (by omega)) hE (by omega))
          hE (by omega) (by omega))
        (pw_const hN 1 (by norm_num)) (by omega) (by omega)
    have b3 : (choiceTableT pd).time ≤ I.size ^ 16 := by
      have h4 : pd.length * (2 * (40 * 40) + 2 * 40 + 5) ≤ 10 * (2 * (40 * 40) + 2 * 40 + 5) :=
        Nat.mul_le_mul_right _ hl1
      exact pw_const hN 16 (by omega)
    exact pw_mono hN _
      (pw_add hN 18 (h1.trans b1) (pw_add hN 17 b2 b3 (by omega) (by omega))
        (by omega) (by omega)) (by omega))
  -- summing up
  have hD4 : (2 ^ 40 + 1) ^ 10 ≤ (2 ^ 40 + 1) ^ 10 * D := Nat.le_mul_of_pos_right _ hD1
  have hmul : (2 ^ 40 + 1) ^ 10 * (D + 4) = (2 ^ 40 + 1) ^ 10 * D + 4 * (2 ^ 40 + 1) ^ 10 := by
    ring
  have hsum : (Answer.solve I).time ≤ 2 ^ 64 * D + 85 * ((2 ^ 40 + 1) ^ 10 * D) := by
    generalize (2 ^ 40 + 1) ^ 10 * D = FD at *
    generalize (2 ^ 40 + 1) ^ 10 = F at *
    omega
  have hF : (2 ^ 40 + 1) ^ 10 ≤ 2 ^ 410 :=
    pw_pow (N := 2) le_rfl 410 10 (by norm_num : 2 ^ 40 + 1 ≤ 2 ^ 41) (by norm_num)
  have h85 : (85 : ℕ) ≤ 2 ^ 7 := by norm_num
  have hK : 2 ^ 64 + 85 * (2 ^ 40 + 1) ^ 10 ≤ 2 ^ 420 :=
    pw_add (N := 2) le_rfl 420 (le_refl (2 ^ 64))
      (pw_mul (N := 2) le_rfl 417 h85 hF (by norm_num)) (by norm_num) (by norm_num)
  calc (Answer.solve I).time ≤ 2 ^ 64 * D + 85 * ((2 ^ 40 + 1) ^ 10 * D) := hsum
    _ = (2 ^ 64 + 85 * (2 ^ 40 + 1) ^ 10) * D := by ring
    _ ≤ 2 ^ 420 * D := Nat.mul_le_mul_right D hK

/-- Sub-exponential running time: for every `ε > 0`, on all large enough instances with at
most 10 ports and 40 cities, the running time is at most `2 ^ (ε · N)`. -/
theorem subexp :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      n₀ ≤ I.size → ((Answer.solve I).time : ℝ) ≤ (2 : ℝ) ^ (ε * I.size) := by
  intro ε hε
  obtain ⟨n₀, h⟩ := pow_sqrt_subexp (2 ^ 420) 60 90 ε hε
  refine ⟨n₀, fun I hP hC hn => ?_⟩
  have h1 : ((Answer.solve I).time : ℝ) ≤
      ((2 ^ 420 * I.size ^ (60 + 90 * mOf (decide (I.H ≤ I.W)) I.W I.H) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (solve_time_le I hP hC)
  exact h1.trans (h I.size (mOf (decide (I.H ≤ I.W)) I.W I.H) hn (mOf_sq_le I))

end Answer

end TrainNetwork
