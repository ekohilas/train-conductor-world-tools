/-
Sizes of variable indices and of the O(1) clause blocks emitted by `toK`.
-/
import TrainNetwork.Bound

namespace TrainNetwork.Answer

open TrainNetwork TimeM

theorem sz_pair {a b m : ℕ} (ha : Nat.size a ≤ m) (hb : Nat.size b ≤ m) :
    Nat.size (Nat.pair a b) ≤ 2 * m := by
  rw [Nat.size_le] at ha hb ⊢
  have hmax : max a b + 1 ≤ 2 ^ m := by
    rcases le_total a b with h' | h'
    · rw [max_eq_right h']; omega
    · rw [max_eq_left h']; omega
  calc Nat.pair a b < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hmax 2
    _ = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]

theorem sz_pair' {a b m k : ℕ} (ha : Nat.size a ≤ m) (hb : Nat.size b ≤ m) (hk : 2 * m ≤ k) :
    Nat.size (Nat.pair a b) ≤ k := le_trans (sz_pair ha hb) hk

theorem sz_atom {a M : ℕ} (h : a ≤ M) : Nat.size a ≤ M :=
  Nat.size_le.mpr (lt_of_le_of_lt h Nat.lt_two_pow_self)

/-- Both coordinates of a cell are at most `M`. -/
def CellB (M : ℕ) (c : Cell) : Prop := c.1 ≤ M ∧ c.2 ≤ M

theorem sz_cell {M : ℕ} {c : Cell} (h : CellB M c) : Nat.size (cellCode c) ≤ 2 * M :=
  sz_pair (sz_atom h.1) (sz_atom h.2)

section sizes
variable {M : ℕ} (hM : 3 ≤ M)
include hM

theorem sz_vEdge {u v : Cell} (hu : CellB M u) (hv : CellB M v) :
    Nat.size (vEdge u v) ≤ 32 * M := by
  unfold vEdge
  have h1 : Nat.size (min (cellCode u) (cellCode v)) ≤ 2 * M := by
    rcases min_choice (cellCode u) (cellCode v) with h | h <;> rw [h]
    · exact sz_cell hu
    · exact sz_cell hv
  have h2 : Nat.size (max (cellCode u) (cellCode v)) ≤ 2 * M := by
    rcases max_choice (cellCode u) (cellCode v) with h | h <;> rw [h]
    · exact sz_cell hu
    · exact sz_cell hv
  exact sz_pair' (m := 4 * M) (sz_atom (by omega)) (sz_pair' h1 h2 (by omega)) (by omega)

theorem sz_vSel {p c : Cell} (hp : CellB M p) (hc : CellB M c) :
    Nat.size (vSel p c) ≤ 32 * M := by
  unfold vSel
  exact sz_pair' (m := 4 * M) (sz_atom (by omega))
    (sz_pair' (sz_cell hp) (sz_cell hc) (by omega)) (by omega)

theorem sz_vGrid {p v : Cell} {t : ℕ} (hp : CellB M p) (ht : t ≤ M) (hv : CellB M v) :
    Nat.size (vGrid p t v) ≤ 32 * M := by
  unfold vGrid
  exact sz_pair' (m := 8 * M) (sz_atom (by omega))
    (sz_pair' (m := 4 * M) (le_trans (sz_cell hp) (by omega))
      (sz_pair' (m := 2 * M) (sz_atom (by omega)) (sz_cell hv) (by omega)) (by omega)) (by omega)

theorem sz_vNet {p v : Cell} {t : ℕ} (hp : CellB M p) (ht : t ≤ M) (hv : CellB M v) :
    Nat.size (vNet p t v) ≤ 32 * M := by
  unfold vNet
  exact sz_pair' (m := 8 * M) (sz_atom (by omega))
    (sz_pair' (m := 4 * M) (le_trans (sz_cell hp) (by omega))
      (sz_pair' (m := 2 * M) (sz_atom (by omega)) (sz_cell hv) (by omega)) (by omega)) (by omega)

theorem sz_vStep {p v u : Cell} {t : ℕ} (hp : CellB M p) (ht : t ≤ M) (hv : CellB M v)
    (hu : CellB M u) : Nat.size (vStep p t v u) ≤ 32 * M := by
  unfold vStep
  exact sz_pair' (m := 16 * M) (sz_atom (by omega))
    (sz_pair' (m := 8 * M) (le_trans (sz_cell hp) (by omega))
      (sz_pair' (m := 4 * M) (sz_atom (by omega))
        (sz_pair' (sz_cell hv) (sz_cell hu) (by omega)) (by omega)) (by omega)) (by omega)

theorem sz_vTile {x : Cell} (hx : CellB M x) : Nat.size (vTile x) ≤ 32 * M := by
  unfold vTile
  exact sz_pair' (m := 2 * M) (sz_atom (by omega)) (sz_cell hx) (by omega)

theorem sz_tag {g : ℕ} {p : Cell} (hg : g ≤ 3) (hp : CellB M p) :
    Nat.size (Nat.pair g (cellCode p)) ≤ 4 * M :=
  sz_pair' (m := 2 * M) (sz_atom (by omega)) (sz_cell hp) (by omega)

theorem sz_vCount {tag i j : ℕ} (htag : Nat.size tag ≤ 4 * M) (hi : i ≤ M) (hj : j ≤ M) :
    Nat.size (vCount tag i j) ≤ 32 * M := by
  unfold vCount
  exact sz_pair' (m := 8 * M) (sz_atom (by omega))
    (sz_pair' (m := 4 * M) htag (sz_pair' (sz_atom hi) (sz_atom hj) (by omega)) (by omega))
    (by omega)

end sizes

/-- A clause with at most 6 literals whose variables have at most `S` bits. -/
def CB (S : ℕ) (c : Clause) : Prop := c.length ≤ 6 ∧ ∀ l ∈ c, Nat.size l.1 ≤ S

theorem clauseSize_le {S : ℕ} {c : Clause} (h : CB S c) : clauseSize c ≤ 7 + 6 * S := by
  unfold clauseSize
  have h1 : (c.map litSize).sum ≤ (c.map litSize).length • (1 + S) := by
    apply List.sum_le_length_nsmul
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    unfold litSize
    have := h.2 l hl
    omega
  simp only [List.length_map, smul_eq_mul] at h1
  have h2 : c.length * (1 + S) ≤ 6 * (1 + S) := Nat.mul_le_mul_right _ h.1
  omega

/-- Cost of emitting a block of at most `n` bounded clauses. -/
theorem block_time_le (c S n : ℕ) (φ : List Clause) (hlen : φ.length ≤ n)
    (h : ∀ cl ∈ φ, CB S cl) : (block c φ).time ≤ c + n * (199 + 6 * S) := by
  rw [block_time]
  have h1 : lits φ ≤ φ.length • 6 := by
    unfold lits
    have := List.sum_le_length_nsmul (φ.map List.length) 6 (by
      intro x hx
      obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hx
      exact (h cl hcl).1)
    simpa using this
  have h2 : wsize φ ≤ φ.length • (7 + 6 * S) := by
    unfold wsize
    have := List.sum_le_length_nsmul (φ.map clauseSize) (7 + 6 * S) (by
      intro x hx
      obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hx
      exact clauseSize_le (h cl hcl))
    simpa using this
  simp only [smul_eq_mul] at h1 h2
  have h3 : φ.length * (199 + 6 * S) ≤ n * (199 + 6 * S) := Nat.mul_le_mul_right _ hlen
  have e : φ.length * (199 + 6 * S) = 32 * (φ.length * 6) + φ.length * (7 + 6 * S) := by ring
  omega

theorem cb_of {S : ℕ} (c : Clause) (hlen : c.length ≤ 6)
    (h : ∀ v ∈ c.map Prod.fst, Nat.size v ≤ S) : CB S c :=
  ⟨hlen, fun l hl => h l.1 (List.mem_map_of_mem hl)⟩

/-- Uniform bound on the cost of every block emitted by `toK`, when all coordinates,
times and counter indices are at most `M`. -/
def Q (M : ℕ) : ℕ := 128 + 15 * (199 + 192 * M)

theorem block_le_Q (c n M : ℕ) (hc : c ≤ 128) (hn : n ≤ 15) (φ : List Clause)
    (hlen : φ.length ≤ n) (h : ∀ cl ∈ φ, CB (32 * M) cl) : (block c φ).time ≤ Q M := by
  have h1 := block_time_le c (32 * M) n φ hlen h
  have h2 : n * (199 + 6 * (32 * M)) ≤ 15 * (199 + 6 * (32 * M)) := Nat.mul_le_mul_right _ hn
  unfold Q
  omega

variable (I : Instance)

section blocks
variable {M : ℕ} (hM : 3 ≤ M)
include hM

omit hM in
theorem edgeAt_len (v u : Cell) : (edgeAt I v u).length ≤ 2 := by
  unfold edgeAt
  split_ifs <;> simp

theorem edgeAt_cb {v u : Cell} (hv : CellB M v) (hu : CellB M u) :
    ∀ cl ∈ edgeAt I v u, CB (32 * M) cl := by
  intro cl hcl
  have h3 : cl = [(vEdge v u, false), (vTile v, true)] ∨
      cl = [(vEdge v u, false), (vTile u, true)] ∨ cl = [(vEdge v u, false)] := by
    unfold edgeAt at hcl
    split_ifs at hcl <;> simp at hcl <;> tauto
  rcases h3 with rfl | rfl | rfl
  · exact cb_of _ (by simp) (by simp; exact ⟨sz_vEdge hM hv hu, sz_vTile hM hv⟩)
  · exact cb_of _ (by simp) (by simp; exact ⟨sz_vEdge hM hv hu, sz_vTile hM hu⟩)
  · exact cb_of _ (by simp) (by simp; exact sz_vEdge hM hv hu)

theorem edge_block_le (v : Cell) (hv : v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M) :
    (block 64 (edgeAt I v (v.1 + 1, v.2) ++ edgeAt I v (v.1, v.2 + 1) ++ degAt I v)).time ≤
      Q M := by
  have hv' : CellB M v := ⟨by omega, by omega⟩
  have hr : CellB M (v.1 + 1, v.2) := ⟨hv.1, by show v.2 ≤ M; omega⟩
  have hd : CellB M (v.1, v.2 + 1) := ⟨by show v.1 ≤ M; omega, hv.2⟩
  have hl : CellB M (v.1 - 1, v.2) := ⟨by show v.1 - 1 ≤ M; omega, by show v.2 ≤ M; omega⟩
  have hu : CellB M (v.1, v.2 - 1) := ⟨by show v.1 ≤ M; omega, by show v.2 - 1 ≤ M; omega⟩
  have hdl : (degAt I v).length ≤ 1 := by unfold degAt; split_ifs <;> simp
  apply block_le_Q 64 5 M (by omega) (by omega)
  · have h1 := edgeAt_len I v (v.1 + 1, v.2)
    have h2 := edgeAt_len I v (v.1, v.2 + 1)
    simp only [List.length_append]
    omega
  · intro cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with (hcl | hcl) | hcl
    · exact edgeAt_cb I hM hv' hr cl hcl
    · exact edgeAt_cb I hM hv' hd cl hcl
    · unfold degAt at hcl
      split_ifs at hcl
      · simp at hcl
        subst hcl
        exact cb_of _ (by simp) (by
          simp
          exact ⟨sz_vEdge hM hv' hr, sz_vEdge hM hv' hd, sz_vEdge hM hv' hl,
            sz_vEdge hM hv' hu⟩)
      · simp at hcl

theorem init_block_le {p v : Cell} (hp : CellB M p) (hv : CellB M v) :
    (block 1 (if v = p then [[(vGrid p 0 v, true)]]
      else [[(vGrid p 0 v, false)], [(vNet p 0 v, false)]])).time ≤ Q M := by
  apply block_le_Q 1 2 M (by omega) (by omega)
  · split_ifs <;> simp
  · intro cl hcl
    split_ifs at hcl
    · simp at hcl; subst hcl
      exact cb_of _ (by simp) (by simp; exact sz_vGrid hM hp (by omega) hv)
    · simp at hcl
      rcases hcl with rfl | rfl
      · exact cb_of _ (by simp) (by simp; exact sz_vGrid hM hp (by omega) hv)
      · exact cb_of _ (by simp) (by simp; exact sz_vNet hM hp (by omega) hv)

theorem fin_block_le {p c : Cell} (hp : CellB M p) (hc : CellB M c) (hT : I.W * I.H ≤ M) :
    (block 4 [[(vSel p c, false), (vGrid p (I.W * I.H) c, true)],
      [(vSel p c, false), (vNet p (I.W * I.H) c, true)]]).time ≤ Q M := by
  apply block_le_Q 4 2 M (by omega) (by omega)
  · simp
  · intro cl hcl
    simp at hcl
    rcases hcl with rfl | rfl
    · exact cb_of _ (by simp) (by simp; exact ⟨sz_vSel hM hp hc, sz_vGrid hM hp hT hc⟩)
    · exact cb_of _ (by simp) (by simp; exact ⟨sz_vSel hM hp hc, sz_vNet hM hp hT hc⟩)

theorem near_block_le {p c c2 : Cell} {t : ℕ} (hp : CellB M p) (hc : CellB M c)
    (hc2 : CellB M c2) (ht : t ≤ M) :
    (block 0 [[(vSel p c, false), (vSel p c2, true), (vGrid p t c2, false),
      (vGrid p t c, true)]]).time ≤ Q M := by
  apply block_le_Q 0 1 M (by omega) (by omega)
  · simp
  · intro cl hcl
    simp at hcl
    subst hcl
    exact cb_of _ (by simp) (by
      simp
      exact ⟨sz_vSel hM hp hc, sz_vSel hM hp hc2, sz_vGrid hM hp ht hc2, sz_vGrid hM hp ht hc⟩)

omit hM in
theorem nbrs_len (v : Cell) : (nbrs v).length ≤ 4 := by
  unfold nbrs
  split_ifs <;> simp

omit hM in
theorem nbrs_bound {u v : Cell} (h : u ∈ nbrs v) : u.1 ≤ v.1 + 1 ∧ u.2 ≤ v.2 + 1 := by
  rw [mem_nbrs] at h
  unfold Adjacent at h
  omega

omit hM in
theorem stepsN_len (p v : Cell) : (stepsN I p v).length ≤ 4 :=
  le_trans (List.length_filter_le _ _) (nbrs_len v)

omit hM in
theorem stepsG_len (p v : Cell) : (stepsG I p v).length ≤ 4 :=
  le_trans (List.length_filter_le _ _) (stepsN_len I p v)

omit hM in
theorem flatMap_pair_len {α β : Type} (l : List α) (f g : α → β) :
    (l.flatMap fun u => [f u, g u]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]; omega

theorem step_block_le {p v : Cell} {t : ℕ} (hp : CellB M p)
    (hv : v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M) (ht : t + 1 ≤ M) :
    (block 128 (stepClauses I p t v)).time ≤ Q M := by
  have hv' : CellB M v := ⟨by omega, by omega⟩
  have hN : ∀ u ∈ stepsN I p v, CellB M u := fun u hu => by
    have := nbrs_bound (List.mem_of_mem_filter hu)
    exact ⟨by omega, by omega⟩
  have hG : ∀ u ∈ stepsG I p v, CellB M u := fun u hu => hN u (List.mem_of_mem_filter hu)
  have hlN := stepsN_len I p v
  have hlG := stepsG_len I p v
  apply block_le_Q 128 15 M le_rfl le_rfl
  · unfold stepClauses
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
      flatMap_pair_len]
    omega
  · intro cl hcl
    unfold stepClauses at hcl
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      List.not_mem_nil, or_false] at hcl
    rcases hcl with (((hcl | hcl) | ⟨u, hu, rfl⟩) | hcl) | ⟨u, hu, hcl⟩
    · subst hcl
      refine ⟨by simp only [List.length_cons, List.length_map]; omega, ?_⟩
      intro l hl
      simp only [List.mem_cons, List.mem_map] at hl
      rcases hl with rfl | rfl | ⟨u, hu, rfl⟩
      · exact sz_vGrid hM hp ht hv'
      · exact sz_vGrid hM hp (by omega) hv'
      · exact sz_vGrid hM hp (by omega) (hG u hu)
    · subst hcl
      exact cb_of _ (by simp) (by
        simp; exact ⟨sz_vGrid hM hp (by omega) hv', sz_vGrid hM hp ht hv'⟩)
    · exact cb_of _ (by simp) (by
        simp; exact ⟨sz_vGrid hM hp (by omega) (hG u hu), sz_vGrid hM hp ht hv'⟩)
    · subst hcl
      refine ⟨by simp only [List.length_cons, List.length_map]; omega, ?_⟩
      intro l hl
      simp only [List.mem_cons, List.mem_map] at hl
      rcases hl with rfl | rfl | ⟨u, hu, rfl⟩
      · exact sz_vNet hM hp ht hv'
      · exact sz_vNet hM hp (by omega) hv'
      · exact sz_vStep hM hp (by omega) hv' (hN u hu)
    · rcases hcl with rfl | rfl
      · exact cb_of _ (by simp) (by
          simp
          exact ⟨sz_vStep hM hp (by omega) hv' (hN u hu), sz_vNet hM hp (by omega) (hN u hu)⟩)
      · exact cb_of _ (by simp) (by
          simp
          exact ⟨sz_vStep hM hp (by omega) hv' (hN u hu), sz_vEdge hM (hN u hu) hv'⟩)

omit hM in
theorem counter_step_block_le (cv : ℕ → ℕ → ℕ) (i j : ℕ) (it : List Lit)
    (hit : it.length ≤ 3 ∧ ∀ l ∈ it, Nat.size l.1 ≤ 32 * M)
    (hcv : ∀ i' j', i' ≤ i + 1 → j' ≤ j → Nat.size (cv i' j') ≤ 32 * M) :
    (block 8 [[(cv i j, false), (cv (i + 1) j, true)],
        if j = 0 then negLits it ++ [(cv (i + 1) 0, true)]
        else negLits it ++ [(cv i (j - 1), false), (cv (i + 1) j, true)]]).time ≤ Q M := by
  have hneg : ∀ l ∈ negLits it, Nat.size l.1 ≤ 32 * M := by
    intro l hl
    unfold negLits at hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    exact hit.2 l' hl'
  have hnl : (negLits it).length ≤ 3 := by
    unfold negLits; simpa using hit.1
  apply block_le_Q 8 2 M (by omega) (by omega)
  · simp
  · intro cl hcl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact cb_of _ (by simp) (by
        simp; exact ⟨hcv i j (by omega) le_rfl, hcv (i + 1) j le_rfl le_rfl⟩)
    · split_ifs with h0
      · refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
        intro l hl
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with hl | rfl
        · exact hneg l hl
        · exact hcv (i + 1) 0 le_rfl (by omega)
      · refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
        intro l hl
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with hl | rfl | rfl
        · exact hneg l hl
        · exact hcv i (j - 1) (by omega) (by omega)
        · exact hcv (i + 1) j le_rfl le_rfl

omit hM in
theorem counter_final_block_le (cv : ℕ → ℕ → ℕ) (i B : ℕ)
    (h : Nat.size (cv i B) ≤ 32 * M) : (block 0 [[(cv i B, false)]]).time ≤ Q M := by
  apply block_le_Q 0 1 M (by omega) (by omega)
  · simp
  · intro cl hcl
    simp at hcl
    subst hcl
    exact cb_of _ (by simp) (by simp; exact h)

end blocks

end TrainNetwork.Answer
