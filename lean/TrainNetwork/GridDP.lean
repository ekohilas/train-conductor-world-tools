/-
The layered DP instantiated with distance-label certificates.

* candidate labels: all edge patterns × all lists of port entries with distance `< M`;
* a layer is a column (if `H ≤ W`) or a row (otherwise) of the grid, so it has
  `min W H` cells; a layer state is a list of labels, one per cell;
* the self-check runs the unary checks and the pair checks inside the layer and sums
  the cell costs; the link-check runs the pair checks between consecutive layers.

`dpRun` returns a labelling of the whole grid that passes all checks and has minimum
certified cost among all labellings with labels in the candidate list.
-/
import TrainNetwork.LayerDP
import TrainNetwork.Complete

namespace TrainNetwork

open TimeM

/-! ## Enumerating labels -/

def dirs : List Dir := [.R, .D, .L, .U]

/-- All port entries with distance below `n`. The list has `4 n + 1` elements. -/
def entryListT (n : ℕ) : TimeM (List DEntry) := do
  tickN (16 * n + 16)
  pure (none :: (List.range n).flatMap (fun d => dirs.map (fun δ => some (d, δ))))

theorem mem_entryListT {n : ℕ} {en : DEntry} (h : ∀ d δ, en = some (d, δ) → d < n) :
    en ∈ (entryListT n).val := by
  simp only [entryListT, bind_val, pure_val]
  cases en with
  | none => simp
  | some e =>
      obtain ⟨d, δ⟩ := e
      refine List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr (h d δ rfl), ?_⟩)
      cases δ <;> simp [dirs]

theorem length_entryListT (n : ℕ) : (entryListT n).val.length = 4 * n + 1 := by
  simp [entryListT, List.length_flatMap, dirs, List.map_const', List.sum_replicate, mul_comm]

/-- The 16 edge patterns. -/
def bools4 : List (Bool × Bool × Bool × Bool) :=
  [(false, false, false, false), (false, false, false, true), (false, false, true, false),
   (false, false, true, true), (false, true, false, false), (false, true, false, true),
   (false, true, true, false), (false, true, true, true), (true, false, false, false),
   (true, false, false, true), (true, false, true, false), (true, false, true, true),
   (true, true, false, false), (true, true, false, true), (true, true, true, false),
   (true, true, true, true)]

theorem mem_bools4 : ∀ e : Bool × Bool × Bool × Bool, e ∈ bools4 := by decide

theorem forall₂_mem_replicate {α : Type} {es : List α} :
    ∀ {l : List α} {q : ℕ}, l.length = q → (∀ a ∈ l, a ∈ es) →
      List.Forall₂ (fun a s => a ∈ s) l (List.replicate q es)
  | [], q, hlen, _ => by
      subst hlen
      exact List.Forall₂.nil
  | a :: l, q, hlen, hmem => by
      subst hlen
      rw [List.length_cons, List.replicate_succ]
      exact List.Forall₂.cons (hmem a (by simp))
        (forall₂_mem_replicate rfl (fun b hb => hmem b (by simp [hb])))

theorem mem_sections_replicate {α : Type} {es l : List α} {q : ℕ} (hlen : l.length = q)
    (hmem : ∀ a ∈ l, a ∈ es) : l ∈ (List.replicate q es).sections :=
  List.mem_sections.mpr (forall₂_mem_replicate hlen hmem)

theorem prodSucc_replicate {α : Type} (es : List α) (q : ℕ) :
    prodSucc (List.replicate q es) = (es.length + 1) ^ q := by
  simp [prodSucc, List.map_replicate, List.prod_replicate]

/-- All labels for `q` ports with distances below `n`. -/
def labsT (q n : ℕ) : TimeM (List Lab) := do
  let es ← entryListT n
  tickN (q + 1)
  let dss ← tsections (List.replicate q es)
  let r ← tmapM (fun ds => tmapM
      (fun (e : Bool × Bool × Bool × Bool) => do
        -- one record
        tick
        pure (⟨e.1, e.2.1, e.2.2.1, e.2.2.2, ds⟩ : Lab))
      bools4) dss
  -- flattening `|dss|` lists of length 16
  tickN (17 * dss.length + 1)
  pure r.flatten

theorem mem_labsT {q n : ℕ} {a : Lab} (hlen : a.ds.length = q)
    (hr : ∀ en ∈ a.ds, ∀ (d : ℕ) (δ : Dir), en = some (d, δ) → d < n) :
    a ∈ (labsT q n).val := by
  simp only [labsT, bind_val, pure_val, tsections_val, tmapM_val, List.mem_flatten,
    List.mem_map]
  refine ⟨_, ⟨a.ds, mem_sections_replicate hlen (fun en hen => mem_entryListT (hr en hen)),
    rfl⟩, ?_⟩
  exact List.mem_map.mpr ⟨(a.eR, a.eD, a.eL, a.eU), mem_bools4 _, rfl⟩

theorem length_labsT_le (q n : ℕ) : (labsT q n).val.length ≤ 16 * (4 * n + 2) ^ q := by
  have h1 := length_sections_le (List.replicate q (entryListT n).val)
  rw [prodSucc_replicate, length_entryListT] at h1
  simp only [labsT, bind_val, pure_val, tsections_val, tmapM_val, List.length_flatten,
    List.map_map]
  simp only [Function.comp_def, List.length_map, List.map_const', List.sum_replicate,
    smul_eq_mul]
  have hb : bools4.length = 16 := rfl
  have h4 : 4 * n + 1 + 1 = 4 * n + 2 := by omega
  rw [h4] at h1
  rw [hb]
  omega

theorem labsT_time_le (q n : ℕ) :
    (labsT q n).time ≤ 16 * n + q + 18 + (8 * q + 84) * (4 * n + 2) ^ q := by
  have h1 := length_sections_le (List.replicate q (entryListT n).val)
  rw [prodSucc_replicate, length_entryListT] at h1
  have h2 := tsections_time_le (List.replicate q (entryListT n).val)
  rw [prodSucc_replicate, length_entryListT, List.length_replicate] at h2
  have hinner : ∀ ds ∈ (List.replicate q (entryListT n).val).sections,
      (tmapM (fun (e : Bool × Bool × Bool × Bool) =>
        (do tick; pure (⟨e.1, e.2.1, e.2.2.1, e.2.2.2, ds⟩ : Lab) : TimeM Lab)) bools4).time
        ≤ 64 := by
    intro ds _
    have := tmapM_time_le (fun (e : Bool × Bool × Bool × Bool) =>
        (do tick; pure (⟨e.1, e.2.1, e.2.2.1, e.2.2.2, ds⟩ : Lab) : TimeM Lab)) bools4 1
        (by simp)
    simpa [bools4] using this
  have h3 := tmapM_time_le (fun ds => tmapM (fun (e : Bool × Bool × Bool × Bool) =>
        (do tick; pure (⟨e.1, e.2.1, e.2.2.1, e.2.2.2, ds⟩ : Lab) : TimeM Lab)) bools4)
      (List.replicate q (entryListT n).val).sections 64 hinner
  have h0 : (entryListT n).time = 16 * n + 16 := by simp [entryListT]
  simp only [labsT, bind_time, pure_time, tickN_time, tsections_val, h0]
  have h4 : 4 * n + 1 + 1 = 4 * n + 2 := by omega
  rw [h4] at h1 h2
  nlinarith

/-! ## Checks on a whole layer -/

/-- The pair check between cell `j` of a layer (kind `k`, label `a`) and the next cell
of the same layer, if there is one. -/
def withinT (dW : Dir) (k : Kind) (a : Lab) (ks : List Kind) (as : List Lab) (m j : ℕ) :
    TimeM Bool :=
  if j + 1 < m then
    pairT dW k a (ks.getD (j + 1) default) (as.getD (j + 1) default)
  else pure true

theorem withinT_val (dW : Dir) (k : Kind) (a : Lab) (ks : List Kind) (as : List Lab)
    (m j : ℕ) :
    (withinT dW k a ks as m j).val = true ↔
      (j + 1 < m → PairOK dW k a (ks.getD (j + 1) default) (as.getD (j + 1) default)) := by
  unfold withinT
  by_cases hj : j + 1 < m
  · simp [hj, pairT_val]
  · simp [hj]

/-- Unary checks, pair checks inside the layer (direction `dW`) and total cost of the
first `j` cells of a layer of `m` cells. -/
def colSelfT (β M : ℕ) (dW : Dir) (ks : List Kind) (as : List Lab) (m : ℕ) :
    ℕ → TimeM (Option ℕ)
  | 0 => pure (some 0)
  | j + 1 => do
      -- recursive call; four list accesses (indices `j`, `j`, `j + 1`, `j + 1`: at most
      -- `4 j + 6` steps); two additions, one comparison, one result
      tickN (4 * j + 14)
      let r ← colSelfT β M dW ks as m j
      let k := ks.getD j default
      let a := as.getD j default
      let u ← unaryT β k a
      let p ← withinT dW k a ks as m j
      let c ← cellCostT M k a
      pure (match r with
        | some t => if u && p then some (t + c) else none
        | none => none)

theorem colSelfT_val (β M : ℕ) (dW : Dir) (ks : List Kind) (as : List Lab) (m q c : ℕ) :
    (colSelfT β M dW ks as m q).val = some c ↔
      (∀ j, j < q → UnaryOK β (ks.getD j default) (as.getD j default) ∧
        (j + 1 < m → PairOK dW (ks.getD j default) (as.getD j default)
          (ks.getD (j + 1) default) (as.getD (j + 1) default))) ∧
      c = ∑ j ∈ Finset.range q, (cellCostT M (ks.getD j default) (as.getD j default)).val := by
  induction q generalizing c with
  | zero => simp [colSelfT, eq_comm]
  | succ q ih =>
      simp only [colSelfT, bind_val, pure_val]
      cases hr : (colSelfT β M dW ks as m q).val with
      | none =>
          constructor
          · intro h
            exact absurd h (by simp)
          · rintro ⟨hall, -⟩
            have := (ih (∑ j ∈ Finset.range q,
              (cellCostT M (ks.getD j default) (as.getD j default)).val)).mpr
              ⟨fun j hj => hall j (Nat.lt_succ_of_lt hj), rfl⟩
            rw [hr] at this
            exact absurd this (by simp)
      | some t =>
          obtain ⟨hall, ht⟩ := (ih t).mp hr
          by_cases hup : ((unaryT β (ks.getD q default) (as.getD q default)).val &&
              (withinT dW (ks.getD q default) (as.getD q default) ks as m q).val) = true
          · have hup' := hup
            rw [Bool.and_eq_true, unaryT_val, withinT_val] at hup'
            simp only [hup, ite_true, Option.some.injEq]
            constructor
            · intro h
              refine ⟨?_, ?_⟩
              · intro j hj
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                · exact hall j hlt
                · exact hup'
              · rw [Finset.sum_range_succ, ← ht, ← h]
            · rintro ⟨-, hc⟩
              rw [hc, Finset.sum_range_succ, ← ht]
          · simp only [hup, Bool.false_eq_true, ite_false]
            constructor
            · intro h
              exact absurd h (by simp)
            · rintro ⟨hall', -⟩
              exfalso
              apply hup
              rw [Bool.and_eq_true, unaryT_val, withinT_val]
              exact hall' q (Nat.lt_succ_self q)

theorem getD_pp_le {ks : List Kind} {Q : ℕ} (h : ∀ k ∈ ks, k.pp.length ≤ Q) (j : ℕ) :
    (ks.getD j default).pp.length ≤ Q := by
  by_cases hj : j < ks.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    exact Nat.zero_le _

theorem colSelfT_time_le (β M : ℕ) (dW : Dir) (ks : List Kind) (as : List Lab) (m Q : ℕ)
    (hQ : ∀ k ∈ ks, k.pp.length ≤ Q) (q : ℕ) :
    (colSelfT β M dW ks as m q).time ≤ q * (4 * q + 14 + 3 * cellBound Q) := by
  induction q with
  | zero => simp [colSelfT]
  | succ q ih =>
      have hk := getD_pp_le hQ q
      have h1 := unaryT_time_le (β := β) (a := as.getD q default) hk
      have h2 : (withinT dW (ks.getD q default) (as.getD q default) ks as m q).time
          ≤ cellBound Q := by
        unfold withinT
        by_cases hq : q + 1 < m
        · simp only [hq, ite_true]
          exact pairT_time_le hk
        · simp [hq]
      have h3 := cellCostT_time_le (M := M) (a := as.getD q default) hk
      simp only [colSelfT, bind_time, tickN_time, pure_time]
      nlinarith

/-- Pair checks (direction `dA`) between the first `j` cells of two consecutive layers. -/
def colLinkT (dA : Dir) (ks : List Kind) (as : List Lab) (ks' : List Kind) (as' : List Lab) :
    ℕ → TimeM Bool
  | 0 => pure true
  | j + 1 => do
      -- recursive call; four list accesses at index `j` (`4 j + 4` steps)
      tickN (4 * j + 8)
      let r ← colLinkT dA ks as ks' as' j
      let p ← pairT dA (ks.getD j default) (as.getD j default)
        (ks'.getD j default) (as'.getD j default)
      pure (p && r)

theorem colLinkT_val (dA : Dir) (ks : List Kind) (as : List Lab) (ks' : List Kind)
    (as' : List Lab) (q : ℕ) :
    (colLinkT dA ks as ks' as' q).val = true ↔
      ∀ j, j < q → PairOK dA (ks.getD j default) (as.getD j default)
        (ks'.getD j default) (as'.getD j default) := by
  induction q with
  | zero => simp [colLinkT]
  | succ q ih =>
      simp only [colLinkT, bind_val, pure_val, Bool.and_eq_true, ih, pairT_val]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h2 j h
        · exact h1
      · intro h
        exact ⟨h q (Nat.lt_succ_self q), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

theorem colLinkT_time_le (dA : Dir) (ks : List Kind) (as : List Lab) (ks' : List Kind)
    (as' : List Lab) (Q : ℕ) (hQ : ∀ k ∈ ks, k.pp.length ≤ Q) (q : ℕ) :
    (colLinkT dA ks as ks' as' q).time ≤ q * (4 * q + 8 + cellBound Q) := by
  induction q with
  | zero => simp [colLinkT]
  | succ q ih =>
      have h1 := pairT_time_le (δ := dA) (a := as.getD q default) (kb := ks'.getD q default)
        (b := as'.getD q default) (getD_pp_le hQ q)
      simp only [colLinkT, bind_time, tickN_time, pure_time]
      nlinarith

/-- Self-check of the grid DP. -/
def gSelf (β M : ℕ) (dW : Dir) (ks : List Kind) (as : List Lab) : TimeM (Option ℕ) := do
  -- the length of `ks`, computed once
  tickN (ks.length + 1)
  let m := ks.length
  colSelfT β M dW ks as m m

/-- Link-check of the grid DP. -/
def gLink (dA : Dir) (ks : List Kind) (as : List Lab) (ks' : List Kind) (as' : List Lab) :
    TimeM Bool := do
  -- the length of `ks`
  tickN (ks.length + 1)
  colLinkT dA ks as ks' as' ks.length

theorem gSelf_time_le (β M : ℕ) (dW : Dir) (ks : List Kind) (as : List Lab) (Q : ℕ)
    (hQ : ∀ k ∈ ks, k.pp.length ≤ Q) :
    (gSelf β M dW ks as).time ≤
      ks.length + 1 + ks.length * (4 * ks.length + 14 + 3 * cellBound Q) := by
  have := colSelfT_time_le β M dW ks as ks.length Q hQ ks.length
  simp only [gSelf, bind_time, tickN_time]
  omega

theorem gLink_time_le (dA : Dir) (ks : List Kind) (as : List Lab) (ks' : List Kind)
    (as' : List Lab) (Q : ℕ) (hQ : ∀ k ∈ ks, k.pp.length ≤ Q) :
    (gLink dA ks as ks' as').time ≤
      ks.length + 1 + ks.length * (4 * ks.length + 8 + cellBound Q) := by
  have := colLinkT_time_le dA ks as ks' as' Q hQ ks.length
  simp only [gLink, bind_time, tickN_time]
  omega

/-! ## From layer assignments to labellings and back -/

section Bridge

variable (β M : ℕ) (dW dA : Dir) (n m : ℕ) (KK : ℕ → ℕ → Kind)

/-- The kinds of all layers. -/
def layersOf : List (List Kind) :=
  (List.range n).map (fun i => (List.range m).map (fun j => KK i j))

/-- A labelling as a list of layer states. -/
def tab (Λ : ℕ → ℕ → Lab) : List (List Lab) :=
  (List.range n).map (fun i => (List.range m).map (fun j => Λ i j))

/-- The label of cell `j` of layer `i` in a list of layer states. -/
def lab (w : List (List Lab)) (i j : ℕ) : Lab := (w.getD i []).getD j default

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem layersOf_length : (layersOf n m KK).length = n := by simp [layersOf]

theorem layersOf_getD {i : ℕ} (hi : i < n) :
    (layersOf n m KK).getD i [] = (List.range m).map (fun j => KK i j) :=
  getD_map_range _ _ hi

theorem lab_tab (Λ : ℕ → ℕ → Lab) {i j : ℕ} (hi : i < n) (hj : j < m) :
    lab (tab n m Λ) i j = Λ i j := by
  simp only [lab, tab]
  rw [getD_map_range _ _ hi, getD_map_range _ _ hj]

variable {β M dW dA n m KK}

theorem gSelf_row_iff (i : ℕ) (as : List Lab) (c : ℕ) :
    (gSelf β M dW ((List.range m).map (fun j => KK i j)) as).val = some c ↔
      (∀ j, j < m → UnaryOK β (KK i j) (as.getD j default) ∧
        (j + 1 < m → PairOK dW (KK i j) (as.getD j default) (KK i (j + 1))
          (as.getD (j + 1) default))) ∧
      c = ∑ j ∈ Finset.range m, (cellCostT M (KK i j) (as.getD j default)).val := by
  simp only [gSelf, bind_val, List.length_map, List.length_range, colSelfT_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h1 j hj
      rw [getD_map_range _ _ hj] at this
      refine ⟨this.1, fun hj' => ?_⟩
      have h3 := this.2 hj'
      rw [getD_map_range _ _ hj'] at h3
      exact h3
    · rw [h2]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [getD_map_range _ _ (Finset.mem_range.mp hj)]
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [getD_map_range _ _ hj]
      refine ⟨(h1 j hj).1, fun hj' => ?_⟩
      rw [getD_map_range _ _ hj']
      exact (h1 j hj).2 hj'
    · rw [h2]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [getD_map_range _ _ (Finset.mem_range.mp hj)]

theorem gLink_row_iff (i i' : ℕ) (as as' : List Lab) :
    (gLink dA ((List.range m).map (fun j => KK i j)) as
      ((List.range m).map (fun j => KK i' j)) as').val = true ↔
      ∀ j, j < m → PairOK dA (KK i j) (as.getD j default) (KK i' j) (as'.getD j default) := by
  simp only [gLink, bind_val, List.length_map, List.length_range, colLinkT_val]
  constructor
  · intro h j hj
    have := h j hj
    rw [getD_map_range _ _ hj, getD_map_range _ _ hj] at this
    exact this
  · intro h j hj
    rw [getD_map_range _ _ hj, getD_map_range _ _ hj]
    exact h j hj

/-- A valid layer assignment is a labelling that passes all checks. -/
theorem valid_layOK {cands : List (List Lab)} {w : List (List Lab)}
    (h : LayerDP.Valid (gSelf β M dW) (gLink dA) cands (layersOf n m KK) w) :
    LayOK β dW dA n m KK (lab w) := by
  rw [LayerDP.valid_iff_getD [] []] at h
  obtain ⟨-, hall⟩ := h
  rw [layersOf_length] at hall
  have hrow : ∀ i, i < n → ∀ j, j < m → UnaryOK β (KK i j) (lab w i j) ∧
      (j + 1 < m → PairOK dW (KK i j) (lab w i j) (KK i (j + 1)) (lab w i (j + 1))) := by
    intro i hi
    obtain ⟨-, hsome, -⟩ := hall i hi
    rw [layersOf_getD n m KK hi] at hsome
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    exact ((gSelf_row_iff i _ c).mp hc).1
  refine ⟨fun i j hi hj => (hrow i hi j hj).1, fun i j hi hj => (hrow i hi j (by omega)).2 hj,
    fun i j hi hj => ?_⟩
  obtain ⟨-, -, hlink⟩ := hall i (by omega)
  have := hlink hi
  rw [layersOf_getD n m KK (by omega : i < n), layersOf_getD n m KK hi] at this
  exact (gLink_row_iff i (i + 1) _ _).mp this j hj

/-- The cost of a valid layer assignment is the sum of its cell costs. -/
theorem cost_of_valid {cands : List (List Lab)} {w : List (List Lab)}
    (h : LayerDP.Valid (gSelf β M dW) (gLink dA) cands (layersOf n m KK) w) :
    LayerDP.cost (gSelf β M dW) (layersOf n m KK) w =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, (cellCostT M (KK i j) (lab w i j)).val := by
  have h' := h
  rw [LayerDP.valid_iff_getD [] []] at h'
  obtain ⟨hlen, hall⟩ := h'
  rw [LayerDP.cost_eq_sum [] [] _ _ hlen, layersOf_length]
  rw [layersOf_length] at hall
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  obtain ⟨-, hsome, -⟩ := hall i hi'
  rw [layersOf_getD n m KK hi'] at hsome ⊢
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  rw [hc, Option.getD_some, ((gSelf_row_iff i _ c).mp hc).2]
  rfl

/-- A labelling that passes all checks, with labels from `labs`, is a valid layer
assignment. -/
theorem valid_tab {labs : List Lab} {Λ : ℕ → ℕ → Lab} (h : LayOK β dW dA n m KK Λ)
    (hl : ∀ i j, i < n → j < m → Λ i j ∈ labs) :
    LayerDP.Valid (gSelf β M dW) (gLink dA) (List.replicate m labs).sections
      (layersOf n m KK) (tab n m Λ) := by
  rw [LayerDP.valid_iff_getD [] []]
  refine ⟨by simp [tab, layersOf], ?_⟩
  rw [layersOf_length]
  intro i hi
  have htab : ∀ i, i < n → (tab n m Λ).getD i [] = (List.range m).map (fun j => Λ i j) :=
    fun i hi => getD_map_range _ _ hi
  have hget : ∀ i j, j < m → ((List.range m).map (fun j => Λ i j)).getD j default = Λ i j :=
    fun i j hj => getD_map_range _ _ hj
  rw [htab i hi, layersOf_getD n m KK hi]
  refine ⟨?_, ?_, ?_⟩
  · refine mem_sections_replicate (by simp) ?_
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact hl i j hi (List.mem_range.mp hj)
  · rw [Option.isSome_iff_exists]
    refine ⟨_, (gSelf_row_iff i _ _).mpr ⟨fun j hj => ?_, rfl⟩⟩
    rw [hget i j hj]
    refine ⟨h.unary i j hi hj, fun hj' => ?_⟩
    rw [hget i (j + 1) hj']
    exact h.within i j hi hj'
  · intro hi'
    rw [htab (i + 1) hi', layersOf_getD n m KK hi']
    refine (gLink_row_iff i (i + 1) _ _).mpr (fun j hj => ?_)
    rw [hget i j hj, hget (i + 1) j hj]
    exact h.across i j hi' hj

end Bridge

end TrainNetwork
