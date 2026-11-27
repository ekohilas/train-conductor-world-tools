/-
Completeness of certificates: for every network `τ` whose edges are grid edges, the
true network distances (with a predecessor direction chosen on a shortest walk) form a
labelling that passes all local checks, uses distances below `W · H`, and whose
certified cost is at most the true cost of `τ`.

Everything here is proof-only (noncomputable); the algorithm never runs it.
-/
import TrainNetwork.Sound

namespace TrainNetwork

open TimeM

section

variable (I : Instance) (τ : Solution)

theorem netAdj_gridAdj {I : Instance} {τ : Solution}
    (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) {a b : Cell} (h : τ.NetAdj a b) :
    I.GridAdj a b := by
  rcases h with h | h
  · exact hE _ h
  · exact (hE _ h).symm

/-- The `δ`-neighbour of `x` is the last-but-one cell of a shortest walk from `p`. -/
def IsPred (p x : Cell) (δ : Dir) : Prop :=
  ∃ y, IsNb δ x y ∧ τ.NetAdj y x ∧ τ.netDist I p y + 1 = τ.netDist I p x ∧
    (y = p ∨ I.IsFree y)

open Classical in
/-- A predecessor direction of `x` (arbitrary if there is none). -/
noncomputable def predDir (p x : Cell) : Dir :=
  if h : ∃ δ, IsPred I τ p x δ then Classical.choose h else Dir.R

variable {I τ}

theorem predDir_spec (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) {p x : Cell} (hxp : x ≠ p)
    (hfin : τ.netDist I p x < ⊤) : IsPred I τ p x (predDir I τ p x) := by
  have hex : ∃ δ, IsPred I τ p x δ := by
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfin.ne
    cases d with
    | zero =>
        have h0 : I.walkDist τ.NetAdj p x = ((0 : ℕ) : ℕ∞) := hd.symm
        exact absurd (reach_zero_iff.mp (walkDist_eq_coe_iff.mp h0).1) hxp
    | succ d =>
        have h1 : I.walkDist τ.NetAdj p x = ((d + 1 : ℕ) : ℕ∞) := hd.symm
        obtain ⟨y, hyx, hy, hor⟩ := exists_pred h1
        obtain ⟨δ, hδ⟩ := adjacent_iff_isNb.mp (netAdj_gridAdj hE hyx).symm.1
        refine ⟨δ, y, hδ, hyx, ?_, hor⟩
        show I.walkDist τ.NetAdj p y + 1 = I.walkDist τ.NetAdj p x
        rw [hy, h1]
        push_cast
        rfl
  unfold predDir
  split
  · rename_i h
    exact Classical.choose_spec h
  · rename_i h
    exact absurd hex h

variable (I τ)

open Classical in
/-- The entry of cell `x` for a port at `p`: its exact network distance, if finite. -/
noncomputable def certEntry (p x : Cell) : DEntry :=
  if τ.netDist I p x < ⊤ then some ((τ.netDist I p x).toNat, predDir I τ p x) else none

open Classical in
/-- The canonical label of cell `x`. -/
noncomputable def certLab (pd : PD) (x : Cell) : Lab where
  eR := decide (hasNb .R x = true ∧ τ.NetAdj x (nbOf .R x))
  eD := decide (hasNb .D x = true ∧ τ.NetAdj x (nbOf .D x))
  eL := decide (hasNb .L x = true ∧ τ.NetAdj x (nbOf .L x))
  eU := decide (hasNb .U x = true ∧ τ.NetAdj x (nbOf .U x))
  ds := pd.map (fun e => certEntry I τ e.1 x)

variable {I τ}

theorem certEntry_fin {p x : Cell} (h : τ.netDist I p x < ⊤) :
    certEntry I τ p x = some ((τ.netDist I p x).toNat, predDir I τ p x) := by
  simp only [certEntry, h, ↓reduceIte]

theorem certEntry_inf {p x : Cell} (h : ¬ τ.netDist I p x < ⊤) : certEntry I τ p x = none := by
  simp only [certEntry, h, ↓reduceIte]

theorem certLab_edge (pd : PD) (x : Cell) (δ : Dir) :
    (certLab I τ pd x).edge δ = true ↔ ∃ y, IsNb δ x y ∧ τ.NetAdj x y := by
  have h0 : (certLab I τ pd x).edge δ = true ↔
      (hasNb δ x = true ∧ τ.NetAdj x (nbOf δ x)) := by
    cases δ <;> simp only [certLab, Lab.edge, decide_eq_true_eq]
  rw [h0]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨nbOf δ x, isNb_iff.mpr ⟨h1, rfl⟩, h2⟩
  · rintro ⟨y, h1, h2⟩
    obtain ⟨h3, rfl⟩ := isNb_iff.mp h1
    exact ⟨h3, h2⟩

theorem certLab_d (pd : PD) (x : Cell) {j : ℕ} {p : Cell} {dl : List (Cell × ℕ)}
    (hj : pd[j]? = some (p, dl)) : (certLab I τ pd x).d j = certEntry I τ p x := by
  simp [Lab.d, certLab, List.getD_eq_getElem?_getD, hj]

theorem certLab_ds_length (pd : PD) (x : Cell) : (certLab I τ pd x).ds.length = pd.length := by
  simp [certLab]

/-- Finite distances and their `toNat`. -/
theorem netDist_coe_toNat {p x : Cell} (h : τ.netDist I p x < ⊤) :
    ((τ.netDist I p x).toNat : ℕ∞) = τ.netDist I p x :=
  ENat.natCast_toNat h.ne

/-- All distances used by the canonical labelling are below `W · H`. -/
theorem certLab_range (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) (pd : PD)
    (hpin : ∀ e ∈ pd, I.InBounds e.1) (x : Cell) :
    ∀ en ∈ (certLab I τ pd x).ds, ∀ (d : ℕ) (δ : Dir), en = some (d, δ) → d < I.W * I.H := by
  intro en hen d δ hd
  simp only [certLab, List.mem_map] at hen
  obtain ⟨e, he, rfl⟩ := hen
  by_cases hfin : τ.netDist I e.1 x < ⊤
  · rw [certEntry_fin hfin] at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    exact walkDist_lt_cells (R := τ.NetAdj) (fun a b hab => (netAdj_gridAdj hE hab).2.2.1)
      (hpin e he) (netDist_coe_toNat hfin).symm
  · rw [certEntry_inf hfin] at hd
    exact absurd hd (by simp)

/-- The predecessor condition holds for the canonical labelling. -/
theorem certLab_pred (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) (pd : PD) {δ : Dir} {x y : Cell}
    (hnb : IsNb δ x y) {j : ℕ} {p : Cell} {dl : List (Cell × ℕ)} (hj : pd[j]? = some (p, dl)) :
    predOK δ ((kindOf I pd x).p j) ((certLab I τ pd x).d j) ((kindOf I pd y).p j)
      ((certLab I τ pd y).d j) = true := by
  rw [kindOf_p I pd x hj, kindOf_p I pd y hj, certLab_d pd x hj, certLab_d pd y hj]
  by_cases hfin : τ.netDist I p x < ⊤
  · rw [certEntry_fin hfin]
    by_cases hc : predDir I τ p x = δ ∧ x ≠ p
    · obtain ⟨hδ, hxp⟩ := hc
      obtain ⟨y₀, hnb₀, -, hdist, hor⟩ := predDir_spec hE hxp hfin
      rw [hδ] at hnb₀
      have hy : y₀ = y := isNb_unique hnb₀ hnb
      subst hy
      have hfy : τ.netDist I p y₀ < ⊤ := by
        refine lt_of_le_of_lt ?_ hfin
        rw [← hdist]
        exact le_self_add
      rw [certEntry_fin hfy]
      have hnat : (τ.netDist I p y₀).toNat + 1 = (τ.netDist I p x).toNat := by
        have h1 := netDist_coe_toNat hfin
        have h2 := netDist_coe_toNat hfy
        rw [← h1, ← h2] at hdist
        exact_mod_cast hdist
      have htr : (decide (I.IsFree y₀) || decide (y₀ = p)) = true := by
        rcases hor with h | h
        · simp [h]
        · simp [h]
      simp only [predOK, pkOf, hδ, hxp, decide_false, and_self, ite_true, htr, Bool.true_and,
        beq_iff_eq]
      exact hnat
    · have hc' : ¬ (predDir I τ p x = δ ∧ decide (x = p) = false) :=
        fun hcond => hc ⟨hcond.1, by simpa using hcond.2⟩
      simp only [predOK, pkOf, hc', ↓reduceIte]
  · rw [certEntry_inf hfin]
    rfl

/-- All pair checks hold for the canonical labelling. -/
theorem certLab_pair (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) (pd : PD) {δ : Dir} {c c' : Cell}
    (hnb : IsNb δ c c') :
    PairOK δ (kindOf I pd c) (certLab I τ pd c) (kindOf I pd c') (certLab I τ pd c') := by
  constructor
  · rw [Bool.eq_iff_iff, certLab_edge, certLab_edge]
    constructor
    · rintro ⟨y, hy1, hy2⟩
      rw [isNb_unique hy1 hnb] at hy2
      exact ⟨c, isNb_opp.mpr hnb, hy2.symm⟩
    · rintro ⟨y, hy1, hy2⟩
      have : y = c := isNb_unique hy1 (isNb_opp.mpr hnb)
      rw [this] at hy2
      exact ⟨c', hnb, hy2.symm⟩
  · intro j hj
    rw [kindOf_pp_length] at hj
    obtain ⟨⟨p, dl⟩, hpd⟩ : ∃ e, pd[j]? = some e := ⟨pd[j], List.getElem?_eq_getElem hj⟩
    simp only [predAt, Bool.and_eq_true]
    exact ⟨certLab_pred hE pd hnb hpd, certLab_pred hE pd (isNb_opp.mpr hnb) hpd⟩

/-- All unary checks hold for the canonical labelling. -/
theorem certLab_unary (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) {β : ℕ}
    (hdeg : ∀ x, I.IsFree x → (τ.neighbours x).card ≤ β) (pd : PD)
    (hdem : ∀ (j : ℕ) (p : Cell) (dl : List (Cell × ℕ)) (x : Cell) (g : ℕ),
      pd[j]? = some (p, dl) → (tlookup x dl).val = some g → τ.netDist I p x < ⊤)
    (c : Cell) : UnaryOK β (kindOf I pd c) (certLab I τ pd c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨y, hy1, hy2⟩ := (certLab_edge pd c δ).mp hδ
    exact (kindOf_allow I pd c δ).mpr ⟨y, hy1, netAdj_gridAdj hE hy2⟩
  · intro hfree
    have hfree' : I.IsFree c := (kindOf_free I pd c).mp hfree
    rw [Lab.deg_eq_card]
    have hinj : Set.InjOn (fun δ => nbOf δ c)
        ↑(Finset.univ.filter (fun δ : Dir => (certLab I τ pd c).edge δ = true)) := by
      intro δ hδ δ' hδ' heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hδ hδ'
      obtain ⟨y, hy1, -⟩ := (certLab_edge pd c δ).mp hδ
      obtain ⟨y', hy1', -⟩ := (certLab_edge pd c δ').mp hδ'
      have e1 := (isNb_iff.mp hy1).2
      have e2 := (isNb_iff.mp hy1').2
      have : y = y' := by rw [e1, e2]; exact heq
      rw [← this] at hy1'
      exact isNb_dir_unique hy1 hy1'
    rw [← Finset.card_image_of_injOn hinj]
    refine le_trans (Finset.card_le_card ?_) (hdeg c hfree')
    intro y hy
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
    obtain ⟨y, hy1, hy2⟩ := (certLab_edge pd c δ).mp hδ
    rw [← (isNb_iff.mp hy1).2]
    exact Solution.mem_neighbours.mpr hy2
  · intro j hj
    rw [kindOf_pp_length] at hj
    obtain ⟨⟨p, dl⟩, hpd⟩ : ∃ e, pd[j]? = some e := ⟨pd[j], List.getElem?_eq_getElem hj⟩
    rw [kindOf_p I pd c hpd, certLab_d pd c hpd]
    by_cases hfin : τ.netDist I p c < ⊤
    · rw [certEntry_fin hfin]
      by_cases hcp : c = p
      · subst hcp
        have h0 : τ.netDist I c c = 0 := walkDist_self
        simp [entryOK, pkOf, h0]
      · obtain ⟨y, hy1, hy2, hdist, -⟩ := predDir_spec hE hcp hfin
        have hedge : (certLab I τ pd c).edge (predDir I τ p c) = true :=
          (certLab_edge pd c _).mpr ⟨y, hy1, hy2.symm⟩
        have hpos : 1 ≤ (τ.netDist I p c).toNat := by
          have h1 := netDist_coe_toNat hfin
          have h2 : (1 : ℕ∞) ≤ τ.netDist I p c := by
            rw [← hdist]
            exact le_add_self
          rw [← h1] at h2
          exact_mod_cast h2
        simp [entryOK, pkOf, hcp, hedge, hpos]
    · rw [certEntry_inf hfin]
      have hcp : c ≠ p := by
        rintro rfl
        exact hfin (by rw [show τ.netDist I c c = 0 from walkDist_self]; simp)
      have hnone : (tlookup c dl).val = none := by
        cases hl : (tlookup c dl).val with
        | none => rfl
        | some g => exact absurd (hdem j p dl c g hpd hl) hfin
      simp [entryOK, pkOf, hcp, hnone]

/-- The canonical labelling passes all checks. -/
theorem certLab_ok (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) {β : ℕ}
    (hdeg : ∀ x, I.IsFree x → (τ.neighbours x).card ≤ β) (pd : PD)
    (hdem : ∀ (j : ℕ) (p : Cell) (dl : List (Cell × ℕ)) (x : Cell) (g : ℕ),
      pd[j]? = some (p, dl) → (tlookup x dl).val = some g → τ.netDist I p x < ⊤) :
    GridOK β I.W I.H (kindOf I pd) (certLab I τ pd) :=
  ⟨fun x y _ _ => certLab_unary hE hdeg pd hdem (x, y),
   fun x y _ _ => certLab_pair hE pd (δ := .D) (c := (x, y)) (c' := (x, y + 1)) rfl,
   fun x y _ _ => certLab_pair hE pd (δ := .R) (c := (x, y)) (c' := (x + 1, y)) rfl⟩

/-- The certified tile count of the canonical labelling is at most the true one. -/
theorem certLab_tiles (pd : PD) : tileCount I pd (certLab I τ pd) ≤ (τ.tiles I).card := by
  rw [tileCount_eq_card]
  refine Finset.card_le_card ?_
  intro c hc
  simp only [Finset.mem_filter, Bool.and_eq_true] at hc
  obtain ⟨-, hfree, hany⟩ := hc
  obtain ⟨δ, hδ⟩ := (Lab.any_iff _).mp hany
  obtain ⟨y, -, hy⟩ := (certLab_edge pd c δ).mp hδ
  simp only [Solution.tiles, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  refine ⟨?_, (kindOf_free I pd c).mp hfree⟩
  rcases hy with h | h
  · exact Or.inl ⟨(c, y), h, rfl⟩
  · exact Or.inr ⟨(y, c), h, rfl⟩

/-- The certified excess of the canonical labelling is at most the true one, when the
demands of `pd` are chosen cities of `τ` with their grid distances. -/
theorem certLab_excess (pd : PD) (hnd : (pd.map Prod.fst).Nodup)
    (hpf : (pd.map Prod.fst).toFinset = I.ports)
    (hch : ∀ (j : ℕ) (p : Cell) (dl : List (Cell × ℕ)) (c : Cell) (g : ℕ),
      pd[j]? = some (p, dl) → (tlookup c dl).val = some g →
        c ∈ τ.choice p ∧ I.gridDist p c = (g : ℕ∞)) :
    (excCount I pd (certLab I τ pd) : ℕ∞) ≤ τ.excess I := by
  unfold Solution.excess
  rw [sum_ports hnd hpf, excCount_eq, Nat.cast_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjlt : j < pd.length := Finset.mem_range.mp hj
  obtain ⟨⟨p, dl⟩, hpd⟩ : ∃ e, pd[j]? = some e := ⟨pd[j], List.getElem?_eq_getElem hjlt⟩
  have hget : (pd.getD j default).1 = p := by
    simp [List.getD_eq_getElem?_getD, hpd]
  rw [hget, Nat.cast_sum]
  calc ∑ c ∈ Finset.range I.W ×ˢ Finset.range I.H,
        ((excAt (kindOf I pd c) (certLab I τ pd c) j : ℕ) : ℕ∞)
      ≤ ∑ c ∈ τ.choice p, ((excAt (kindOf I pd c) (certLab I τ pd c) j : ℕ) : ℕ∞) := by
        refine Finset.sum_le_sum_of_ne_zero (fun c _ hne => ?_)
        cases hl : (tlookup c dl).val with
        | none =>
            rw [excAt_of_lookup_none I _ hpd hl] at hne
            exact absurd rfl hne
        | some g => exact (hch j p dl c g hpd hl).1
    _ ≤ ∑ c ∈ τ.choice p, (τ.netDist I p c - I.gridDist p c) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        cases hl : (tlookup c dl).val with
        | none =>
            rw [excAt_of_lookup_none I _ hpd hl]
            simp
        | some g =>
            by_cases hfin : τ.netDist I p c < ⊤
            · have hd := certLab_d (I := I) (τ := τ) pd c hpd
              rw [certEntry_fin hfin] at hd
              rw [excAt_of I _ hpd hl hd, (hch j p dl c g hpd hl).2]
              have h1 := netDist_coe_toNat hfin
              rw [← h1]
              push_cast
              rfl
            · have hd := certLab_d (I := I) (τ := τ) pd c hpd
              rw [certEntry_inf hfin] at hd
              rw [excAt_of_entry_none _ _ hd]
              simp

end

end TrainNetwork
