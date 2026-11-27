/-
Soundness of certificates: a labelling that passes all local checks describes a network
in which every entry `(d, _)` for a port is witnessed by a walk of length `d` from that
port, the degree cap holds, and the certified cost bounds the true cost from above.
-/
import TrainNetwork.Cert

namespace TrainNetwork

open TimeM

/-- All local checks hold, stated in layer coordinates: `n` layers of `m` cells each,
`dW` the direction inside a layer, `dA` the direction to the next layer. -/
structure LayOK (β : ℕ) (dW dA : Dir) (n m : ℕ) (KK : ℕ → ℕ → Kind) (Λ : ℕ → ℕ → Lab) :
    Prop where
  unary : ∀ i j, i < n → j < m → UnaryOK β (KK i j) (Λ i j)
  within : ∀ i j, i < n → j + 1 < m →
    PairOK dW (KK i j) (Λ i j) (KK i (j + 1)) (Λ i (j + 1))
  across : ∀ i j, i + 1 < n → j < m →
    PairOK dA (KK i j) (Λ i j) (KK (i + 1) j) (Λ (i + 1) j)

/-- All local checks hold on the `W × H` grid (layers = columns). -/
def GridOK (β W H : ℕ) (K : Cell → Kind) (L : Cell → Lab) : Prop :=
  LayOK β .D .R W H (fun x y => K (x, y)) (fun x y => L (x, y))

/-- The same statement with rows as layers. -/
theorem gridOK_iff_rows {β W H : ℕ} {K : Cell → Kind} {L : Cell → Lab} :
    GridOK β W H K L ↔ LayOK β .R .D H W (fun i j => K (j, i)) (fun i j => L (j, i)) := by
  constructor
  · intro h
    exact ⟨fun i j hi hj => h.unary j i hj hi, fun i j hi hj => h.across j i hj hi,
      fun i j hi hj => h.within j i hj hi⟩
  · intro h
    exact ⟨fun i j hi hj => h.unary j i hj hi, fun i j hi hj => h.across j i hj hi,
      fun i j hi hj => h.within j i hj hi⟩

/-- Certified number of track tiles. -/
def tileCount (I : Instance) (pd : PD) (L : Cell → Lab) : ℕ :=
  ∑ x ∈ Finset.range I.W, ∑ y ∈ Finset.range I.H, tileAt (kindOf I pd (x, y)) (L (x, y))

/-- Certified total excess. -/
def excCount (I : Instance) (pd : PD) (L : Cell → Lab) : ℕ :=
  ∑ x ∈ Finset.range I.W, ∑ y ∈ Finset.range I.H, ∑ j ∈ Finset.range pd.length,
    excAt (kindOf I pd (x, y)) (L (x, y)) j

/-- Total certified cost, as computed by the DP. -/
def gridCost (M : ℕ) (I : Instance) (pd : PD) (L : Cell → Lab) : ℕ :=
  ∑ x ∈ Finset.range I.W, ∑ y ∈ Finset.range I.H,
    (cellCostT M (kindOf I pd (x, y)) (L (x, y))).val

theorem gridCost_eq (M : ℕ) (I : Instance) (pd : PD) (L : Cell → Lab) :
    gridCost M I pd L = excCount I pd L * M + tileCount I pd L := by
  simp only [gridCost, excCount, tileCount, cellCostT_val, kindOf_pp_length,
    Finset.sum_add_distrib, Finset.sum_mul]

theorem tileCount_le (I : Instance) (pd : PD) (L : Cell → Lab) :
    tileCount I pd L ≤ I.W * I.H := by
  have h : ∀ x ∈ Finset.range I.W, ∑ y ∈ Finset.range I.H,
      tileAt (kindOf I pd (x, y)) (L (x, y)) ≤ I.H := by
    intro x _
    calc ∑ y ∈ Finset.range I.H, tileAt (kindOf I pd (x, y)) (L (x, y))
        ≤ ∑ _y ∈ Finset.range I.H, 1 := Finset.sum_le_sum (fun y _ => by
          unfold tileAt; split <;> omega)
      _ = I.H := by simp
  calc tileCount I pd L ≤ ∑ _x ∈ Finset.range I.W, I.H := Finset.sum_le_sum h
    _ = I.W * I.H := by simp

theorem excAt_of (I : Instance) {pd : PD} (L : Cell → Lab) {x : Cell} {j : ℕ} {p : Cell}
    {dl : List (Cell × ℕ)} (hj : pd[j]? = some (p, dl)) {g d : ℕ} {δ : Dir}
    (hg : (tlookup x dl).val = some g) (hd : (L x).d j = some (d, δ)) :
    excAt (kindOf I pd x) (L x) j = d - g := by
  simp only [excAt, kindOf_p I pd x hj, pkOf, hg, hd]

theorem excAt_of_lookup_none (I : Instance) {pd : PD} (L : Cell → Lab) {x : Cell} {j : ℕ}
    {p : Cell} {dl : List (Cell × ℕ)} (hj : pd[j]? = some (p, dl))
    (hg : (tlookup x dl).val = none) : excAt (kindOf I pd x) (L x) j = 0 := by
  simp only [excAt, kindOf_p I pd x hj, pkOf, hg]

theorem excAt_of_entry_none (k : Kind) (a : Lab) {j : ℕ} (hd : a.d j = none) :
    excAt k a j = 0 := by
  simp only [excAt, hd]
  split <;> simp_all

/-- The certified tile count is the number of free cells with an edge bit. -/
theorem tileCount_eq_card (I : Instance) (pd : PD) (L : Cell → Lab) :
    tileCount I pd L = ((Finset.range I.W ×ˢ Finset.range I.H).filter
      (fun c => ((kindOf I pd c).free && (L c).any) = true)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  rfl

/-- The certified excess, summed port by port. -/
theorem excCount_eq (I : Instance) (pd : PD) (L : Cell → Lab) :
    excCount I pd L = ∑ j ∈ Finset.range pd.length,
      ∑ c ∈ Finset.range I.W ×ˢ Finset.range I.H, excAt (kindOf I pd c) (L c) j := by
  unfold excCount
  have h1 : ∀ x ∈ Finset.range I.W,
      ∑ y ∈ Finset.range I.H, ∑ j ∈ Finset.range pd.length,
        excAt (kindOf I pd (x, y)) (L (x, y)) j =
      ∑ j ∈ Finset.range pd.length, ∑ y ∈ Finset.range I.H,
        excAt (kindOf I pd (x, y)) (L (x, y)) j := fun x _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_product]

/-- Sum over the ports of an instance, re-indexed by position in the port list. -/
theorem sum_ports {I : Instance} {pd : PD} (hnd : (pd.map Prod.fst).Nodup)
    (hpf : (pd.map Prod.fst).toFinset = I.ports) (F : Cell → ℕ∞) :
    ∑ p ∈ I.ports, F p = ∑ j ∈ Finset.range pd.length, F (pd.getD j default).1 := by
  rw [← hpf, List.sum_toFinset F hnd, List.map_map]
  clear hnd hpf
  induction pd with
  | nil => simp
  | cons e pd ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
        List.getD_cons_succ, List.getD_cons_zero, Function.comp_apply, ih]
      rw [add_comm]

/-- A labelling `L` that passes all checks, together with the network `σ` it describes. -/
structure IsCert (I : Instance) (pd : PD) (β : ℕ) (L : Cell → Lab) (σ : Solution) : Prop where
  ok : GridOK β I.W I.H (kindOf I pd) L
  edges : ∀ a b, (a, b) ∈ σ.edges ↔
    I.InBounds a ∧ (((L a).eR = true ∧ b = (a.1 + 1, a.2)) ∨
      ((L a).eD = true ∧ b = (a.1, a.2 + 1)))

namespace IsCert

variable {I : Instance} {pd : PD} {β : ℕ} {L : Cell → Lab} {σ : Solution}

theorem unary (h : IsCert I pd β L σ) {x : Cell} (hx : I.InBounds x) :
    UnaryOK β (kindOf I pd x) (L x) :=
  h.ok.unary x.1 x.2 hx.1 hx.2

theorem mask (h : IsCert I pd β L σ) {x : Cell} (hx : I.InBounds x) {δ : Dir}
    (hδ : (L x).edge δ = true) : ∃ y, IsNb δ x y ∧ I.GridAdj x y :=
  (kindOf_allow I pd x δ).mp ((h.unary hx).mask δ hδ)

/-- The pair checks, for an arbitrary direction. -/
theorem dir (h : IsCert I pd β L σ) {δ : Dir} {x y : Cell} (hx : I.InBounds x)
    (hy : I.InBounds y) (hnb : IsNb δ x y) :
    (L x).edge δ = (L y).edge δ.opp ∧
    ∀ j, j < pd.length →
      predOK δ ((kindOf I pd x).p j) ((L x).d j) ((kindOf I pd y).p j) ((L y).d j) = true := by
  cases δ
  · have hnb' : y = (x.1 + 1, x.2) := hnb
    subst hnb'
    have hp := h.ok.across x.1 x.2 hy.1 hx.2
    refine ⟨hp.edge, fun j hj => ?_⟩
    have := hp.preds j (by rw [kindOf_pp_length]; exact hj)
    simp only [predAt, Bool.and_eq_true] at this
    exact this.1
  · have hnb' : y = (x.1, x.2 + 1) := hnb
    subst hnb'
    have hp := h.ok.within x.1 x.2 hx.1 hy.2
    refine ⟨hp.edge, fun j hj => ?_⟩
    have := hp.preds j (by rw [kindOf_pp_length]; exact hj)
    simp only [predAt, Bool.and_eq_true] at this
    exact this.1
  · have hnb' : x = (y.1 + 1, y.2) := hnb
    subst hnb'
    have hp := h.ok.across y.1 y.2 hx.1 hy.2
    refine ⟨hp.edge.symm, fun j hj => ?_⟩
    have := hp.preds j (by rw [kindOf_pp_length]; exact hj)
    simp only [predAt, Bool.and_eq_true] at this
    exact this.2
  · have hnb' : x = (y.1, y.2 + 1) := hnb
    subst hnb'
    have hp := h.ok.within y.1 y.2 hy.1 hx.2
    refine ⟨hp.edge.symm, fun j hj => ?_⟩
    have := hp.preds j (by rw [kindOf_pp_length]; exact hj)
    simp only [predAt, Bool.and_eq_true] at this
    exact this.2

/-- Network adjacency in terms of the edge bits. -/
theorem netAdj_iff (h : IsCert I pd β L σ) {a b : Cell} :
    σ.NetAdj a b ↔ ∃ δ, IsNb δ a b ∧ I.InBounds a ∧ I.InBounds b ∧ (L a).edge δ = true := by
  constructor
  · rintro (hab | hba)
    · obtain ⟨ha, ⟨he, rfl⟩ | ⟨he, rfl⟩⟩ := (h.edges a b).mp hab
      · obtain ⟨y, hy1, hy2⟩ := h.mask ha (δ := .R) he
        have hy : y = (a.1 + 1, a.2) := hy1
        subst hy
        exact ⟨.R, rfl, ha, hy2.2.2.1, he⟩
      · obtain ⟨y, hy1, hy2⟩ := h.mask ha (δ := .D) he
        have hy : y = (a.1, a.2 + 1) := hy1
        subst hy
        exact ⟨.D, rfl, ha, hy2.2.2.1, he⟩
    · obtain ⟨hb, ⟨he, rfl⟩ | ⟨he, rfl⟩⟩ := (h.edges b a).mp hba
      · obtain ⟨y, hy1, hy2⟩ := h.mask hb (δ := .R) he
        have hy : y = (b.1 + 1, b.2) := hy1
        subst hy
        have hd := (h.dir hb hy2.2.2.1 (δ := .R) rfl).1
        exact ⟨.L, rfl, hy2.2.2.1, hb, hd.symm.trans he⟩
      · obtain ⟨y, hy1, hy2⟩ := h.mask hb (δ := .D) he
        have hy : y = (b.1, b.2 + 1) := hy1
        subst hy
        have hd := (h.dir hb hy2.2.2.1 (δ := .D) rfl).1
        exact ⟨.U, rfl, hy2.2.2.1, hb, hd.symm.trans he⟩
  · rintro ⟨δ, hnb, ha, hb, he⟩
    cases δ
    · exact Or.inl ((h.edges a b).mpr ⟨ha, Or.inl ⟨he, hnb⟩⟩)
    · exact Or.inl ((h.edges a b).mpr ⟨ha, Or.inr ⟨he, hnb⟩⟩)
    · have hd := (h.dir ha hb (δ := .L) hnb).1
      exact Or.inr ((h.edges b a).mpr ⟨hb, Or.inl ⟨hd.symm.trans he, hnb⟩⟩)
    · have hd := (h.dir ha hb (δ := .U) hnb).1
      exact Or.inr ((h.edges b a).mpr ⟨hb, Or.inr ⟨hd.symm.trans he, hnb⟩⟩)

theorem gridAdj (h : IsCert I pd β L σ) {a b : Cell} (hab : σ.NetAdj a b) : I.GridAdj a b := by
  obtain ⟨δ, hnb, ha, -, he⟩ := h.netAdj_iff.mp hab
  obtain ⟨y, hy1, hy2⟩ := h.mask ha he
  rw [isNb_unique hnb hy1]
  exact hy2

theorem edges_gridAdj (h : IsCert I pd β L σ) : ∀ e ∈ σ.edges, I.GridAdj e.1 e.2 :=
  fun _ he => h.gridAdj (Or.inl he)

/-- The degree cap. -/
theorem deg (h : IsCert I pd β L σ) {x : Cell} (hx : I.IsFree x) :
    (σ.neighbours x).card ≤ β := by
  have hsub : σ.neighbours x ⊆
      (Finset.univ.filter (fun δ : Dir => (L x).edge δ = true)).image (fun δ => nbOf δ x) := by
    intro y hy
    obtain ⟨δ, hnb, -, -, he⟩ := h.netAdj_iff.mp (Solution.mem_neighbours.mp hy)
    exact Finset.mem_image.mpr
      ⟨δ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, ((isNb_iff.mp hnb).2).symm⟩
  calc (σ.neighbours x).card
      ≤ ((Finset.univ.filter (fun δ : Dir => (L x).edge δ = true)).image
          (fun δ => nbOf δ x)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun δ : Dir => (L x).edge δ = true)).card := Finset.card_image_le
    _ = (L x).deg := (Lab.deg_eq_card _).symm
    _ ≤ β := (h.unary hx.1).deg ((kindOf_free I pd x).mpr hx)

/-- Every entry `(d, _)` for port `j` is witnessed by a walk of length `d`. -/
theorem reach (h : IsCert I pd β L σ) {j : ℕ} {p : Cell} {dl : List (Cell × ℕ)}
    (hj : pd[j]? = some (p, dl)) :
    ∀ (d : ℕ) (x : Cell) (δ : Dir), I.InBounds x → (L x).d j = some (d, δ) →
      Reach I σ.NetAdj p d x := by
  have hjlt : j < pd.length := (List.getElem?_eq_some_iff.mp hj).1
  intro d
  induction d with
  | zero =>
      intro x δ hx hd
      have hu := (h.unary hx).entries j (by rw [kindOf_pp_length]; exact hjlt)
      rw [kindOf_p I pd x hj, hd] at hu
      by_cases hxp : x = p
      · subst hxp; exact Reach.zero
      · simp [entryOK, pkOf, hxp] at hu
  | succ d ih =>
      intro x δ hx hd
      have hu := (h.unary hx).entries j (by rw [kindOf_pp_length]; exact hjlt)
      rw [kindOf_p I pd x hj, hd] at hu
      by_cases hxp : x = p
      · simp [entryOK, pkOf, hxp] at hu
      · simp only [entryOK, pkOf, hxp, decide_false, Bool.false_eq_true, ite_false,
          Bool.and_eq_true] at hu
        have he : (L x).edge δ = true := hu.1.1
        obtain ⟨y, hnb, hadj⟩ := h.mask hx he
        have hy : I.InBounds y := hadj.2.2.1
        have hdir := h.dir hx hy hnb
        have hp := hdir.2 j hjlt
        rw [kindOf_p I pd x hj, kindOf_p I pd y hj, hd] at hp
        simp only [predOK, pkOf, hxp, decide_false, and_self, ite_true, Bool.and_eq_true,
          Bool.or_eq_true, decide_eq_true_eq] at hp
        obtain ⟨htr, hm⟩ := hp
        cases hdy : (L y).d j with
        | none => rw [hdy] at hm; simp at hm
        | some e =>
            obtain ⟨d', δ'⟩ := e
            rw [hdy] at hm
            have hdd : d' = d := by simpa using hm
            subst hdd
            have hry := ih y δ' hy hdy
            have hnet : σ.NetAdj y x :=
              h.netAdj_iff.mpr ⟨δ.opp, isNb_opp.mpr hnb, hy, hx, hdir.1.symm.trans he⟩
            refine Reach.step hry ?_ hnet
            rcases htr with hf | hyp
            · exact Or.inr hf
            · left
              have hu' := (h.unary hy).entries j (by rw [kindOf_pp_length]; exact hjlt)
              rw [kindOf_p I pd y hj, hdy] at hu'
              simpa [entryOK, pkOf, hyp] using hu'

/-- A chosen city carries an entry. -/
theorem dem_entry (h : IsCert I pd β L σ) {j : ℕ} {p : Cell} {dl : List (Cell × ℕ)}
    (hj : pd[j]? = some (p, dl)) {x : Cell} (hx : I.InBounds x) {g : ℕ}
    (hg : (tlookup x dl).val = some g) : ∃ d δ, (L x).d j = some (d, δ) := by
  have hjlt : j < pd.length := (List.getElem?_eq_some_iff.mp hj).1
  have hu := (h.unary hx).entries j (by rw [kindOf_pp_length]; exact hjlt)
  rw [kindOf_p I pd x hj] at hu
  cases hd : (L x).d j with
  | none => simp [entryOK, pkOf, hd, hg] at hu
  | some e => exact ⟨e.1, e.2, rfl⟩

/-- The certified tile count bounds the true one. -/
theorem tiles_le (h : IsCert I pd β L σ) : (σ.tiles I).card ≤ tileCount I pd L := by
  have hsub : σ.tiles I ⊆ (Finset.range I.W ×ˢ Finset.range I.H).filter
      (fun c => ((kindOf I pd c).free && (L c).any) = true) := by
    intro c hc
    simp only [Solution.tiles, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hc
    obtain ⟨hmem, hfree⟩ := hc
    have hin : I.InBounds c := hfree.1
    have hany : (L c).any = true := by
      rw [Lab.any_iff]
      rcases hmem with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · obtain ⟨δ, -, -, -, hδ⟩ := h.netAdj_iff.mp (Or.inl he : σ.NetAdj e.1 e.2)
        exact ⟨δ, hδ⟩
      · obtain ⟨δ, -, -, -, hδ⟩ := h.netAdj_iff.mp (Or.inr he : σ.NetAdj e.2 e.1)
        exact ⟨δ, hδ⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hin.1,
      Finset.mem_range.mpr hin.2⟩, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(kindOf_free I pd c).mpr hfree, hany⟩
  rw [tileCount_eq_card]
  exact Finset.card_le_card hsub

/-- The certified excess bounds the true one, when the demands of `pd` are the chosen
cities of `σ` with their grid distances. -/
theorem excess_le (h : IsCert I pd β L σ) (hnd : (pd.map Prod.fst).Nodup)
    (hpf : (pd.map Prod.fst).toFinset = I.ports)
    (hch : ∀ (j : ℕ) (p : Cell) (dl : List (Cell × ℕ)), pd[j]? = some (p, dl) →
      ∀ c ∈ σ.choice p,
        I.InBounds c ∧ ∃ g : ℕ, (tlookup c dl).val = some g ∧ I.gridDist p c = (g : ℕ∞)) :
    σ.excess I ≤ (excCount I pd L : ℕ∞) := by
  unfold Solution.excess
  rw [sum_ports hnd hpf]
  rw [excCount_eq, Nat.cast_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjlt : j < pd.length := Finset.mem_range.mp hj
  obtain ⟨⟨p, dl⟩, hpd⟩ : ∃ e, pd[j]? = some e := ⟨pd[j], List.getElem?_eq_getElem hjlt⟩
  have hget : (pd.getD j default).1 = p := by
    simp [List.getD_eq_getElem?_getD, hpd]
  rw [hget, Nat.cast_sum]
  have hsubset : σ.choice p ⊆ Finset.range I.W ×ˢ Finset.range I.H := by
    intro c hc
    have := (hch j p dl hpd c hc).1
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr this.1, Finset.mem_range.mpr this.2⟩
  calc ∑ c ∈ σ.choice p, (σ.netDist I p c - I.gridDist p c)
      ≤ ∑ c ∈ σ.choice p, ((excAt (kindOf I pd c) (L c) j : ℕ) : ℕ∞) := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        obtain ⟨hin, g, hg, hgd⟩ := hch j p dl hpd c hc
        obtain ⟨d, δ, hd⟩ := h.dem_entry hpd hin hg
        have hr := h.reach hpd d c δ hin hd
        have hle : σ.netDist I p c ≤ (d : ℕ∞) := walkDist_le_of_reach hr
        rw [excAt_of I L hpd hg hd, hgd]
        calc σ.netDist I p c - (g : ℕ∞) ≤ (d : ℕ∞) - (g : ℕ∞) := tsub_le_tsub_right hle _
          _ = ((d - g : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ∑ c ∈ Finset.range I.W ×ˢ Finset.range I.H,
          ((excAt (kindOf I pd c) (L c) j : ℕ) : ℕ∞) :=
        Finset.sum_le_sum_of_subset hsubset

end IsCert

end TrainNetwork
