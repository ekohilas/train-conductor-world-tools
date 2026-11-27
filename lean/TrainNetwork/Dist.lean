/-
Specification of the helper steps of `solve`: the cell list, the scans, the decoded edge
list, and `distT` (grid distances via the certificate DP without degree constraint).
-/
import TrainNetwork.Solve

namespace TrainNetwork

open TimeM

/-! ### Cells and scans -/

theorem cellsT_val (I : Instance) :
    (cellsT I).val = List.product (List.range I.W) (List.range I.H) := by
  simp only [cellsT, bind_val, pure_val, tmapM_val]
  rfl

theorem mem_cellsT {I : Instance} {c : Cell} : c ∈ (cellsT I).val ↔ I.InBounds c := by
  obtain ⟨x, y⟩ := c
  rw [cellsT_val]
  simp [Instance.InBounds]

theorem nodup_cellsT (I : Instance) : (cellsT I).val.Nodup := by
  rw [cellsT_val]
  exact List.Nodup.product List.nodup_range List.nodup_range

theorem scanT_val (s : Finset Cell) (cells : List Cell) :
    (scanT s cells).val = cells.filter (fun x => decide (x ∈ s)) := by
  simp [scanT]

theorem mem_scanT {I : Instance} {s : Finset Cell} (hs : ∀ x ∈ s, I.InBounds x) {x : Cell} :
    x ∈ (scanT s (cellsT I).val).val ↔ x ∈ s := by
  rw [scanT_val, List.mem_filter, mem_cellsT, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hs x h, h⟩⟩

theorem nodup_scanT (I : Instance) (s : Finset Cell) : (scanT s (cellsT I).val).val.Nodup := by
  rw [scanT_val]
  exact (nodup_cellsT I).filter _

theorem toFinset_scanT {I : Instance} {s : Finset Cell} (hs : ∀ x ∈ s, I.InBounds x) :
    (scanT s (cellsT I).val).val.toFinset = s := by
  ext x
  rw [List.mem_toFinset, mem_scanT hs]

/-! ### The edge list of a labelling -/

/-- The network edges described by a labelling. -/
def edgeList (L : Cell → Lab) (cells : List Cell) : List (Cell × Cell) :=
  (cells.map (fun x =>
    (if (L x).eR then [(x, (x.1 + 1, x.2))] else []) ++
    (if (L x).eD then [(x, (x.1, x.2 + 1))] else []))).flatten

theorem edgesT_val (I : Instance) (w : List (List Lab)) (cells : List Cell) :
    (edgesT I w cells).val = edgeList (labOf (decide (I.H ≤ I.W)) w) cells := by
  simp [edgesT, edgeList]

theorem mem_edgeList {L : Cell → Lab} {cells : List Cell} {a b : Cell} :
    (a, b) ∈ edgeList L cells ↔
      a ∈ cells ∧ (((L a).eR = true ∧ b = (a.1 + 1, a.2)) ∨
        ((L a).eD = true ∧ b = (a.1, a.2 + 1))) := by
  simp only [edgeList, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨x, hx, rfl⟩, hab⟩
    rcases List.mem_append.mp hab with h | h
    · by_cases hR : (L x).eR = true
      · simp only [hR, ite_true, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hx, Or.inl ⟨hR, rfl⟩⟩
      · simp [hR] at h
    · by_cases hD : (L x).eD = true
      · simp only [hD, ite_true, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hx, Or.inr ⟨hD, rfl⟩⟩
      · simp [hD] at h
  · rintro ⟨ha, ⟨hR, rfl⟩ | ⟨hD, rfl⟩⟩
    · exact ⟨_, ⟨a, ha, rfl⟩, List.mem_append_left _ (by simp [hR])⟩
    · exact ⟨_, ⟨a, ha, rfl⟩, List.mem_append_right _ (by simp [hD])⟩

/-- A labelling that passes all checks, with its decoded network, is a certificate. -/
theorem isCert_of {I : Instance} {pd : PD} {β : ℕ} {L : Cell → Lab}
    (hok : GridOK β I.W I.H (kindOf I pd) L) (ch : Cell → Finset Cell) :
    IsCert I pd β L ⟨(edgeList L (cellsT I).val).toFinset, ch⟩ :=
  ⟨hok, fun a b => by rw [List.mem_toFinset, mem_edgeList, mem_cellsT]⟩

/-! ### The full grid network -/

open Classical in
/-- All grid edges: the network in which network distance is grid distance. -/
noncomputable def fullNet (I : Instance) : Solution :=
  ⟨((Finset.range I.W ×ˢ Finset.range I.H) ×ˢ (Finset.range I.W ×ˢ Finset.range I.H)).filter
      (fun e => I.GridAdj e.1 e.2), fun _ => ∅⟩

theorem fullNet_edges (I : Instance) : ∀ e ∈ (fullNet I).edges, I.GridAdj e.1 e.2 := by
  intro e he
  simp only [fullNet, Finset.mem_filter] at he
  exact he.2

theorem fullNet_netAdj {I : Instance} {a b : Cell} : (fullNet I).NetAdj a b ↔ I.GridAdj a b := by
  constructor
  · exact netAdj_gridAdj (fullNet_edges I)
  · intro h
    left
    simp only [fullNet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨h.2.1.1, h.2.2.1⟩, h⟩

theorem fullNet_dist (I : Instance) (p c : Cell) : (fullNet I).netDist I p c = I.gridDist p c :=
  le_antisymm (walkDist_mono (fun _ _ h => fullNet_netAdj.mpr h))
    (walkDist_mono (fun _ _ h => fullNet_netAdj.mp h))

theorem card_neighbours_le_four {I : Instance} {τ : Solution}
    (hE : ∀ e ∈ τ.edges, I.GridAdj e.1 e.2) (x : Cell) : (τ.neighbours x).card ≤ 4 := by
  have hsub : τ.neighbours x ⊆ (Finset.univ : Finset Dir).image (fun δ => nbOf δ x) := by
    intro y hy
    obtain ⟨δ, hδ⟩ := adjacent_iff_isNb.mp (netAdj_gridAdj hE (Solution.mem_neighbours.mp hy)).1
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_univ _, ((isNb_iff.mp hδ).2).symm⟩
  calc (τ.neighbours x).card ≤ ((Finset.univ : Finset Dir).image (fun δ => nbOf δ x)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset Dir).card := Finset.card_image_le
    _ = 4 := rfl

/-! ### Grid distances by the DP -/

/-- `none` is "unreachable". -/
def oENat : Option ℕ → ℕ∞
  | none => ⊤
  | some d => (d : ℕ∞)

theorem lookup_single (x c : Cell) (g : ℕ) :
    (tlookup x [(c, g)]).val = if x = c then some g else none := by
  by_cases h : x = c <;> simp [tlookup, h]

/-- With the single demand `(p, c)` at reference distance `0`, the certified excess is
the entry of `c`. -/
theorem excCount_single (I : Instance) (p c : Cell) (L : Cell → Lab) (hc : I.InBounds c) :
    excCount I [(p, [(c, 0)])] L = excAt (kindOf I [(p, [(c, 0)])] c) (L c) 0 := by
  rw [excCount_eq]
  show ∑ j ∈ Finset.range 1, _ = _
  rw [Finset.sum_range_one]
  refine Finset.sum_eq_single c (fun x _ hx => ?_) (fun hnot => ?_)
  · refine excAt_of_lookup_none I L (p := p) (dl := [(c, 0)]) rfl ?_
    simp [lookup_single, hx]
  · exact absurd (Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hc.1, Finset.mem_range.mpr hc.2⟩) hnot

/-- Any labelling that passes the checks of a distance run certifies an upper bound on
the grid distance. -/
theorem dist_sound {I : Instance} {p c : Cell} (hc : I.InBounds c) {L : Cell → Lab}
    (hL : GridOK 4 I.W I.H (kindOf I [(p, [(c, 0)])]) L) :
    I.gridDist p c ≤ (excCount I [(p, [(c, 0)])] L : ℕ∞) := by
  have hcert := isCert_of hL (fun _ => ∅)
  have hpd : ([(p, [(c, 0)])] : PD)[0]? = some (p, [(c, 0)]) := rfl
  have hlook : (tlookup c [(c, 0)]).val = some 0 := by simp [lookup_single]
  obtain ⟨d, δ, hd⟩ := hcert.dem_entry hpd hc hlook
  have hr := hcert.reach hpd d c δ hc hd
  have hr' : Reach I I.GridAdj p d c := hr.mono (fun _ _ h => hcert.gridAdj h)
  rw [excCount_single I p c L hc, excAt_of I L hpd hlook hd]
  exact walkDist_le_of_reach hr'

/-- If the grid distance is finite, the exact distances in the full grid network form a
labelling in range that passes the checks and certifies exactly that distance. -/
theorem dist_complete {I : Instance} {p c : Cell} (hp : I.InBounds p) (hc : I.InBounds c)
    {g : ℕ} (hg : I.gridDist p c = (g : ℕ∞)) :
    ∃ L : Cell → Lab, GridOK 4 I.W I.H (kindOf I [(p, [(c, 0)])]) L ∧
      InRange I [(p, [(c, 0)])] L ∧ excCount I [(p, [(c, 0)])] L = g := by
  have hE := fullNet_edges I
  have hfin : (fullNet I).netDist I p c < ⊤ := by
    rw [fullNet_dist, hg]
    exact ENat.natCast_lt_top g
  have hdem : ∀ (j : ℕ) (p' : Cell) (dl : List (Cell × ℕ)) (x : Cell) (g' : ℕ),
      ([(p, [(c, 0)])] : PD)[j]? = some (p', dl) → (tlookup x dl).val = some g' →
      (fullNet I).netDist I p' x < ⊤ := by
    intro j p' dl x g' hj hl
    cases j with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        rw [lookup_single] at hl
        by_cases hx : x = c
        · rw [hx]; exact hfin
        · simp [hx] at hl
    | succ j => simp at hj
  refine ⟨certLab I (fullNet I) [(p, [(c, 0)])],
    certLab_ok hE (fun x _ => card_neighbours_le_four hE x) _ hdem, ?_, ?_⟩
  · intro x _
    refine ⟨certLab_ds_length _ x, fun en hen d δ hd => ?_⟩
    have := certLab_range hE [(p, [(c, 0)])] (by simpa using hp) x en hen d δ hd
    omega
  · have hpd : ([(p, [(c, 0)])] : PD)[0]? = some (p, [(c, 0)]) := rfl
    have hlook : (tlookup c [(c, 0)]).val = some 0 := by simp [lookup_single]
    have hd := certLab_d (I := I) (τ := fullNet I) [(p, [(c, 0)])] c hpd
    rw [certEntry_fin hfin] at hd
    rw [excCount_single I p c _ hc, excAt_of I _ hpd hlook hd, fullNet_dist, hg]
    simp

/-- `distT` computes the grid distance. -/
theorem distT_spec (I : Instance) {p c : Cell} (hp : I.InBounds p) (hc : I.InBounds c) :
    oENat (distT I p c).val = I.gridDist p c := by
  simp only [distT, bind_val, pure_val]
  cases hr : (dpRun I [(p, [(c, 0)])] 4).val with
  | none =>
      simp only [Option.map_none, oENat]
      by_contra hne
      obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp (Ne.symm hne)
      obtain ⟨L, hL, hrange, -⟩ := dist_complete hp hc hg.symm
      exact dpRun_none hr L hL hrange
  | some e =>
      obtain ⟨cost, w⟩ := e
      obtain ⟨hok, hcost, hmin⟩ := dpRun_some hr
      simp only [Option.map_some, oENat]
      set L := labOf (decide (I.H ≤ I.W)) w with hLdef
      have hsound := dist_sound hc hok
      have ht := tileCount_le I [(p, [(c, 0)])] L
      rw [gridCost_eq] at hcost
      have hdiv : cost / (I.W * I.H + 1) = excCount I [(p, [(c, 0)])] L := by
        rw [← hcost, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
          Nat.div_eq_of_lt (by omega), Nat.zero_add]
      rw [hdiv]
      refine le_antisymm ?_ hsound
      obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp
        (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsound)
      obtain ⟨L', hL', hrange', hexc'⟩ := dist_complete hp hc hg.symm
      have hle := hmin L' hL' hrange'
      rw [gridCost_eq, hexc', ← hcost] at hle
      have ht' := tileCount_le I [(p, [(c, 0)])] L'
      have hlt : excCount I [(p, [(c, 0)])] L < g + 1 := by
        by_contra hge
        have h1 : (g + 1) * (I.W * I.H + 1) ≤
            excCount I [(p, [(c, 0)])] L * (I.W * I.H + 1) :=
          Nat.mul_le_mul_right _ (not_lt.mp hge)
        nlinarith
      rw [← hg]
      exact_mod_cast Nat.lt_succ_iff.mp hlt

end TrainNetwork
