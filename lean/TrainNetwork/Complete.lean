/-
Completeness of the encoding: a feasible solution within the bounds yields a satisfying
assignment of `enc I X K`.
-/
import TrainNetwork.SoundMain

namespace TrainNetwork.Answer

open TrainNetwork

variable (I : Instance) (σ : Solution)

open Classical in
/-- The intended meaning of the variables of families 0-5, read off a solution. -/
noncomputable def baseAsg : ℕ → Bool := fun n =>
  let tg := n.unpair.1
  let m := n.unpair.2
  if tg = 0 then decide (σ.NetAdj (cellOf m.unpair.1) (cellOf m.unpair.2))
  else if tg = 1 then decide (cellOf m.unpair.2 ∈ σ.choice (cellOf m.unpair.1))
  else if tg = 2 then
    decide (I.reach I.GridAdj (cellOf m.unpair.1) m.unpair.2.unpair.1 (cellOf m.unpair.2.unpair.2))
  else if tg = 3 then
    decide (I.reach σ.NetAdj (cellOf m.unpair.1) m.unpair.2.unpair.1 (cellOf m.unpair.2.unpair.2))
  else if tg = 4 then
    decide (I.reach σ.NetAdj (cellOf m.unpair.1) m.unpair.2.unpair.1
        (cellOf m.unpair.2.unpair.2.unpair.2) ∧
      σ.NetAdj (cellOf m.unpair.2.unpair.2.unpair.2) (cellOf m.unpair.2.unpair.2.unpair.1))
  else if tg = 5 then decide (cellOf m ∈ σ.tiles I)
  else false

/-- The item list of the cardinality gadget with a given tag. -/
def itemsOf (tag : ℕ) : List (List Lit) :=
  if tag.unpair.1 = 0 then selItems I (cellOf tag.unpair.2) true
  else if tag.unpair.1 = 1 then selItems I (cellOf tag.unpair.2) false
  else if tag.unpair.1 = 2 then excessItems I
  else tileItems I

/-- The full assignment: counter variables count active items of their gadget. -/
noncomputable def fullAsg : ℕ → Bool := fun n =>
  if n.unpair.1 = 6 then
    decide (n.unpair.2.unpair.2.unpair.2 <
      cnt (baseAsg I σ) ((itemsOf I n.unpair.2.unpair.1).take n.unpair.2.unpair.2.unpair.1))
  else baseAsg I σ n

theorem netAdj_symm {x y : Cell} : σ.NetAdj x y ↔ σ.NetAdj y x := by
  unfold Solution.NetAdj; exact Or.comm

open Classical in
@[simp] theorem full_vEdge (u v : Cell) : fullAsg I σ (vEdge u v) = decide (σ.NetAdj u v) := by
  simp only [fullAsg, baseAsg, vEdge, Nat.unpair_pair]
  rcases le_total (cellCode u) (cellCode v) with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h, cellOf_cellCode]
    simp [netAdj_symm σ (x := v)]

open Classical in
@[simp] theorem full_vSel (p c : Cell) : fullAsg I σ (vSel p c) = decide (c ∈ σ.choice p) := by
  simp [fullAsg, baseAsg, vSel, Nat.unpair_pair]

open Classical in
@[simp] theorem full_vGrid (p : Cell) (t : ℕ) (v : Cell) :
    fullAsg I σ (vGrid p t v) = decide (I.reach I.GridAdj p t v) := by
  simp [fullAsg, baseAsg, vGrid, Nat.unpair_pair]

open Classical in
@[simp] theorem full_vNet (p : Cell) (t : ℕ) (v : Cell) :
    fullAsg I σ (vNet p t v) = decide (I.reach σ.NetAdj p t v) := by
  simp [fullAsg, baseAsg, vNet, Nat.unpair_pair]

open Classical in
@[simp] theorem full_vStep (p : Cell) (t : ℕ) (v u : Cell) :
    fullAsg I σ (vStep p t v u) = decide (I.reach σ.NetAdj p t u ∧ σ.NetAdj u v) := by
  simp [fullAsg, baseAsg, vStep, Nat.unpair_pair]

open Classical in
@[simp] theorem full_vTile (x : Cell) : fullAsg I σ (vTile x) = decide (x ∈ σ.tiles I) := by
  simp [fullAsg, baseAsg, vTile, Nat.unpair_pair]

theorem full_vCount (tag i j : ℕ) :
    fullAsg I σ (vCount tag i j) =
      decide (j < cnt (baseAsg I σ) ((itemsOf I tag).take i)) := by
  simp [fullAsg, vCount, Nat.unpair_pair]

theorem iact_congr (a b : ℕ → Bool) (it : List Lit) (h : ∀ l ∈ it, a l.1 = b l.1) :
    iact a it = iact b it := by
  rw [Bool.eq_iff_iff, iact_iff, iact_iff]
  constructor
  · intro H l hl; unfold LTrue; rw [← h l hl]; exact H l hl
  · intro H l hl; unfold LTrue; rw [h l hl]; exact H l hl

theorem cnt_congr (a b : ℕ → Bool) (items : List (List Lit))
    (h : ∀ it ∈ items, ∀ l ∈ it, a l.1 = b l.1) : cnt a items = cnt b items := by
  unfold cnt
  apply List.countP_congr
  intro it hit
  rw [iact_congr a b it (h it hit)]

theorem full_eq_base (n : ℕ) (h : n.unpair.1 ≠ 6) : fullAsg I σ n = baseAsg I σ n := by
  simp [fullAsg, h]

theorem itemsOf_no6 (tag : ℕ) : ∀ it ∈ itemsOf I tag, ∀ l ∈ it, l.1.unpair.1 ≠ 6 := by
  intro it hit l hl
  unfold itemsOf at hit
  split_ifs at hit
  · simp only [selItems, List.mem_map] at hit
    obtain ⟨c, _, rfl⟩ := hit
    simp at hl; subst hl; simp [vSel]
  · simp only [selItems, List.mem_map] at hit
    obtain ⟨c, _, rfl⟩ := hit
    simp at hl; subst hl; simp [vSel]
  · simp only [excessItems, List.mem_flatMap, List.mem_map] at hit
    obtain ⟨p, _, c, _, t, _, rfl⟩ := hit
    simp at hl
    rcases hl with rfl | rfl | rfl <;> simp [vSel, vGrid, vNet]
  · simp only [tileItems, List.mem_map] at hit
    obtain ⟨x, _, rfl⟩ := hit
    simp at hl; subst hl; simp [vTile]

theorem cnt_full_take (tag i : ℕ) :
    cnt (fullAsg I σ) ((itemsOf I tag).take i) = cnt (baseAsg I σ) ((itemsOf I tag).take i) := by
  apply cnt_congr
  intro it hit l hl
  exact full_eq_base I σ _ (itemsOf_no6 I tag it (List.mem_of_mem_take hit) l hl)

/-- The counter variables of gadget `tag` have their intended values. -/
theorem counter_hv (tag : ℕ) (items : List (List Lit)) (hitems : itemsOf I tag = items) :
    ∀ i j, fullAsg I σ (vCount tag i j) =
      decide (j < cnt (fullAsg I σ) (items.take i)) := by
  intro i j
  rw [full_vCount, ← hitems, cnt_full_take]

theorem netAdj_grid (hF : σ.Feasible I) {x y : Cell} (h : σ.NetAdj x y) :
    Adjacent x y ∧ I.IsOpen x ∧ I.IsOpen y := by
  rcases h with h | h
  · have := hF.1 _ h
    exact ⟨this.1, this.2.1, this.2.2⟩
  · have := hF.1 _ h
    exact ⟨adjacent_comm.mp this.1, this.2.2, this.2.1⟩

theorem mem_tiles (x : Cell) : x ∈ σ.tiles I ↔ I.IsFree x ∧ ∃ y, σ.NetAdj x y := by
  unfold Solution.tiles Solution.NetAdj
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨(⟨e, he, rfl⟩ | ⟨e, he, rfl⟩), hf⟩
    · exact ⟨hf, e.2, Or.inl he⟩
    · exact ⟨hf, e.1, Or.inr he⟩
  · rintro ⟨hf, y, (h | h)⟩
    · exact ⟨Or.inl ⟨(x, y), h, rfl⟩, hf⟩
    · exact ⟨Or.inr ⟨(y, x), h, rfl⟩, hf⟩

open Classical in
theorem full_sat_edge (hF : σ.Feasible I) : Sat (fullAsg I σ) (edgeClauses I) := by
  rw [sat_edgeClauses]
  intro v hv
  have hedge : ∀ u, Sat (fullAsg I σ) (edgeAt I v u) := by
    intro u
    rw [sat_edgeAt]
    simp only [full_vEdge, full_vTile, decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hno hadj => hno ⟨(netAdj_grid I σ hF hadj).2.1, (netAdj_grid I σ hF hadj).2.2⟩,
      fun _ _ hadj => ⟨fun hf => (mem_tiles I σ v).mpr ⟨hf, u, hadj⟩,
        fun hf => (mem_tiles I σ u).mpr ⟨hf, v, (netAdj_symm σ).mp hadj⟩⟩⟩
  refine ⟨hedge _, hedge _, ?_⟩
  rw [sat_degAt]
  intro hfree h1 h2
  simp only [full_vEdge, decide_eq_false_iff_not]
  by_contra hall
  push Not at hall
  have hsub : (nbrs v).toFinset ⊆ σ.neighbours v := by
    intro y hy
    rw [mem_neighbours]
    simp [nbrs, h1, h2] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2.1
    · exact hall.2.2.2
  have hcard : (nbrs v).toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup]
    · simp [nbrs, h1, h2]
    · simp [nbrs, h1, h2]
      omega
  have h3 := Finset.card_le_card hsub
  have h4 := hF.2.1 v hfree
  omega

open Classical in
theorem full_sat_init (p : Cell) : Sat (fullAsg I σ) (initClauses I p) := by
  rw [sat_initClauses]
  intro v _
  simp only [full_vGrid, full_vNet, decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨fun h => h, fun h => ⟨h, h⟩⟩

open Classical in
theorem full_sat_reach (hF : σ.Feasible I) (p : Cell) :
    Sat (fullAsg I σ) (reachClauses I p) := by
  rw [sat_reachClauses]
  intro t _ v _
  rw [sat_stepClauses]
  simp only [full_vGrid, full_vNet, full_vStep, full_vEdge, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · show (I.reach I.GridAdj p t v ∨
      ∃ u, I.reach I.GridAdj p t u ∧ (u = p ∨ I.IsFree u) ∧ I.GridAdj u v) ↔ _
    apply or_congr_right
    constructor
    · rintro ⟨u, hr, hok, hadj⟩
      exact ⟨u, (mem_stepsG I p u v).mpr ⟨hok, hadj⟩, hr⟩
    · rintro ⟨u, hu, hr⟩
      rw [mem_stepsG] at hu
      exact ⟨u, hr, hu.1, hu.2⟩
  · rintro (h | ⟨u, hr, hok, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, (mem_stepsN I p u v).mpr ⟨(netAdj_grid I σ hF hadj).1, hok⟩, hr, hadj⟩
  · intro u _ h
    exact h

open Classical in
theorem full_sat_fin (hF : σ.Feasible I) {p : Cell} (hp : p ∈ I.ports) :
    Sat (fullAsg I σ) (finClauses I p) := by
  rw [sat_finClauses]
  intro c _ hc
  simp only [full_vSel, full_vGrid, full_vNet, decide_eq_true_eq] at hc ⊢
  constructor
  · obtain ⟨n, hn⟩ := (I.walkDist_lt_top_iff I.GridAdj p c).mp ((hF.2.2.1 p hp).2.2.1 c hc)
    exact I.reach_horizon (I.ports_inBounds p hp) (fun u v huv => huv.2.2.1) n c hn
  · obtain ⟨n, hn⟩ := (I.walkDist_lt_top_iff σ.NetAdj p c).mp (hF.2.2.2 p hp c hc)
    exact I.reach_horizon (I.ports_inBounds p hp)
      (fun u v huv => (netAdj_grid I σ hF huv).2.2.1) n c hn

open Classical in
theorem full_sat_near (hF : σ.Feasible I) {p : Cell} (hp : p ∈ I.ports) :
    Sat (fullAsg I σ) (nearClauses I p) := by
  rw [sat_nearClauses]
  intro c _ c2 hc2 t _ hs hs2 hg
  simp only [full_vSel, full_vGrid, decide_eq_true_eq, decide_eq_false_iff_not] at hs hs2 hg ⊢
  have hle := (hF.2.2.1 p hp).2.2.2 c hs c2 ((mem_cityL I c2).mp hc2) hs2
  have h2 : I.gridDist p c2 ≤ t := (I.walkDist_le_iff I.GridAdj p c2 t).mpr hg
  exact (I.walkDist_le_iff I.GridAdj p c t).mp (le_trans hle h2)

open Classical in
theorem full_sat_card (hF : σ.Feasible I) {p : Cell} (hp : p ∈ I.ports) :
    Sat (fullAsg I σ) (cardClauses I p) := by
  unfold cardClauses
  rw [sat_append]
  have hch := hF.2.2.1 p hp
  have e1 : (cityL I).countP (fun c => decide (c ∈ σ.choice p)) = I.k := by
    rw [← card_filter_cities, ← hch.2.1]
    congr 1
    ext c
    simp only [Finset.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun h => hch.1 h
  have hsum := countP_add_countP_not (fun c => decide (c ∈ σ.choice p)) (cityL I)
  constructor
  · apply atMost_complete
    · exact counter_hv I σ _ _ (by simp [itemsOf])
    · rw [cnt_selItems]
      have : (fun c => fullAsg I σ (vSel p c) == true) = fun c => decide (c ∈ σ.choice p) := by
        funext c; simp
      rw [this, e1]
  · apply atMost_complete
    · exact counter_hv I σ _ _ (by simp [itemsOf])
    · rw [cnt_selItems]
      have : (fun c => fullAsg I σ (vSel p c) == false) =
          fun c => !decide (c ∈ σ.choice p) := by
        funext c; simp
      rw [this]
      omega

theorem full_sat_port (hF : σ.Feasible I) {p : Cell} (hp : p ∈ I.ports) :
    Sat (fullAsg I σ) (portClauses I p) := by
  rw [sat_portClauses]
  exact ⟨full_sat_init I σ p, full_sat_reach I σ hF p, full_sat_fin I σ hF hp,
    full_sat_near I σ hF hp, full_sat_card I σ hF hp⟩

open Classical in
theorem full_sat_excess (hF : σ.Feasible I) (X : ℕ) (hX : σ.excess I ≤ X) :
    Sat (fullAsg I σ) (atMost (vCount (Nat.pair 2 0)) X (excessItems I)) := by
  apply atMost_complete
  · exact counter_hv I σ _ _ (by simp [itemsOf])
  · rw [cnt_excessItems]
    have hle : (((((portL I).map fun p => ((cityL I).map fun c =>
        (List.range (I.W * I.H)).countP (exPred (fullAsg I σ) p c)).sum).sum : ℕ)) : ℕ∞) ≤
        σ.excess I := by
      unfold Solution.excess
      rw [sum_ports]
      apply cast_le_list_sum
      intro p hp
      rw [mem_portL] at hp
      have hch := hF.2.2.1 p hp
      have hfil : σ.choice p = I.cities.filter (fun c => c ∈ σ.choice p) := by
        ext c
        simp only [Finset.mem_filter, iff_and_self]
        exact fun h => hch.1 h
      rw [hfil, Finset.sum_filter, sum_cities]
      apply cast_le_list_sum
      intro c _
      split_ifs with hs
      · have hnd : σ.netDist I p c < ⊤ := hF.2.2.2 p hp c hs
        have hgd : I.gridDist p c < ⊤ := hch.2.2.1 c hs
        obtain ⟨n, hn_eq⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hnd)
        obtain ⟨d, hd_eq⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hgd)
        rw [← hn_eq, ← hd_eq, ← ENat.natCast_sub]
        refine Nat.cast_le.mpr (countP_range_le _ d n _ ?_)
        intro t _ ht
        simp only [exPred, full_vSel, full_vGrid, full_vNet, Bool.and_eq_true,
          decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at ht
        obtain ⟨⟨_, hg⟩, hnn⟩ := ht
        constructor
        · have h1 : I.gridDist p c ≤ t := (I.walkDist_le_iff I.GridAdj p c t).mpr hg
          rw [← hd_eq] at h1
          exact_mod_cast h1
        · by_contra hnt
          apply hnn
          apply (I.walkDist_le_iff σ.NetAdj p c t).mp
          show σ.netDist I p c ≤ _
          rw [← hn_eq]
          exact_mod_cast (not_lt.mp hnt)
      · have hz : (List.range (I.W * I.H)).countP (exPred (fullAsg I σ) p c) = 0 := by
          rw [List.countP_eq_zero]
          intro t _
          simp [exPred, hs]
        rw [hz]
        simp
    exact_mod_cast le_trans hle hX

open Classical in
theorem full_sat_tiles (K : ℕ) (hK : (σ.tiles I).card ≤ K) :
    Sat (fullAsg I σ) (atMost (vCount (Nat.pair 3 0)) K (tileItems I)) := by
  apply atMost_complete
  · exact counter_hv I σ _ _ (by simp [itemsOf])
  · rw [cnt_tileItems]
    have : (fun x => fullAsg I σ (vTile x)) = fun x => decide (x ∈ σ.tiles I) := by
      funext x; simp
    rw [this, List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup ((nodup_cells I).filter _)]
    refine le_trans (Finset.card_le_card ?_) hK
    intro x hx
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2

/-- Completeness: a feasible solution within the bounds gives a satisfying assignment. -/
theorem enc_complete (X K : ℕ) (h : Decide I X K) : ∃ a, Sat a (enc I X K) := by
  obtain ⟨σ, hF, hX, hK⟩ := h
  exact ⟨fullAsg I σ, (sat_enc I _ X K).mpr ⟨full_sat_edge I σ hF,
    fun p hp => full_sat_port I σ hF ((mem_portL I p).mp hp),
    full_sat_excess I σ hF X hX, full_sat_tiles I σ K hK⟩⟩

/-- The formula `enc I X K` is satisfiable iff the instance is a yes-instance. -/
theorem enc_correct (X K : ℕ) : Decide I X K ↔ ∃ a, Sat a (enc I X K) :=
  ⟨enc_complete I X K, fun ⟨a, h⟩ => enc_sound I a X K h⟩

end TrainNetwork.Answer
