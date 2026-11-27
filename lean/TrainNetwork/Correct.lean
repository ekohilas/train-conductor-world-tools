/-
Correctness of `Answer.solve`: it returns an optimal solution, or `none` exactly when no
feasible solution exists. (The bounds on the number of ports and cities are not needed
for correctness, only for the running time.)
-/
import TrainNetwork.Dist

namespace TrainNetwork

open TimeM

/-! ### Reachable cities with their distances -/

theorem distsT_val (I : Instance) (cities : List Cell) (p : Cell) :
    (distsT I cities p).val =
      cities.filterMap (fun c => (distT I p c).val.map (fun g => (c, g))) := by
  simp only [distsT, bind_val, pure_val, tmapM_val, List.filterMap_map]
  rfl

theorem mem_distsT {I : Instance} {cities : List Cell} {p c : Cell} {g : ℕ} :
    (c, g) ∈ (distsT I cities p).val ↔ c ∈ cities ∧ (distT I p c).val = some g := by
  rw [distsT_val, List.mem_filterMap]
  constructor
  · rintro ⟨c', hc', h⟩
    cases hd : (distT I p c').val with
    | none => rw [hd] at h; simp at h
    | some g' =>
        rw [hd] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hc', hd⟩
  · rintro ⟨hc, hd⟩
    exact ⟨c, hc, by rw [hd]; rfl⟩

theorem distsT_keys (I : Instance) (cities : List Cell) (p : Cell) :
    (distsT I cities p).val.map Prod.fst =
      cities.filter (fun c => (distT I p c).val.isSome) := by
  rw [distsT_val]
  induction cities with
  | nil => rfl
  | cons c cs ih =>
      cases hd : (distT I p c).val <;> simp [hd, ih]

/-- The list of cities and the list of ports of an instance. -/
def citiesL (I : Instance) : List Cell := (scanT I.cities (cellsT I).val).val
def portsL (I : Instance) : List Cell := (scanT I.ports (cellsT I).val).val

/-- The reachable cities of `p` with their distances. -/
def finOf (I : Instance) (p : Cell) : List (Cell × ℕ) := (distsT I (citiesL I) p).val

theorem mem_citiesL {I : Instance} {c : Cell} : c ∈ citiesL I ↔ c ∈ I.cities :=
  mem_scanT I.cities_inBounds

theorem mem_portsL {I : Instance} {p : Cell} : p ∈ portsL I ↔ p ∈ I.ports :=
  mem_scanT I.ports_inBounds

theorem oENat_eq_coe {o : Option ℕ} {g : ℕ} : oENat o = (g : ℕ∞) ↔ o = some g := by
  cases o with
  | none => simp [oENat]
  | some d => simp [oENat]

/-- What the algorithm knows about the reachable cities of a port. -/
structure FinSpec (I : Instance) (p : Cell) (fin : List (Cell × ℕ)) : Prop where
  mem : ∀ (c : Cell) (g : ℕ), (c, g) ∈ fin ↔ c ∈ I.cities ∧ I.gridDist p c = (g : ℕ∞)
  nodup : (fin.map Prod.fst).Nodup

theorem finSpec_finOf (I : Instance) {p : Cell} (hp : p ∈ I.ports) : FinSpec I p (finOf I p) := by
  constructor
  · intro c g
    unfold finOf
    rw [mem_distsT, mem_citiesL]
    constructor
    · rintro ⟨hc, hd⟩
      refine ⟨hc, ?_⟩
      rw [← distT_spec I (I.ports_inBounds p hp) (I.cities_inBounds c hc), hd]
      rfl
    · rintro ⟨hc, hd⟩
      refine ⟨hc, ?_⟩
      rw [← distT_spec I (I.ports_inBounds p hp) (I.cities_inBounds c hc)] at hd
      exact oENat_eq_coe.mp hd
  · unfold finOf
    rw [distsT_keys]
    exact (nodup_scanT I I.cities).filter _

/-! ### The nearest-choice test -/

theorem nearRowT_val (S : List (Cell × ℕ)) (g : ℕ) (fin : List (Cell × ℕ)) :
    (nearRowT S g fin).val = true ↔ ∀ e' ∈ fin, e' ∈ S ∨ g ≤ e'.2 := by
  induction fin with
  | nil => simp [nearRowT]
  | cons e fin ih =>
      simp only [nearRowT, bind_val, pure_val, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, ih, List.mem_cons, forall_eq_or_imp]

theorem nearAllT_val (S fin rest : List (Cell × ℕ)) :
    (nearAllT S fin rest).val = true ↔ ∀ e ∈ rest, ∀ e' ∈ fin, e' ∈ S ∨ e.2 ≤ e'.2 := by
  induction rest with
  | nil => simp [nearAllT]
  | cons e rest ih =>
      simp only [nearAllT, bind_val, pure_val, Bool.and_eq_true, nearRowT_val, ih,
        List.mem_cons, forall_eq_or_imp]

theorem nearT_val (k : ℕ) (fin S : List (Cell × ℕ)) :
    (nearT k fin S).val = true ↔
      S.length = k ∧ ∀ e ∈ S, ∀ e' ∈ fin, e' ∈ S ∨ e.2 ≤ e'.2 := by
  simp only [nearT, bind_val, pure_val, Bool.and_eq_true, decide_eq_true_eq, nearAllT_val]

theorem mem_map_fst_toFinset {S : List (Cell × ℕ)} {c : Cell} :
    c ∈ (S.map Prod.fst).toFinset ↔ ∃ g, (c, g) ∈ S := by
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, he⟩
  · rintro ⟨g, hg⟩
    exact ⟨(c, g), hg, rfl⟩

/-- A sub-list that passes the test is a valid nearest choice. -/
theorem nearest_of_near {I : Instance} {p : Cell} {fin S : List (Cell × ℕ)}
    (hf : FinSpec I p fin) (hS : S.Sublist fin) (hn : (nearT I.k fin S).val = true) :
    I.IsNearestChoice p (S.map Prod.fst).toFinset := by
  rw [nearT_val] at hn
  obtain ⟨hlen, hall⟩ := hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨g, hg⟩ := mem_map_fst_toFinset.mp hc
    exact ((hf.mem c g).mp (hS.subset hg)).1
  · rw [List.toFinset_card_of_nodup (hf.nodup.sublist (hS.map Prod.fst)), List.length_map, hlen]
  · intro c hc
    obtain ⟨g, hg⟩ := mem_map_fst_toFinset.mp hc
    rw [((hf.mem c g).mp (hS.subset hg)).2]
    exact ENat.natCast_lt_top g
  · intro c hc c' hc' hnot
    obtain ⟨g, hg⟩ := mem_map_fst_toFinset.mp hc
    rw [((hf.mem c g).mp (hS.subset hg)).2]
    by_cases hfin : I.gridDist p c' = ⊤
    · rw [hfin]
      exact le_top
    · obtain ⟨g', hg'⟩ := ENat.ne_top_iff_exists.mp hfin
      have hmem' : (c', g') ∈ fin := (hf.mem c' g').mpr ⟨hc', hg'.symm⟩
      rcases hall (c, g) hg (c', g') hmem' with h | h
      · exact absurd (mem_map_fst_toFinset.mpr ⟨g', h⟩) hnot
      · rw [← hg']
        exact_mod_cast h

/-- Every valid nearest choice is found among the sub-lists that pass the test. -/
theorem near_of_nearest {I : Instance} {p : Cell} {fin : List (Cell × ℕ)} {T : Finset Cell}
    (hf : FinSpec I p fin) (hT : I.IsNearestChoice p T) :
    (fin.filter (fun e => decide (e.1 ∈ T))).Sublist fin ∧
    (nearT I.k fin (fin.filter (fun e => decide (e.1 ∈ T)))).val = true ∧
    ((fin.filter (fun e => decide (e.1 ∈ T))).map Prod.fst).toFinset = T := by
  obtain ⟨hsub, hcard, hfinite, hcmp⟩ := hT
  have hSsub : (fin.filter (fun e => decide (e.1 ∈ T))).Sublist fin := List.filter_sublist
  have hmemS : ∀ e, e ∈ fin.filter (fun e => decide (e.1 ∈ T)) ↔ e ∈ fin ∧ e.1 ∈ T := by
    intro e
    rw [List.mem_filter, decide_eq_true_eq]
  have hset : ((fin.filter (fun e => decide (e.1 ∈ T))).map Prod.fst).toFinset = T := by
    ext c
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ((hmemS e).mp he).2
    · intro hc
      obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp (hfinite c hc).ne
      exact ⟨(c, g), (hmemS _).mpr ⟨(hf.mem c g).mpr ⟨hsub hc, hg.symm⟩, hc⟩, rfl⟩
  refine ⟨hSsub, ?_, hset⟩
  rw [nearT_val]
  constructor
  · have hnd := hf.nodup.sublist (hSsub.map Prod.fst)
    have h1 := List.toFinset_card_of_nodup hnd
    rw [hset, hcard, List.length_map] at h1
    exact h1.symm
  · intro e he e' he'
    by_cases h : e'.1 ∈ T
    · exact Or.inl ((hmemS e').mpr ⟨he', h⟩)
    · right
      obtain ⟨hefin, heT⟩ := (hmemS e).mp he
      have h1 := (hf.mem e.1 e.2).mp hefin
      have h2 := (hf.mem e'.1 e'.2).mp he'
      have h3 := hcmp e.1 heT e'.1 h2.1 h
      rw [h1.2, h2.2] at h3
      exact_mod_cast h3

/-! ### Choices and their combinations -/

theorem mem_choicesT {I : Instance} {cities : List Cell} {p : Cell}
    {e : Cell × List (Cell × ℕ)} :
    e ∈ (choicesT I cities p).val ↔
      e.1 = p ∧ e.2.Sublist (distsT I cities p).val ∧
        (nearT I.k (distsT I cities p).val e.2).val = true := by
  simp only [choicesT, bind_val, tmapM_val, tfilterM_val, tsublists_val, pure_val,
    List.mem_map, List.mem_filter, List.mem_sublists']
  constructor
  · rintro ⟨S, ⟨hS, hn⟩, rfl⟩
    exact ⟨rfl, hS, hn⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨e.2, ⟨h2, h3⟩, by rw [← h1]⟩

theorem mem_familiesT {I : Instance} {cities ports : List Cell} {pd : PD} :
    pd ∈ (familiesT I cities ports).val ↔
      List.Forall₂ (fun e p => e ∈ (choicesT I cities p).val) pd ports := by
  simp only [familiesT, bind_val, tsections_val, tmapM_val, List.mem_sections,
    List.forall₂_map_right_iff]

/-- All combinations of valid choices. -/
def famsOf (I : Instance) : List PD := (familiesT I (citiesL I) (portsL I)).val

theorem forall₂_choices {I : Instance} {cities : List Cell} :
    ∀ {pd : PD} {ports : List Cell},
      List.Forall₂ (fun e p => e ∈ (choicesT I cities p).val) pd ports →
      pd.map Prod.fst = ports ∧ ∀ e ∈ pd, e.2.Sublist (distsT I cities e.1).val ∧
        (nearT I.k (distsT I cities e.1).val e.2).val = true
  | [], [], _ => by simp
  | e :: pd, p :: ports, h => by
      rw [List.forall₂_cons] at h
      obtain ⟨he, hrest⟩ := h
      obtain ⟨h1, h2⟩ := forall₂_choices hrest
      obtain ⟨hp, hs, hn⟩ := mem_choicesT.mp he
      refine ⟨by simp [hp, h1], ?_⟩
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · rw [hp]
        exact ⟨hs, hn⟩
      · exact h2 e' he'

/-- What membership in `famsOf` gives. -/
theorem famsOf_spec {I : Instance} {pd : PD} (h : pd ∈ famsOf I) :
    pd.map Prod.fst = portsL I ∧ ∀ e ∈ pd, e.2.Sublist (finOf I e.1) ∧
      (nearT I.k (finOf I e.1) e.2).val = true :=
  forall₂_choices (mem_familiesT.mp h)

/-! ### `bestT` -/

theorem bestT_cons (I : Instance) (pd : PD) (rest : List PD) :
    (bestT I (pd :: rest)).val =
      match (dpRun I pd 3).val with
      | none => (bestT I rest).val
      | some (c, w) =>
          match (bestT I rest).val with
          | none => some (c, pd, w)
          | some (c', pd', w') => if c ≤ c' then some (c, pd, w) else some (c', pd', w') := by
  simp only [bestT, bind_val]
  cases (dpRun I pd 3).val with
  | none => rfl
  | some e =>
      obtain ⟨c, w⟩ := e
      cases (bestT I rest).val with
      | none => rfl
      | some e' =>
          obtain ⟨c', pd', w'⟩ := e'
          by_cases hc : c ≤ c' <;> simp [hc]

theorem bestT_none {I : Instance} {fams : List PD} (h : (bestT I fams).val = none) :
    ∀ pd ∈ fams, (dpRun I pd 3).val = none := by
  induction fams with
  | nil => simp
  | cons pd rest ih =>
      rw [bestT_cons] at h
      cases hd : (dpRun I pd 3).val with
      | none =>
          rw [hd] at h
          intro pd' hpd'
          rcases List.mem_cons.mp hpd' with rfl | hpd'
          · exact hd
          · exact ih h pd' hpd'
      | some e =>
          obtain ⟨c, w⟩ := e
          rw [hd] at h
          cases hr : (bestT I rest).val with
          | none => rw [hr] at h; simp at h
          | some e' =>
              obtain ⟨c', pd', w'⟩ := e'
              rw [hr] at h
              by_cases hc : c ≤ c' <;> simp [hc] at h

theorem bestT_some {I : Instance} {fams : List PD} {c : ℕ} {pd : PD} {w : List (List Lab)}
    (h : (bestT I fams).val = some (c, pd, w)) :
    pd ∈ fams ∧ (dpRun I pd 3).val = some (c, w) ∧
      ∀ pd' ∈ fams, ∀ (c' : ℕ) (w' : List (List Lab)),
        (dpRun I pd' 3).val = some (c', w') → c ≤ c' := by
  induction fams generalizing c pd w with
  | nil => simp [bestT] at h
  | cons pd₀ rest ih =>
      rw [bestT_cons] at h
      cases hd : (dpRun I pd₀ 3).val with
      | none =>
          rw [hd] at h
          obtain ⟨h1, h2, h3⟩ := ih h
          refine ⟨List.mem_cons_of_mem _ h1, h2, ?_⟩
          intro pd' hpd' c' w' hrun
          rcases List.mem_cons.mp hpd' with rfl | hpd'
          · rw [hd] at hrun
            exact absurd hrun (by simp)
          · exact h3 pd' hpd' c' w' hrun
      | some e =>
          obtain ⟨c₀, w₀⟩ := e
          rw [hd] at h
          cases hr : (bestT I rest).val with
          | none =>
              rw [hr] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              refine ⟨by simp, hd, ?_⟩
              intro pd' hpd' c' w' hrun
              rcases List.mem_cons.mp hpd' with rfl | hpd'
              · rw [hd] at hrun
                simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                omega
              · rw [bestT_none hr pd' hpd'] at hrun
                exact absurd hrun (by simp)
          | some e' =>
              obtain ⟨c₁, pd₁, w₁⟩ := e'
              rw [hr] at h
              obtain ⟨h1, h2, h3⟩ := ih hr
              by_cases hc : c₀ ≤ c₁
              · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                refine ⟨by simp, hd, ?_⟩
                intro pd' hpd' c' w' hrun
                rcases List.mem_cons.mp hpd' with rfl | hpd'
                · rw [hd] at hrun
                  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                  omega
                · exact le_trans hc (h3 pd' hpd' c' w' hrun)
              · simp only [hc, ite_false, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                refine ⟨List.mem_cons_of_mem _ h1, h2, ?_⟩
                intro pd' hpd' c' w' hrun
                rcases List.mem_cons.mp hpd' with rfl | hpd'
                · rw [hd] at hrun
                  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                  omega
                · exact h3 pd' hpd' c' w' hrun

/-! ### The returned solution -/

/-- The choice function returned by `solve`. -/
def choiceOf (pd : PD) : Cell → Finset Cell :=
  fun p => ((tlookup p (choiceTableT pd).val).val).getD ∅

/-- The solution decoded from a labelling and a choice combination. -/
def solOf (I : Instance) (pd : PD) (L : Cell → Lab) : Solution :=
  ⟨(edgeList L (cellsT I).val).toFinset, choiceOf pd⟩

theorem choiceOf_eq {pd : PD} (hnd : (pd.map Prod.fst).Nodup) {p : Cell}
    {dl : List (Cell × ℕ)} (h : (p, dl) ∈ pd) :
    choiceOf pd p = (dl.map Prod.fst).toFinset := by
  have hval : (choiceTableT pd).val = pd.map (fun e => (e.1, (e.2.map Prod.fst).toFinset)) := by
    simp [choiceTableT]
  have hkeys : ((choiceTableT pd).val.map Prod.fst) = pd.map Prod.fst := by
    rw [hval, List.map_map]
    rfl
  have hmem : (p, (dl.map Prod.fst).toFinset) ∈ (choiceTableT pd).val := by
    rw [hval]
    exact List.mem_map.mpr ⟨(p, dl), h, rfl⟩
  unfold choiceOf
  rw [tlookup_of_mem (by rw [hkeys]; exact hnd) hmem]
  rfl

theorem solve_val (I : Instance) :
    (Answer.solve I).val =
      match (bestT I (famsOf I)).val with
      | none => none
      | some (_, pd, w) => some (solOf I pd (labOf (decide (I.H ≤ I.W)) w)) := by
  simp only [Answer.solve, bind_val]
  cases h : (bestT I (famsOf I)).val with
  | none =>
      simp only [famsOf, citiesL, portsL] at h
      rw [h]
      rfl
  | some e =>
      obtain ⟨c, pd, w⟩ := e
      simp only [famsOf, citiesL, portsL] at h
      rw [h]
      simp only [bind_val, pure_val, edgesT_val]
      rfl

/-! ### Soundness of a returned labelling -/

theorem nodup_portsL (I : Instance) : (portsL I).Nodup := nodup_scanT I I.ports

theorem toFinset_portsL (I : Instance) : (portsL I).toFinset = I.ports :=
  toFinset_scanT I.ports_inBounds

/-- Facts about one port entry of a choice combination. -/
theorem fam_entry {I : Instance} {pd : PD} (hpd : pd ∈ famsOf I) {p : Cell}
    {dl : List (Cell × ℕ)} (he : (p, dl) ∈ pd) :
    p ∈ I.ports ∧ dl.Sublist (finOf I p) ∧ (nearT I.k (finOf I p) dl).val = true ∧
      (dl.map Prod.fst).Nodup := by
  obtain ⟨h1, h2⟩ := famsOf_spec hpd
  have hp : p ∈ I.ports := by
    rw [← mem_portsL, ← h1]
    exact List.mem_map.mpr ⟨(p, dl), he, rfl⟩
  obtain ⟨hs, hn⟩ := h2 (p, dl) he
  exact ⟨hp, hs, hn, (finSpec_finOf I hp).nodup.sublist (hs.map Prod.fst)⟩

/-- A labelling that passes all checks for a choice combination decodes to a feasible
solution whose true cost is bounded by the certified cost. -/
theorem sound_family {I : Instance} {pd : PD} (hpd : pd ∈ famsOf I) {L : Cell → Lab}
    (hL : GridOK 3 I.W I.H (kindOf I pd) L) :
    (solOf I pd L).Feasible I ∧ (solOf I pd L).excess I ≤ (excCount I pd L : ℕ∞) ∧
      ((solOf I pd L).tiles I).card ≤ tileCount I pd L := by
  have hcert : IsCert I pd 3 L (solOf I pd L) := isCert_of hL (choiceOf pd)
  obtain ⟨hfst, -⟩ := famsOf_spec hpd
  have hnd : (pd.map Prod.fst).Nodup := by rw [hfst]; exact nodup_portsL I
  have hpf : (pd.map Prod.fst).toFinset = I.ports := by rw [hfst]; exact toFinset_portsL I
  have hchoice : ∀ {p : Cell} {dl : List (Cell × ℕ)}, (p, dl) ∈ pd →
      (solOf I pd L).choice p = (dl.map Prod.fst).toFinset := fun he => choiceOf_eq hnd he
  -- every chosen city carries a demand with the right distance
  have hdem : ∀ {p : Cell} {dl : List (Cell × ℕ)}, (p, dl) ∈ pd →
      ∀ c ∈ (solOf I pd L).choice p,
        I.InBounds c ∧ ∃ g : ℕ, (tlookup c dl).val = some g ∧ I.gridDist p c = (g : ℕ∞) := by
    intro p dl he c hc
    rw [hchoice he] at hc
    obtain ⟨g, hg⟩ := mem_map_fst_toFinset.mp hc
    obtain ⟨hp, hs, -, hdlnd⟩ := fam_entry hpd he
    obtain ⟨hcity, hdist⟩ := ((finSpec_finOf I hp).mem c g).mp (hs.subset hg)
    exact ⟨I.cities_inBounds c hcity, g, tlookup_of_mem hdlnd hg, hdist⟩
  refine ⟨⟨hcert.edges_gridAdj, fun x hx => hcert.deg hx, ?_, ?_⟩, ?_, hcert.tiles_le⟩
  · intro p hp
    have hp' : p ∈ pd.map Prod.fst := by rw [hfst]; exact mem_portsL.mpr hp
    obtain ⟨⟨p', dl⟩, he, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨-, hs, hn, -⟩ := fam_entry hpd he
    rw [hchoice he]
    exact nearest_of_near (finSpec_finOf I hp) hs hn
  · intro p hp c hc
    have hp' : p ∈ pd.map Prod.fst := by rw [hfst]; exact mem_portsL.mpr hp
    obtain ⟨⟨p', dl⟩, he, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    obtain ⟨hin, g, hg, -⟩ := hdem he c hc
    obtain ⟨d, δ, hd⟩ := hcert.dem_entry hj hin hg
    exact walkDist_lt_top_iff.mpr ⟨d, hcert.reach hj d c δ hin hd⟩
  · refine hcert.excess_le hnd hpf ?_
    intro j p dl hj c hc
    exact hdem (List.mem_of_getElem? hj) c hc

/-! ### Completeness: every feasible solution is covered by some choice combination -/

/-- For every feasible solution there are a choice combination and a labelling in range
that passes all checks and whose certified cost is at most the cost of the solution. -/
theorem complete_family {I : Instance} {τ : Solution} (hτ : τ.Feasible I) :
    ∃ pd ∈ famsOf I, ∃ L : Cell → Lab, GridOK 3 I.W I.H (kindOf I pd) L ∧ InRange I pd L ∧
      (excCount I pd L : ℕ∞) ≤ τ.excess I ∧ tileCount I pd L ≤ (τ.tiles I).card := by
  obtain ⟨hE, hdeg, hnear, hconn⟩ := hτ
  let f : Cell → Cell × List (Cell × ℕ) :=
    fun p => (p, (finOf I p).filter (fun e => decide (e.1 ∈ τ.choice p)))
  have hfst : ((portsL I).map f).map Prod.fst = portsL I := by
    rw [List.map_map]
    exact List.map_id _
  have hmem : (portsL I).map f ∈ famsOf I := by
    unfold famsOf
    rw [mem_familiesT, List.forall₂_map_left_iff, List.forall₂_same]
    intro p hp
    have hp' := mem_portsL.mp hp
    obtain ⟨h1, h2, -⟩ := near_of_nearest (finSpec_finOf I hp') (hnear p hp')
    exact mem_choicesT.mpr ⟨rfl, h1, h2⟩
  have hentry : ∀ {p : Cell} {dl : List (Cell × ℕ)}, (p, dl) ∈ (portsL I).map f →
      p ∈ I.ports ∧ dl = (finOf I p).filter (fun e => decide (e.1 ∈ τ.choice p)) := by
    intro p dl he
    obtain ⟨p', hp', heq⟩ := List.mem_map.mp he
    simp only [f, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨mem_portsL.mp hp', rfl⟩
  have hlook : ∀ {p : Cell} {dl : List (Cell × ℕ)}, (p, dl) ∈ (portsL I).map f →
      ∀ (c : Cell) (g : ℕ), (tlookup c dl).val = some g →
        c ∈ τ.choice p ∧ I.gridDist p c = (g : ℕ∞) := by
    intro p dl he c g hg
    obtain ⟨hp, rfl⟩ := hentry he
    have hin := tlookup_some hg
    rw [List.mem_filter, decide_eq_true_eq] at hin
    exact ⟨hin.2, (((finSpec_finOf I hp).mem c g).mp hin.1).2⟩
  refine ⟨(portsL I).map f, hmem, certLab I τ ((portsL I).map f), ?_, ?_, ?_, ?_⟩
  · refine certLab_ok hE hdeg _ ?_
    intro j p dl x g hj hg
    have he := List.mem_of_getElem? hj
    exact hconn p (hentry he).1 x (hlook he x g hg).1
  · intro x _
    refine ⟨certLab_ds_length _ x, fun en hen d δ hd => ?_⟩
    have hpin : ∀ e ∈ (portsL I).map f, I.InBounds e.1 := by
      intro e he
      exact I.ports_inBounds _ (hentry (p := e.1) (dl := e.2) he).1
    have := certLab_range hE _ hpin x en hen d δ hd
    omega
  · refine certLab_excess _ (by rw [hfst]; exact nodup_portsL I)
      (by rw [hfst]; exact toFinset_portsL I) ?_
    intro j p dl c g hj hg
    exact hlook (List.mem_of_getElem? hj) c g hg
  · exact certLab_tiles _

/-! ### The main theorem -/

namespace Answer

/-- On every instance, `solve` returns an optimal solution, or `none` exactly when no
feasible solution exists. -/
theorem correct (I : Instance) (_hP : I.ports.card ≤ 10) (_hC : I.cities.card ≤ 40) :
    match (Answer.solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I := by
  rw [solve_val]
  cases hbest : (bestT I (famsOf I)).val with
  | none =>
      rintro ⟨τ, hτ⟩
      obtain ⟨pd, hpd, L, hL, hrange, -, -⟩ := complete_family hτ
      exact dpRun_none (bestT_none hbest pd hpd) L hL hrange
  | some e =>
      obtain ⟨c, pd, w⟩ := e
      obtain ⟨hpd, hrun, hbestmin⟩ := bestT_some hbest
      obtain ⟨hok, hcost, -⟩ := dpRun_some hrun
      obtain ⟨hfeas, hexc, htiles⟩ := sound_family hpd hok
      refine ⟨hfeas, ?_⟩
      intro τ hτ
      obtain ⟨pd', hpd', L', hL', hrange', hexc', htiles'⟩ := complete_family hτ
      -- the DP run for `pd'` succeeds and is at most the certified cost of `L'`
      cases hrun' : (dpRun I pd' 3).val with
      | none => exact absurd (dpRun_none hrun' L' hL' hrange') id
      | some e' =>
          obtain ⟨c', w'⟩ := e'
          obtain ⟨-, -, hmin'⟩ := dpRun_some hrun'
          have h1 : c ≤ c' := hbestmin pd' hpd' c' w' hrun'
          have h2 : c' ≤ gridCost (I.W * I.H + 1) I pd' L' := hmin' L' hL' hrange'
          rw [gridCost_eq] at hcost h2
          have ht := tileCount_le I pd (labOf (decide (I.H ≤ I.W)) w)
          have ht' := tileCount_le I pd' L'
          set a := excCount I pd (labOf (decide (I.H ≤ I.W)) w) with ha
          set t := tileCount I pd (labOf (decide (I.H ≤ I.W)) w) with ht_def
          set a' := excCount I pd' L' with ha'
          set t' := tileCount I pd' L' with ht'_def
          have hle : a * (I.W * I.H + 1) + t ≤ a' * (I.W * I.H + 1) + t' := by omega
          have haa : a ≤ a' := by
            by_contra hlt
            have h3 : (a' + 1) * (I.W * I.H + 1) ≤ a * (I.W * I.H + 1) :=
              Nat.mul_le_mul_right _ (by omega)
            nlinarith
          have hchain : (solOf I pd (labOf (decide (I.H ≤ I.W)) w)).excess I ≤ τ.excess I :=
            le_trans hexc (le_trans (by exact_mod_cast haa) hexc')
          show (solOf I pd (labOf (decide (I.H ≤ I.W)) w)).cost I ≤ τ.cost I
          unfold Solution.cost
          rw [Prod.Lex.toLex_le_toLex]
          rcases lt_or_eq_of_le hchain with hlt | heq
          · exact Or.inl hlt
          · right
            refine ⟨heq, ?_⟩
            have haeq : a = a' := by
              have h4 : (a' : ℕ∞) ≤ (a : ℕ∞) := by
                calc (a' : ℕ∞) ≤ τ.excess I := hexc'
                  _ = (solOf I pd (labOf (decide (I.H ≤ I.W)) w)).excess I := heq.symm
                  _ ≤ (a : ℕ∞) := hexc
              have h5 : a' ≤ a := by exact_mod_cast h4
              omega
            have htt : t ≤ t' := by
              rw [haeq] at hle
              omega
            show ((solOf I pd (labOf (decide (I.H ≤ I.W)) w)).tiles I).card ≤ (τ.tiles I).card
            omega

end Answer

end TrainNetwork
