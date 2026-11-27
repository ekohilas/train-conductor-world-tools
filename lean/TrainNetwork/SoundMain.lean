/-
Soundness of the encoding, assembled: `Sat a (enc I X K) → Decide I X K`.
-/
import TrainNetwork.Sound
import TrainNetwork.Count

namespace TrainNetwork.Answer

open TrainNetwork

variable (I : Instance) (a : ℕ → Bool)

theorem sat_enc (X K : ℕ) :
    Sat a (enc I X K) ↔
      Sat a (edgeClauses I) ∧ (∀ p ∈ portL I, Sat a (portClauses I p)) ∧
      Sat a (atMost (vCount (Nat.pair 2 0)) X (excessItems I)) ∧
      Sat a (atMost (vCount (Nat.pair 3 0)) K (tileItems I)) := by
  unfold enc
  simp only [sat_append, sat_flatMap, and_assoc]

theorem sat_portClauses (p : Cell) :
    Sat a (portClauses I p) ↔
      Sat a (initClauses I p) ∧ Sat a (reachClauses I p) ∧ Sat a (finClauses I p) ∧
      Sat a (nearClauses I p) ∧ Sat a (cardClauses I p) := by
  unfold portClauses
  simp only [sat_append, and_assoc]

theorem card_filter_cities (q : Cell → Bool) :
    (I.cities.filter fun c => q c = true).card = (cityL I).countP q := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((nodup_cityL I).filter _)]
  congr 1
  ext c
  simp [mem_cityL]

theorem countP_add_countP_not (q : Cell → Bool) (l : List Cell) :
    l.countP q + l.countP (fun c => !q c) = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons, List.length_cons]
    cases q x <;> simp <;> omega

theorem le_of_forall_nat_le {x y : ℕ∞} (h : ∀ n : ℕ, y ≤ n → x ≤ n) : x ≤ y := by
  by_cases hy : y = ⊤
  · rw [hy]; exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hy
    rw [← hn]
    exact h n (le_of_eq hn.symm)

theorem card_choice_eq {p : Cell} (hcard : Sat a (cardClauses I p)) :
    (I.cities.filter fun c => a (vSel p c) = true).card = I.k := by
  unfold cardClauses at hcard
  rw [sat_append] at hcard
  have h1 := atMost_sound a _ _ _ hcard.1
  have h0 := atMost_sound a _ _ _ hcard.2
  rw [cnt_selItems] at h1 h0
  have e1 : (fun c => a (vSel p c) == true) = fun c => a (vSel p c) := by
    funext c; simp
  rw [e1] at h1
  have e0 : (fun c => a (vSel p c) == false) = fun c => !a (vSel p c) := by
    funext c; simp
  rw [e0] at h0
  have hsum := countP_add_countP_not (fun c => a (vSel p c)) (cityL I)
  have hk : I.k ≤ (cityL I).length := by rw [cityL_length]; exact I.k_le_cities
  rw [card_filter_cities]
  omega

/-- Soundness: a satisfying assignment gives a feasible solution within the bounds. -/
theorem enc_sound (X K : ℕ) (h : Sat a (enc I X K)) : Decide I X K := by
  rw [sat_enc] at h
  obtain ⟨hE, hP, hX, hK⟩ := h
  have hNet : (decSol I a).NetAdj = EAdj I a := by
    funext x y; exact propext (netAdj_decSol I a hE x y)
  have hport : ∀ p ∈ I.ports, _ := fun p hp =>
    (sat_portClauses I a p).mp (hP p ((mem_portL I p).mpr hp))
  have hgrid : ∀ p ∈ I.ports, ∀ t, t ≤ I.W * I.H → ∀ v ∈ cells I,
      (a (vGrid p t v) = true ↔ I.reach I.GridAdj p t v) := fun p hp =>
    grid_reach I a hp (hport p hp).1 (hport p hp).2.1
  have hnet : ∀ p ∈ I.ports, ∀ t, t ≤ I.W * I.H → ∀ v ∈ cells I,
      a (vNet p t v) = true → I.reach (EAdj I a) p t v := fun p hp =>
    net_reach I a hE hp (hport p hp).1 (hport p hp).2.1
  have hcity : ∀ c ∈ I.cities, c ∈ cells I := fun c hc =>
    (mem_cells I c).mpr (I.cities_inBounds c hc)
  have hsel : ∀ p ∈ I.ports, ∀ c ∈ I.cities, a (vSel p c) = true →
      I.reach I.GridAdj p (I.W * I.H) c ∧ I.reach (EAdj I a) p (I.W * I.H) c := by
    intro p hp c hc hs
    have hfin := (sat_finClauses I a p).mp (hport p hp).2.2.1 c ((mem_cityL I c).mpr hc) hs
    exact ⟨(hgrid p hp _ le_rfl c (hcity c hc)).mp hfin.1,
      hnet p hp _ le_rfl c (hcity c hc) hfin.2⟩
  have hmem : ∀ p c, c ∈ (decSol I a).choice p ↔ c ∈ I.cities ∧ a (vSel p c) = true :=
    fun p c => Finset.mem_filter
  refine ⟨decSol I a, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- edges join grid-adjacent open cells
    rintro ⟨x, y⟩ he
    have hxy : (decSol I a).NetAdj x y := Or.inl he
    rw [hNet] at hxy
    exact ⟨hxy.1, hxy.2.1, hxy.2.2.1⟩
  · exact fun x hx => degree_le I a hE x hx
  · -- nearest choice
    intro p hp
    refine ⟨Finset.filter_subset _ _, card_choice_eq I a (hport p hp).2.2.2.2, ?_, ?_⟩
    · intro c hc
      rw [hmem] at hc
      exact (I.walkDist_lt_top_iff _ p c).mpr ⟨_, (hsel p hp c hc.1 hc.2).1⟩
    · intro c hc c' hc' hnot
      rw [hmem] at hc
      have hs' : a (vSel p c') = false := by
        by_contra hne
        exact hnot ((hmem p c').mpr ⟨hc', by simpa using hne⟩)
      apply le_of_forall_nat_le
      intro n hn
      have hr' : I.reach I.GridAdj p n c' := (I.walkDist_le_iff _ p c' n).mp hn
      have hnear := (sat_nearClauses I a p).mp (hport p hp).2.2.2.1 c
        ((mem_cityL I c).mpr hc.1) c' ((mem_cityL I c').mpr hc')
      apply (I.walkDist_le_iff _ p c n).mpr
      by_cases hnT : n ≤ I.W * I.H
      · exact (hgrid p hp n hnT c (hcity c hc.1)).mp
          (hnear n hnT hc.2 hs' ((hgrid p hp n hnT c' (hcity c' hc')).mpr hr'))
      · have hT' : I.reach I.GridAdj p (I.W * I.H) c' :=
          I.reach_horizon (I.ports_inBounds p hp) (fun u v huv => huv.2.2.1) n c' hr'
        have := (hgrid p hp _ le_rfl c (hcity c hc.1)).mp
          (hnear _ le_rfl hc.2 hs' ((hgrid p hp _ le_rfl c' (hcity c' hc')).mpr hT'))
        exact I.reach_mono (by omega) this
  · -- connectivity
    intro p hp c hc
    rw [hmem] at hc
    show I.walkDist (decSol I a).NetAdj p c < ⊤
    rw [hNet]
    exact (I.walkDist_lt_top_iff _ p c).mpr ⟨_, (hsel p hp c hc.1 hc.2).2⟩
  · -- excess
    have hcnt := atMost_sound a _ X _ hX
    rw [cnt_excessItems] at hcnt
    show (∑ p ∈ I.ports, ∑ c ∈ (decSol I a).choice p,
      ((decSol I a).netDist I p c - I.gridDist p c)) ≤ (X : ℕ∞)
    rw [sum_ports]
    refine le_trans (list_sum_le_cast _ _ _ ?_) (by exact_mod_cast hcnt)
    intro p hp
    rw [mem_portL] at hp
    show (∑ c ∈ I.cities.filter (fun c => a (vSel p c) = true),
      ((decSol I a).netDist I p c - I.gridDist p c)) ≤ _
    rw [Finset.sum_filter, sum_cities]
    apply list_sum_le_cast
    intro c hc
    rw [mem_cityL] at hc
    split_ifs with hs
    · obtain ⟨hg, hn⟩ := hsel p hp c hc hs
      have hnd : (decSol I a).netDist I p c = I.walkDist (EAdj I a) p c := by
        show I.walkDist (decSol I a).NetAdj p c = _
        rw [hNet]
      rw [hnd]
      have hnle : I.walkDist (EAdj I a) p c ≤ ((I.W * I.H : ℕ) : ℕ∞) :=
        (I.walkDist_le_iff _ p c _).mpr hn
      have hgle : I.gridDist p c ≤ ((I.W * I.H : ℕ) : ℕ∞) :=
        (I.walkDist_le_iff _ p c _).mpr hg
      obtain ⟨n, hn_eq⟩ := ENat.ne_top_iff_exists.mp
        (ne_of_lt (lt_of_le_of_lt hnle (ENat.natCast_lt_top _)))
      obtain ⟨d, hd_eq⟩ := ENat.ne_top_iff_exists.mp
        (ne_of_lt (lt_of_le_of_lt hgle (ENat.natCast_lt_top _)))
      rw [← hn_eq, ← hd_eq, ← ENat.natCast_sub]
      have hnT : n ≤ I.W * I.H := by
        rw [← hn_eq] at hnle; exact_mod_cast hnle
      refine Nat.cast_le.mpr (le_countP_range _ d n _ hnT ?_)
      intro t hdt htn
      have hgt : a (vGrid p t c) = true := by
        apply (hgrid p hp t (by omega) c (hcity c hc)).mpr
        apply (I.walkDist_le_iff _ p c t).mp
        show I.gridDist p c ≤ _
        rw [← hd_eq]; exact_mod_cast hdt
      have hnt : a (vNet p t c) = false := by
        by_contra hne
        have hr := hnet p hp t (by omega) c (hcity c hc) (by simpa using hne)
        have := (I.walkDist_le_iff _ p c t).mpr hr
        rw [← hn_eq] at this
        have : n ≤ t := by exact_mod_cast this
        omega
      simp [exPred, hs, hgt, hnt]
    · exact zero_le
  · -- tiles
    have hcnt := atMost_sound a _ K _ hK
    rw [cnt_tileItems] at hcnt
    have hsub : (decSol I a).tiles I ⊆ ((cells I).filter fun x => a (vTile x)).toFinset := by
      intro x hx
      unfold Solution.tiles at hx
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hx
      obtain ⟨hx1, hfree⟩ := hx
      have hex : ∃ y, (decSol I a).NetAdj x y := by
        rcases hx1 with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
        · exact ⟨e.2, Or.inl he⟩
        · exact ⟨e.1, Or.inr he⟩
      obtain ⟨y, hy⟩ := hex
      rw [hNet] at hy
      have ht := (edge_facts I a hE hy.1 hy.2.1.1 hy.2.2.1.1 hy.2.2.2).2 hfree
      simp only [List.mem_toFinset, List.mem_filter, mem_cells]
      exact ⟨hfree.1, ht⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans (List.toFinset_card_le _) ?_)
    rw [← List.countP_eq_length_filter]
    exact hcnt

end TrainNetwork.Answer
