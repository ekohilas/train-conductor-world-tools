/-
Walks of the frozen definition, re-expressed as an inductive "reach in exactly `d` steps"
relation. Everything downstream (certificates, soundness, completeness) uses `Reach`
instead of lists of cells.
-/
import TrainNetwork.Problem

namespace TrainNetwork

/-- `Reach I R s d x`: there is a walk of length `d` from `s` to `x` along `R` whose
intermediate cells are all free (the last-but-one cell of each step is either the start
`s` itself, at distance `0`, or a free cell). -/
inductive Reach (I : Instance) (R : Cell → Cell → Prop) (s : Cell) : ℕ → Cell → Prop
  | zero : Reach I R s 0 s
  | step {d : ℕ} {y x : Cell} :
      Reach I R s d y → (d = 0 ∨ I.IsFree y) → R y x → Reach I R s (d + 1) x

variable {I : Instance} {R R' : Cell → Cell → Prop} {s x : Cell} {d : ℕ}

/-- Extending a walk `w` (ending at `y`) by one more cell `x'`. -/
theorem isWalk_concat {w : List Cell} {y x' : Cell} (hy : w.getLast? = some y) :
    I.IsWalk R s x (w ++ [x']) ↔
      x' = x ∧ I.IsWalk R s y w ∧ R y x' ∧ (w.length = 1 ∨ I.IsFree y) := by
  have hne : w ≠ [] := by rintro rfl; simp at hy
  have hw : w.dropLast ++ [y] = w := List.dropLast_append_getLast? y (by simp [hy])
  have htail : (∀ c ∈ w.tail, I.IsFree c) ↔
      (∀ c ∈ w.dropLast.tail, I.IsFree c) ∧ (w.length = 1 ∨ I.IsFree y) := by
    rcases hd : w.dropLast with _ | ⟨b, l⟩
    · have hwy : w = [y] := by rw [← hw, hd]; rfl
      simp [hwy]
    · have ht : w.tail = l ++ [y] := by rw [← hw, hd]; rfl
      have hl : w.length = l.length + 2 := by rw [← hw, hd]; simp
      rw [ht]
      simp [hl, or_imp, forall_and]
  unfold Instance.IsWalk
  rw [List.head?_append_of_ne_nil _ hne, List.getLast?_concat, List.isChain_append,
    List.dropLast_concat, htail, hy]
  simp
  tauto

/-- A walk gives a `Reach` of its length. -/
theorem reach_of_isWalk (w : List Cell) :
    ∀ x, I.IsWalk R s x w → Reach I R s (w.length - 1) x := by
  induction w using List.reverseRecOn with
  | nil => intro x h; simp [Instance.IsWalk] at h
  | append_singleton w a ih =>
    intro x h
    rcases List.eq_nil_or_concat w with rfl | ⟨w', y, rfl⟩
    · obtain ⟨h1, h2, -⟩ := h
      simp at h1 h2
      subst h1; subst h2
      exact Reach.zero
    · have hy : (w'.concat y).getLast? = some y := by simp
      obtain ⟨rfl, hw, hR, hfree⟩ := (isWalk_concat hy).1 h
      have hlen : (w'.concat y ++ [a]).length - 1 = ((w'.concat y).length - 1) + 1 := by simp
      rw [hlen]
      refine Reach.step (ih y hw) (hfree.imp (fun h1 => ?_) id) hR
      omega

/-- `Reach` is exactly "there is a walk of that length" in the sense of `Instance.IsWalk`. -/
theorem reach_iff_walk :
    Reach I R s d x ↔ ∃ w, I.IsWalk R s x w ∧ w.length - 1 = d := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨[s], ⟨rfl, rfl, List.isChain_singleton _, by simp⟩, rfl⟩
    | @step d y x _ hfree hR ih =>
      obtain ⟨w, hw, hlen⟩ := ih
      have hy : w.getLast? = some y := hw.2.1
      have hne : w ≠ [] := by rintro rfl; simp at hy
      have hpos := List.length_pos_of_ne_nil hne
      refine ⟨w ++ [x], (isWalk_concat hy).2 ⟨rfl, hw, hR, ?_⟩, ?_⟩
      · rcases hfree with h0 | hf
        · left; omega
        · exact Or.inr hf
      · simp; omega
  · rintro ⟨w, hw, rfl⟩
    exact reach_of_isWalk w x hw

theorem reach_zero_iff : Reach I R s 0 x ↔ x = s := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Reach.zero

theorem Reach.mono (h : ∀ a b, R a b → R' a b) (hr : Reach I R s d x) : Reach I R' s d x := by
  induction hr with
  | zero => exact Reach.zero
  | step _ hf hR ih => exact Reach.step ih hf (h _ _ hR)

/-- A `Reach` bounds the distance from above. -/
theorem walkDist_le_of_reach (h : Reach I R s d x) : I.walkDist R s x ≤ (d : ℕ∞) := by
  obtain ⟨w, hw, rfl⟩ := reach_iff_walk.1 h
  exact sInf_le ⟨w, hw, rfl⟩

/-- A lower bound on all `Reach` lengths is a lower bound on the distance. -/
theorem le_walkDist {n : ℕ∞} (h : ∀ d, Reach I R s d x → n ≤ (d : ℕ∞)) :
    n ≤ I.walkDist R s x := by
  refine le_sInf ?_
  rintro _ ⟨w, hw, rfl⟩
  exact h _ (reach_iff_walk.2 ⟨w, hw, rfl⟩)

theorem walkDist_le_coe_iff :
    I.walkDist R s x ≤ (d : ℕ∞) ↔ ∃ d', d' ≤ d ∧ Reach I R s d' x := by
  constructor
  · intro h
    by_contra hne
    have h1 : ((d + 1 : ℕ) : ℕ∞) ≤ I.walkDist R s x := by
      refine le_walkDist fun d' hd' => ?_
      have hlt : d + 1 ≤ d' := by
        by_contra hlt
        exact hne ⟨d', by omega, hd'⟩
      exact_mod_cast hlt
    have h2 : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := h1.trans h
    have h3 : d + 1 ≤ d := by exact_mod_cast h2
    omega
  · rintro ⟨d', hd', hr⟩
    exact (walkDist_le_of_reach hr).trans (by exact_mod_cast hd')

theorem walkDist_lt_top_iff : I.walkDist R s x < ⊤ ↔ ∃ d, Reach I R s d x := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h.ne
    obtain ⟨d', -, hr⟩ := walkDist_le_coe_iff.1 hn.ge
    exact ⟨d', hr⟩
  · rintro ⟨d, hr⟩
    exact (walkDist_le_of_reach hr).trans_lt (ENat.natCast_lt_top d)

theorem walkDist_eq_coe_iff :
    I.walkDist R s x = (d : ℕ∞) ↔ Reach I R s d x ∧ ∀ d', d' < d → ¬ Reach I R s d' x := by
  constructor
  · intro h
    have hmin : ∀ d', d' < d → ¬ Reach I R s d' x := by
      intro d' hd' hr
      have h1 : (d : ℕ∞) ≤ (d' : ℕ∞) := h ▸ walkDist_le_of_reach hr
      have h2 : d ≤ d' := by exact_mod_cast h1
      omega
    obtain ⟨d', hd', hr⟩ := walkDist_le_coe_iff.1 h.le
    rcases hd'.lt_or_eq with hlt | rfl
    · exact absurd hr (hmin d' hlt)
    · exact ⟨hr, hmin⟩
  · rintro ⟨hr, hmin⟩
    refine le_antisymm (walkDist_le_of_reach hr) (le_walkDist fun d' hd' => ?_)
    have hle : d ≤ d' := by
      by_contra hlt
      exact hmin d' (by omega) hd'
    exact_mod_cast hle

theorem walkDist_self : I.walkDist R s s = 0 := by
  have h := (walkDist_eq_coe_iff (I := I) (R := R) (s := s) (x := s) (d := 0)).2
    ⟨Reach.zero, fun d' hd' => by omega⟩
  simpa using h

/-- A larger relation gives smaller distances. -/
theorem walkDist_mono (h : ∀ a b, R a b → R' a b) : I.walkDist R' s x ≤ I.walkDist R s x :=
  le_walkDist fun _ hr => walkDist_le_of_reach (hr.mono h)

/-- The last-but-one cell of a shortest walk. -/
theorem exists_pred (h : I.walkDist R s x = ((d + 1 : ℕ) : ℕ∞)) :
    ∃ y, R y x ∧ I.walkDist R s y = (d : ℕ∞) ∧ (y = s ∨ I.IsFree y) := by
  obtain ⟨hr, hmin⟩ := walkDist_eq_coe_iff.1 h
  cases hr with
  | @step _ y _ hy hfree hR =>
    refine ⟨y, hR, walkDist_eq_coe_iff.2 ⟨hy, ?_⟩, ?_⟩
    · intro d' hd' hr'
      have hfy : I.IsFree y := by
        rcases hfree with h0 | hf
        · omega
        · exact hf
      exact hmin (d' + 1) (by omega) (Reach.step hr' (Or.inr hfy) hR)
    · rcases hfree with h0 | hf
      · subst h0
        exact Or.inl (reach_zero_iff.1 hy)
      · exact Or.inr hf

/-- The cells of a shortest walk of length `d`: `d + 1` distinct in-bounds cells. -/
theorem exists_cells (hR : ∀ a b, R a b → I.InBounds b) (hs : I.InBounds s) :
    ∀ (d : ℕ) (x : Cell), I.walkDist R s x = (d : ℕ∞) →
      ∃ S : Finset Cell, S.card = d + 1 ∧ (∀ z ∈ S, I.InBounds z) ∧
        ∀ z ∈ S, I.walkDist R s z ≤ (d : ℕ∞) := by
  intro d
  induction d with
  | zero =>
    intro x _
    refine ⟨{s}, by simp, ?_, ?_⟩
    · intro z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      exact hs
    · intro z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      rw [walkDist_self]
      simp
  | succ d ih =>
    intro x h
    obtain ⟨y, hyx, hy, -⟩ := exists_pred h
    obtain ⟨S, hcard, hb, hdist⟩ := ih y hy
    have hx : x ∉ S := by
      intro hxS
      have h1 : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := h ▸ hdist x hxS
      have h2 : d + 1 ≤ d := by exact_mod_cast h1
      omega
    refine ⟨insert x S, by rw [Finset.card_insert_of_notMem hx, hcard], ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hR _ _ hyx
      · exact hb z hz
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact h.le
      · exact (hdist z hz).trans (by exact_mod_cast Nat.le_succ d)

/-- Shortest walks are short: a finite distance is smaller than the number of grid cells,
provided every step of `R` ends inside the grid and the start is inside the grid. -/
theorem walkDist_lt_cells (hR : ∀ a b, R a b → I.InBounds b) (hs : I.InBounds s)
    (h : I.walkDist R s x = (d : ℕ∞)) : d < I.W * I.H := by
  obtain ⟨S, hcard, hb, -⟩ := exists_cells hR hs d x h
  have hsub : S ⊆ Finset.range I.W ×ˢ Finset.range I.H := by
    intro z hz
    have hz' := hb z hz
    simp only [Finset.mem_product, Finset.mem_range]
    exact hz'
  have hle := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range, Finset.card_range, hcard] at hle
  omega

end TrainNetwork
