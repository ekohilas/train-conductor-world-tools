/-
Walk lemmas: a computable characterisation of `Instance.walkDist`.

`walkDist R s t` is defined in `Problem.lean` as an `sInf` over all walks. Here we show
that it can be computed by a layered search:

* `WalkN R s t n`      : there is a walk from `s` to `t` with exactly `n` steps;
* `walkN_zero/succ`    : `WalkN` satisfies the obvious layer recurrence;
* `IsWalk.exists_nodup`: every walk can be shortened to one without repeated cells;
* `distL`              : a list-based layered search, and `walkDist_eq_optENat`, which
                         says that it computes `walkDist` for the symmetric closure of
                         an edge list.

Nothing in this file is timed; the `TimeM` versions live in `Timed.lean`.
-/
import TrainNetwork.Cost

namespace TrainNetwork

/-- `Option ℕ` read as an extended natural: `none` is `⊤`. -/
def optENat : Option ℕ → ℕ∞
  | some n => (n : ℕ∞)
  | none => ⊤

@[simp] theorem optENat_some (n : ℕ) : optENat (some n) = (n : ℕ∞) := rfl
@[simp] theorem optENat_none : optENat none = ⊤ := rfl

theorem optENat_lt_top {o : Option ℕ} : optENat o < ⊤ ↔ o.isSome = true := by
  cases o <;> simp

namespace Instance

variable (I : Instance)

/-- There is a walk from `s` to `t` with exactly `n` steps. -/
def WalkN (R : Cell → Cell → Prop) (s t : Cell) (n : ℕ) : Prop :=
  ∃ w, I.IsWalk R s t w ∧ w.length = n + 1

variable {I}

theorem IsWalk.ne_nil {R : Cell → Cell → Prop} {s t : Cell} {w : List Cell}
    (h : I.IsWalk R s t w) : w ≠ [] := by
  rintro rfl
  simp [IsWalk] at h

theorem walkN_zero {R : Cell → Cell → Prop} {s t : Cell} : I.WalkN R s t 0 ↔ t = s := by
  constructor
  · rintro ⟨w, ⟨hh, hl, -, -⟩, hlen⟩
    match w, hlen with
    | [a], _ =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      rw [← hh, ← hl]
  · rintro rfl
    exact ⟨[t], ⟨rfl, rfl, List.isChain_singleton _, by simp⟩, rfl⟩

theorem walkN_succ {R : Cell → Cell → Prop} {s t : Cell} {n : ℕ} :
    I.WalkN R s t (n + 1) ↔
      ∃ x, I.WalkN R s x n ∧ (n = 0 ∨ I.IsFree x) ∧ R x t := by
  constructor
  · rintro ⟨w, ⟨hh, hl, hc, hf⟩, hlen⟩
    rcases List.eq_nil_or_concat w with rfl | ⟨w', b, rfl⟩
    · simp at hlen
    rw [List.concat_eq_append] at hh hl hc hf hlen
    have hw' : w' ≠ [] := by
      rintro rfl
      simp at hlen
    have hlen' : w'.length = n + 1 := by simpa using hlen
    have hb : b = t := by simpa using hl
    subst hb
    rw [List.dropLast_concat] at hf
    obtain ⟨hc1, -, hc2⟩ := List.isChain_append.1 hc
    refine ⟨w'.getLast hw', ⟨w', ⟨?_, ?_, hc1, ?_⟩, hlen'⟩, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil _ hw'] at hh
      exact hh
    · exact List.getLast?_eq_some_getLast hw'
    · intro x hx
      apply hf
      rw [List.tail_dropLast] at hx
      exact List.mem_of_mem_dropLast hx
    · by_cases hn : n = 0
      · exact Or.inl hn
      · right
        apply hf
        match w', hw', hlen' with
        | [a], _, h => exact absurd (by simpa using h) hn
        | a :: c :: l, _, _ =>
          show (a :: c :: l).getLast _ ∈ c :: l
          rw [List.getLast_cons (by simp)]
          exact List.getLast_mem _
    · exact hc2 _ (List.getLast?_eq_some_getLast hw') b (by simp)
  · rintro ⟨x, ⟨w', ⟨hh, hl, hc, hf⟩, hlen⟩, hx, hR⟩
    have hw' : w' ≠ [] := by
      rintro rfl
      simp at hlen
    refine ⟨w' ++ [t], ⟨?_, ?_, ?_, ?_⟩, by simp [hlen]⟩
    · rw [List.head?_append_of_ne_nil _ hw']
      exact hh
    · simp
    · refine hc.append (List.isChain_singleton _) ?_
      intro a ha b hb
      have ha' : a = x := by
        rw [hl] at ha
        exact (Option.some.inj ha).symm
      have hb' : b = t := by simpa using hb.symm
      rw [ha', hb']
      exact hR
    · intro y hy
      rw [List.dropLast_concat] at hy
      obtain ⟨d, rfl⟩ : ∃ d, w' = d ++ [x] :=
        ⟨w'.dropLast, (List.dropLast_append_getLast? x hl).symm⟩
      rw [List.dropLast_concat] at hf
      rcases d with _ | ⟨a, d⟩
      · simp at hy
      · have hy' : y ∈ d ∨ y = x := by simpa using hy
        rcases hy' with hy' | rfl
        · exact hf y (by simpa using hy')
        · rcases hx with hn | hfree
          · simp [hn] at hlen
          · exact hfree

theorem walkDist_eq_coe {R : Cell → Cell → Prop} {s t : Cell} {n : ℕ}
    (h : I.WalkN R s t n) (hmin : ∀ m, I.WalkN R s t m → n ≤ m) :
    I.walkDist R s t = (n : ℕ∞) := by
  unfold walkDist
  apply le_antisymm
  · apply sInf_le
    obtain ⟨w, hw, hl⟩ := h
    exact ⟨w, hw, by simp [hl]⟩
  · apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    have h1 : 1 ≤ w.length := List.length_pos_iff.2 hw.ne_nil
    have := hmin (w.length - 1) ⟨w, hw, by omega⟩
    exact_mod_cast this

theorem walkDist_eq_top {R : Cell → Cell → Prop} {s t : Cell}
    (h : ∀ n, ¬ I.WalkN R s t n) : I.walkDist R s t = ⊤ := by
  unfold walkDist
  rw [sInf_eq_top]
  rintro _ ⟨w, hw, rfl⟩
  have h1 : 1 ≤ w.length := List.length_pos_iff.2 hw.ne_nil
  exact absurd ⟨w, hw, by omega⟩ (h (w.length - 1))

/-- A chain can be shortened to a chain without repeated elements, keeping its first
and last element and using only elements of the original chain. -/
theorem exists_nodup_chain {R : Cell → Cell → Prop} :
    ∀ (l : List Cell) (a : Cell), List.IsChain R (a :: l) →
      ∃ l', List.IsChain R (a :: l') ∧ (a :: l').Nodup ∧
        (a :: l').getLast? = (a :: l).getLast? ∧ l' ⊆ l
  | [], a, _ => ⟨[], List.isChain_singleton _, by simp, rfl, by simp⟩
  | b :: l, a, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨l', hc, hn, hl, hs⟩ := exists_nodup_chain l b h.2
    by_cases ha : a ∈ b :: l'
    · obtain ⟨pre, post, hpp⟩ := List.append_of_mem ha
      refine ⟨post, ?_, ?_, ?_, ?_⟩
      · exact (hpp ▸ hc).right_of_append
      · exact (List.nodup_append.1 (hpp ▸ hn)).2.1
      · have h1 : (b :: l').getLast? = (a :: post).getLast? := by
          rw [hpp, List.getLast?_append_of_ne_nil _ (by simp)]
        rw [← h1, hl]
        simp [List.getLast?_cons_cons]
      · intro x hx
        have : x ∈ b :: l' := by
          rw [hpp]
          simp [hx]
        rcases List.mem_cons.1 this with rfl | hx'
        · simp
        · exact List.mem_cons_of_mem _ (hs hx')
    · refine ⟨b :: l', ?_, ?_, ?_, ?_⟩
      · exact List.isChain_cons_cons.2 ⟨h.1, hc⟩
      · exact List.nodup_cons.2 ⟨ha, hn⟩
      · simpa [List.getLast?_cons_cons] using hl
      · exact List.cons_subset_cons _ hs

theorem IsWalk.exists_nodup {R : Cell → Cell → Prop} {s t : Cell} {w : List Cell}
    (h : I.IsWalk R s t w) : ∃ w', I.IsWalk R s t w' ∧ w'.Nodup ∧ w' ⊆ w := by
  obtain ⟨hh, hl, hc, hf⟩ := h
  rcases w with _ | ⟨a, l⟩
  · simp at hh
  have ha : a = s := by simpa using hh
  subst ha
  obtain ⟨l', hc', hn', hl', hs'⟩ := exists_nodup_chain l a hc
  refine ⟨a :: l', ⟨rfl, hl'.trans hl, hc', ?_⟩, hn', List.cons_subset_cons _ hs'⟩
  intro x hx
  -- `x` is an interior cell of the new walk, hence of the old one.
  rcases List.eq_nil_or_concat l' with rfl | ⟨d', z, rfl⟩
  · simp at hx
  rw [List.concat_eq_append] at hx hn' hl' hs'
  have hx1 : x ∈ d' := by
    have : (a :: (d' ++ [z])).dropLast = a :: d' := by
      rw [← List.cons_append, List.dropLast_concat]
    rw [this] at hx
    simpa using hx
  have hzt : t = z := by
    have h1 : (a :: (d' ++ [z])).getLast? = some z := by
      rw [← List.cons_append, List.getLast?_concat]
    rw [h1] at hl'
    rw [hl] at hl'
    exact (Option.some.inj hl').symm
  have hxz : x ≠ z := by
    intro hxz
    subst hxz
    have := (List.nodup_cons.1 hn').2
    rw [List.nodup_append] at this
    exact this.2.2 x hx1 x (by simp) rfl
  have hxl : x ∈ l := hs' (by simp [hx1])
  rcases List.eq_nil_or_concat l with rfl | ⟨d, y, rfl⟩
  · simp at hxl
  rw [List.concat_eq_append] at hxl hl hf
  have hyt : y = t := by
    have h1 : (a :: (d ++ [y])).getLast? = some y := by
      rw [← List.cons_append, List.getLast?_concat]
    rw [h1] at hl
    exact Option.some.inj hl
  apply hf
  have : (a :: (d ++ [y])).dropLast = a :: d := by
    rw [← List.cons_append, List.dropLast_concat]
  rw [this]
  have hxd : x ∈ d ∨ x = y := by simpa using hxl
  rcases hxd with hxd | rfl
  · simpa using hxd
  · exact absurd (hyt.trans hzt) hxz

/-- In a chain with at least two elements, every element is related to some other
element, in one direction or the other. -/
theorem chain_mem_rel {R : Cell → Cell → Prop} :
    ∀ (w : List Cell), List.IsChain R w → 2 ≤ w.length →
      ∀ x ∈ w, ∃ y, R x y ∨ R y x
  | [], _, h2, _, _ => by simp at h2
  | [_], _, h2, _, _ => by simp at h2
  | [a, b], hc, _, x, hx => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, Or.inl hc.1⟩
    · have : x = b := by simpa using hx
      subst this
      exact ⟨a, Or.inr hc.1⟩
  | a :: b :: c :: l, hc, _, x, hx => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, Or.inl hc.1⟩
    · exact chain_mem_rel (b :: c :: l) hc.2 (by simp) x hx

end Instance

/-! ### List-based layered search -/

/-- The symmetric closure of an edge list, as a relation. -/
def ListAdj (E : List (Cell × Cell)) (a b : Cell) : Prop := (a, b) ∈ E ∨ (b, a) ∈ E

/-- One layer step: all cells adjacent (via `E`, in either direction) to a cell `x` of
`A` that may be left, i.e. `first` holds (then `x` is the source) or `x` is free. -/
def stepL (free : Cell → Bool) (E : List (Cell × Cell)) (first : Bool) (A : List Cell) :
    List Cell :=
  (E.filter (fun e => decide (e.1 ∈ A) && (first || free e.1))).map Prod.snd ++
  (E.filter (fun e => decide (e.2 ∈ A) && (first || free e.2))).map Prod.fst

theorem mem_stepL {free : Cell → Bool} {E : List (Cell × Cell)} {first : Bool}
    {A : List Cell} {t : Cell} :
    t ∈ stepL free E first A ↔
      ∃ x ∈ A, (first = true ∨ free x = true) ∧ ListAdj E x t := by
  simp only [stepL, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, ListAdj]
  constructor
  · rintro (⟨⟨a, b⟩, ⟨hE, hA, hf⟩, rfl⟩ | ⟨⟨a, b⟩, ⟨hE, hA, hf⟩, rfl⟩)
    · exact ⟨a, hA, hf, Or.inl hE⟩
    · exact ⟨b, hA, hf, Or.inr hE⟩
  · rintro ⟨x, hA, hf, hE | hE⟩
    · exact Or.inl ⟨(x, t), ⟨hE, hA, hf⟩, rfl⟩
    · exact Or.inr ⟨(t, x), ⟨hE, hA, hf⟩, rfl⟩

/-- The `n`-th layer: all cells reachable from `s` by a walk with exactly `n` steps. -/
def layerL (free : Cell → Bool) (E : List (Cell × Cell)) (s : Cell) : ℕ → List Cell
  | 0 => [s]
  | n + 1 => stepL free E (n == 0) (layerL free E s n)

theorem mem_layerL {I : Instance} {free : Cell → Bool} (hfree : ∀ x, free x = true ↔ I.IsFree x)
    {E : List (Cell × Cell)} {s : Cell} :
    ∀ {n : ℕ} {t : Cell}, t ∈ layerL free E s n ↔ I.WalkN (ListAdj E) s t n
  | 0, t => by simp [layerL, Instance.walkN_zero]
  | n + 1, t => by
    rw [layerL, mem_stepL, Instance.walkN_succ]
    constructor
    · rintro ⟨x, hx, hf, hE⟩
      refine ⟨x, (mem_layerL hfree).1 hx, ?_, hE⟩
      rcases hf with hf | hf
      · exact Or.inl (by simpa using hf)
      · exact Or.inr ((hfree x).1 hf)
    · rintro ⟨x, hx, hf, hE⟩
      refine ⟨x, (mem_layerL hfree).2 hx, ?_, hE⟩
      rcases hf with hf | hf
      · exact Or.inl (by simpa using hf)
      · exact Or.inr ((hfree x).2 hf)

/-- Layered search: starting from layer `i` (the list `A`), look at up to `fuel` further
layers and return the index of the first one containing `t`. -/
def distL (free : Cell → Bool) (E : List (Cell × Cell)) (t : Cell) :
    ℕ → ℕ → List Cell → Option ℕ
  | 0, i, A => if t ∈ A then some i else none
  | f + 1, i, A =>
    if t ∈ A then some i else distL free E t f (i + 1) (stepL free E (i == 0) A)

theorem distL_layer_some {free : Cell → Bool} {E : List (Cell × Cell)} {s t : Cell} :
    ∀ (f i n : ℕ), distL free E t f i (layerL free E s i) = some n →
      t ∈ layerL free E s n ∧ ∀ m, i ≤ m → t ∈ layerL free E s m → n ≤ m
  | 0, i, n, h => by
    rw [distL] at h
    split_ifs at h with ht
    obtain rfl : i = n := by simpa using h
    exact ⟨ht, fun m hm _ => hm⟩
  | f + 1, i, n, h => by
    rw [distL] at h
    split_ifs at h with ht
    · obtain rfl : i = n := by simpa using h
      exact ⟨ht, fun m hm _ => hm⟩
    · obtain ⟨h1, h2⟩ := distL_layer_some f (i + 1) n h
      refine ⟨h1, fun m hm hmt => ?_⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact absurd hmt ht
      · exact h2 m hlt hmt

theorem distL_layer_none {free : Cell → Bool} {E : List (Cell × Cell)} {s t : Cell} :
    ∀ (f i : ℕ), distL free E t f i (layerL free E s i) = none →
      ∀ m, i ≤ m → m ≤ i + f → t ∉ layerL free E s m
  | 0, i, h, m, hm1, hm2 => by
    rw [distL] at h
    split_ifs at h with ht
    obtain rfl : m = i := by omega
    exact ht
  | f + 1, i, h, m, hm1, hm2 => by
    rw [distL] at h
    split_ifs at h with ht
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · exact ht
    · exact distL_layer_none f (i + 1) h m hlt (by omega)

/-- Shortest walk length along the symmetric closure of `E`, as an `Option ℕ`. The fuel
`2 * E.length` suffices because a shortest walk repeats no cell and every cell of a walk
with at least one step is an endpoint of an edge of `E`. -/
def netDistO (free : Cell → Bool) (E : List (Cell × Cell)) (s t : Cell) : Option ℕ :=
  distL free E t (2 * E.length) 0 [s]

theorem walkN_bound {I : Instance} {E : List (Cell × Cell)} {s t : Cell} {n : ℕ}
    (h : I.WalkN (ListAdj E) s t n) : ∃ m, m ≤ 2 * E.length ∧ I.WalkN (ListAdj E) s t m := by
  obtain ⟨w, hw, -⟩ := h
  obtain ⟨w', hw', hnd, -⟩ := hw.exists_nodup
  have h1 : 1 ≤ w'.length := List.length_pos_iff.2 hw'.ne_nil
  refine ⟨w'.length - 1, ?_, w', hw', by omega⟩
  by_cases h2 : 2 ≤ w'.length
  · have hsub : w' ⊆ E.map Prod.fst ++ E.map Prod.snd := by
      intro x hx
      obtain ⟨y, hy | hy⟩ := Instance.chain_mem_rel w' hw'.2.2.1 h2 x hx
      · rcases hy with hy | hy
        · exact List.mem_append_left _ (List.mem_map.2 ⟨_, hy, rfl⟩)
        · exact List.mem_append_right _ (List.mem_map.2 ⟨_, hy, rfl⟩)
      · rcases hy with hy | hy
        · exact List.mem_append_right _ (List.mem_map.2 ⟨_, hy, rfl⟩)
        · exact List.mem_append_left _ (List.mem_map.2 ⟨_, hy, rfl⟩)
    have := (hnd.subperm hsub).length_le
    simp only [List.length_append, List.length_map] at this
    omega
  · omega

/-- The layered search computes `walkDist`. -/
theorem walkDist_eq_optENat {I : Instance} {free : Cell → Bool}
    (hfree : ∀ x, free x = true ↔ I.IsFree x) (E : List (Cell × Cell)) (s t : Cell) :
    I.walkDist (ListAdj E) s t = optENat (netDistO free E s t) := by
  unfold netDistO
  have h0 : ([s] : List Cell) = layerL free E s 0 := rfl
  rw [h0]
  cases hd : distL free E t (2 * E.length) 0 (layerL free E s 0) with
  | some n =>
    obtain ⟨h1, h2⟩ := distL_layer_some _ _ _ hd
    exact Instance.walkDist_eq_coe ((mem_layerL hfree).1 h1)
      (fun m hm => h2 m (Nat.zero_le _) ((mem_layerL hfree).2 hm))
  | none =>
    have h1 := distL_layer_none _ _ hd
    apply Instance.walkDist_eq_top
    intro n hn
    obtain ⟨m, hm, hmw⟩ := walkN_bound hn
    exact h1 m (Nat.zero_le _) (by omega) ((mem_layerL hfree).2 hmw)

end TrainNetwork
