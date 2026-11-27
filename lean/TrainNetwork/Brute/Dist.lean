/-
An executable shortest-walk length `Brute.walkDistC`, proven equal to the
noncomputable `sInf`-based specification `Instance.walkDist` of `TrainNetwork.Problem`.

The algorithm is a layered search: `layer I R s n` is the list of cells that are the
endpoint of a walk from `s` with exactly `n` edges, and `walkDistC` returns the first
`n ≤ |cells|` whose layer contains `t` (or `⊤`). With `N = W * H` in-bounds cells, one
layer costs `O(N²)` evaluations of `R`, so a call costs `O(N³)` of them in the worst
case and `O(d · N²)` when `t` is found at distance `d`.

Correctness needs only `hR : ∀ a b, R a b → I.InBounds b` (every edge ends in bounds),
which makes the layers finite. It rests on two facts about walks:

* `Instance.isWalk_concat_iff`: a walk ending in `v` is a walk ending in some `u`
  followed by an edge `u → v`, where `u` must be free unless it is the start;
* `Instance.IsWalk.splice` / `Instance.exists_nodup_isWalk`: loops can be cut out, so a
  shortest walk has no repeated cell and hence at most `|cells| + 1` entries.
-/
import TrainNetwork.Brute.Basic

namespace TrainNetwork

/-! ### Generic list helpers -/

private theorem sublist_dropLast {α : Type*} {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    l₁.dropLast.Sublist l₂.dropLast := by
  have h' := h.reverse.tail.reverse
  rwa [← List.dropLast_reverse, ← List.dropLast_reverse, List.reverse_reverse,
    List.reverse_reverse] at h'

private theorem exists_dup_of_not_nodup {α : Type*} :
    ∀ {l : List α}, ¬ l.Nodup → ∃ a x b c, l = a ++ x :: (b ++ x :: c)
  | [], h => absurd List.nodup_nil h
  | y :: l, h => by
    rw [List.nodup_cons, not_and_or, not_not] at h
    rcases h with h | h
    · obtain ⟨b, c, rfl⟩ := List.append_of_mem h
      exact ⟨[], y, b, c, rfl⟩
    · obtain ⟨a, x, b, c, rfl⟩ := exists_dup_of_not_nodup h
      exact ⟨y :: a, x, b, c, rfl⟩

private theorem exists_rel_of_isChain_cons {α : Type*} {R : α → α → Prop} :
    ∀ {a : α} {l : List α}, List.IsChain R (a :: l) → ∀ x ∈ l, ∃ y, R y x
  | _, [], _, x, hx => by simp at hx
  | a, b :: l, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨a, h.1⟩
    · exact exists_rel_of_isChain_cons h.2 x hx

/-! ### General facts about walks and `walkDist` (no decidability needed) -/

namespace Instance

variable {I : Instance} {R R' : Cell → Cell → Prop} {s t u v : Cell} {w : List Cell}

theorem IsWalk.ne_nil (h : I.IsWalk R s t w) : w ≠ [] := by
  rintro rfl
  simp [IsWalk] at h

theorem IsWalk.length_pos (h : I.IsWalk R s t w) : 0 < w.length :=
  List.length_pos_of_ne_nil h.ne_nil

theorem isWalk_singleton_iff {a : Cell} : I.IsWalk R s t [a] ↔ a = s ∧ a = t := by
  simp [IsWalk]

/-- The one-cell walk. Note that `s` need not be free, open or even in bounds. -/
theorem isWalk_refl (s : Cell) : I.IsWalk R s s [s] :=
  isWalk_singleton_iff.2 ⟨rfl, rfl⟩

private theorem isWalk_concat_concat_iff {w0 : List Cell} :
    I.IsWalk R s v (w0 ++ [u] ++ [v]) ↔
      I.IsWalk R s u (w0 ++ [u]) ∧ R u v ∧ ((w0 ++ [u]).length = 1 ∨ I.IsFree u) := by
  have hhead : (w0 ++ [u] ++ [v]).head? = (w0 ++ [u]).head? := by cases w0 <;> rfl
  have hchain : (w0 ++ [u] ++ [v]).IsChain R ↔ (w0 ++ [u]).IsChain R ∧ R u v := by
    rw [List.isChain_append]
    simp
  have hfree : (∀ x ∈ (w0 ++ [u] ++ [v]).dropLast.tail, I.IsFree x) ↔
      (∀ x ∈ (w0 ++ [u]).dropLast.tail, I.IsFree x) ∧
        ((w0 ++ [u]).length = 1 ∨ I.IsFree u) := by
    rw [List.dropLast_concat, List.dropLast_concat]
    cases w0 with
    | nil => simp
    | cons a w0 =>
      simp only [List.cons_append, List.tail_cons, List.forall_mem_append,
        List.forall_mem_singleton, List.length_cons, List.length_append, List.length_nil]
      refine and_congr_right fun _ => ⟨Or.inr, fun h => h.resolve_left (by omega)⟩
  unfold IsWalk
  rw [hhead, hchain, hfree, List.getLast?_concat, List.getLast?_concat]
  tauto

/-- Extending a walk by one edge. The old endpoint `u` becomes an intermediate cell, so
it must be free, unless it is also the start (`w.length = 1`). -/
theorem isWalk_concat_iff (hw : w ≠ []) :
    I.IsWalk R s v (w ++ [v]) ↔
      ∃ u, I.IsWalk R s u w ∧ R u v ∧ (w.length = 1 ∨ I.IsFree u) := by
  obtain ⟨w0, u, rfl⟩ : ∃ w0 u, w = w0 ++ [u] :=
    ⟨w.dropLast, w.getLast hw, (List.dropLast_concat_getLast hw).symm⟩
  rw [isWalk_concat_concat_iff]
  constructor
  · exact fun h => ⟨u, h⟩
  · rintro ⟨u', h1, h2, h3⟩
    obtain rfl : u = u' := by simpa using h1.2.1
    exact ⟨h1, h2, h3⟩

/-- Cutting a loop out of a walk. -/
theorem IsWalk.splice {a b c : List Cell} {x : Cell}
    (h : I.IsWalk R s t (a ++ x :: (b ++ x :: c))) : I.IsWalk R s t (a ++ x :: c) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases a <;> simpa using h1
  · simpa [List.getLast?_append, List.getLast?_cons] using h2
  · rw [List.isChain_append] at h3 ⊢
    refine ⟨h3.1, ?_, h3.2.2⟩
    have h5 := h3.2.1
    rw [← List.cons_append, List.isChain_append] at h5
    exact h5.2.1
  · intro y hy
    apply h4
    have hsub : (a ++ x :: c).Sublist (a ++ x :: (b ++ x :: c)) := by simp
    exact (sublist_dropLast hsub).tail.subset hy

/-- Every walk can be shortened to one without repeated cells. -/
theorem exists_nodup_isWalk (h : I.IsWalk R s t w) :
    ∃ w', I.IsWalk R s t w' ∧ w'.Nodup ∧ w'.length ≤ w.length := by
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hn
    by_cases hnd : w.Nodup
    · exact ⟨w, h, hnd, le_rfl⟩
    · obtain ⟨a, x, b, c, rfl⟩ := exists_dup_of_not_nodup hnd
      have hlt : (a ++ x :: c).length < (a ++ x :: (b ++ x :: c)).length := by
        simp only [List.length_append, List.length_cons]
        omega
      obtain ⟨w', hw', hnd', hl⟩ := ih _ hlt h.splice rfl
      exact ⟨w', hw', hnd', hl.trans hlt.le⟩

theorem walkDist_le_of_isWalk (h : I.IsWalk R s t w) :
    I.walkDist R s t ≤ ((w.length - 1 : ℕ) : ℕ∞) :=
  sInf_le ⟨w, h, rfl⟩

theorem walkDist_lt_top_iff : I.walkDist R s t < ⊤ ↔ ∃ w, I.IsWalk R s t w := by
  unfold walkDist
  rw [sInf_lt_iff]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, -⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨_, ⟨w, hw, rfl⟩, ENat.natCast_lt_top _⟩

theorem walkDist_eq_top_iff : I.walkDist R s t = ⊤ ↔ ¬ ∃ w, I.IsWalk R s t w := by
  rw [← walkDist_lt_top_iff, not_lt, top_le_iff]

/-- The infimum defining `walkDist` is attained as soon as some walk exists. -/
theorem exists_isWalk_walkDist_eq (h : ∃ w, I.IsWalk R s t w) :
    ∃ w, I.IsWalk R s t w ∧ I.walkDist R s t = ((w.length - 1 : ℕ) : ℕ∞) := by
  obtain ⟨w, hw⟩ := h
  exact csInf_mem
    (s := {n : ℕ∞ | ∃ w, I.IsWalk R s t w ∧ n = ((w.length - 1 : ℕ) : ℕ∞)}) ⟨_, w, hw, rfl⟩

theorem walkDist_congr (h : ∀ a b, R a b ↔ R' a b) :
    I.walkDist R s t = I.walkDist R' s t := by
  have : R = R' := funext fun a => funext fun b => propext (h a b)
  rw [this]

theorem walkDist_self (s : Cell) : I.walkDist R s s = 0 := by
  have h := walkDist_le_of_isWalk (I := I) (R := R) (isWalk_refl s)
  simpa using h

end Instance

namespace Brute

open Instance

/-! ### Bounding the length of a shortest walk -/

/-- A walk without repeated cells has at most `|cells| + 1` entries: all entries but the
first are the target of an edge, hence in bounds. -/
theorem length_le_of_nodup_isWalk {I : Instance} {R : Cell → Cell → Prop}
    (hR : ∀ a b, R a b → I.InBounds b) {s t : Cell} {w : List Cell}
    (h : I.IsWalk R s t w) (hnd : w.Nodup) : w.length ≤ (cells I).length + 1 := by
  cases w with
  | nil => simp
  | cons a l =>
    have hsub : l ⊆ cells I := fun x hx => by
      obtain ⟨y, hy⟩ := exists_rel_of_isChain_cons h.2.2.1 x hx
      exact (mem_cells I x).2 (hR y x hy)
    have := (List.nodup_cons.1 hnd).2.length_le_of_subset hsub
    simpa using this

variable (I : Instance) (R : Cell → Cell → Prop) [DecidableRel R]

/-! ### Layers -/

/-- One extension step: the in-bounds cells `v` with an edge `u → v` from some `u ∈ L`
that may serve as an intermediate cell. Cells of layer `0` (the start) are exempt from
the freeness requirement. -/
def step (n : ℕ) (L : List Cell) : List Cell :=
  (cells I).filter fun v => L.any fun u => decide ((n = 0 ∨ I.IsFree u) ∧ R u v)

/-- `layer I R s n` lists the endpoints of the walks from `s` with exactly `n` edges
(see `mem_layer_iff`). -/
def layer (s : Cell) : ℕ → List Cell
  | 0 => [s]
  | n + 1 => step I R n (layer s n)

theorem mem_step {n : ℕ} {L : List Cell} {v : Cell} :
    v ∈ step I R n L ↔ I.InBounds v ∧ ∃ u ∈ L, (n = 0 ∨ I.IsFree u) ∧ R u v := by
  simp [step, mem_cells]

theorem mem_layer_iff (hR : ∀ a b, R a b → I.InBounds b) (s : Cell) (n : ℕ) (v : Cell) :
    v ∈ layer I R s n ↔ ∃ w, I.IsWalk R s v w ∧ w.length = n + 1 := by
  induction n generalizing v with
  | zero =>
    simp only [layer, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨[v], isWalk_refl v, rfl⟩
    · rintro ⟨w, hw, hl⟩
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
      obtain ⟨rfl, rfl⟩ := isWalk_singleton_iff.1 hw
      rfl
  | succ n ih =>
    rw [layer, mem_step]
    constructor
    · rintro ⟨-, u, hu, hfree, huv⟩
      obtain ⟨w, hw, hl⟩ := (ih u).1 hu
      refine ⟨w ++ [v], (isWalk_concat_iff hw.ne_nil).2 ⟨u, hw, huv, ?_⟩, by simp [hl]⟩
      rcases hfree with rfl | h
      · exact Or.inl hl
      · exact Or.inr h
    · rintro ⟨w, hw, hl⟩
      obtain ⟨w', v', rfl⟩ : ∃ w' v', w = w' ++ [v'] :=
        ⟨w.dropLast, w.getLast hw.ne_nil, (List.dropLast_concat_getLast hw.ne_nil).symm⟩
      obtain rfl : v' = v := by simpa using hw.2.1
      have hl' : w'.length = n + 1 := by simpa using hl
      have hne : w' ≠ [] := by
        rintro rfl
        simp at hl'
      obtain ⟨u, hu, huv, hfree⟩ := (isWalk_concat_iff hne).1 hw
      refine ⟨hR u v' huv, u, (ih u).2 ⟨w', hu, hl'⟩, ?_, huv⟩
      rcases hfree with h | h
      · left; omega
      · exact Or.inr h

/-! ### The search -/

/-- `searchO I R t fuel n L`, with `L = layer I R s n`: the least `m` with
`n ≤ m ≤ n + fuel` and `t ∈ layer I R s m`, if any. -/
def searchO (t : Cell) : ℕ → ℕ → List Cell → Option ℕ
  | 0, n, L => if t ∈ L then some n else none
  | fuel + 1, n, L => if t ∈ L then some n else searchO t fuel (n + 1) (step I R n L)

/-- Shortest-walk length as an `Option ℕ` (`none` = unreachable). -/
def walkDistO (s t : Cell) : Option ℕ :=
  searchO I R t (cells I).length 0 [s]

/-- Executable shortest-walk length. `R` is any decidable relation. -/
def walkDistC (s t : Cell) : ℕ∞ :=
  match walkDistO I R s t with
  | some n => (n : ℕ∞)
  | none => ⊤

theorem searchO_eq_some {s t : Cell} {fuel n m : ℕ}
    (h : searchO I R t fuel n (layer I R s n) = some m) :
    t ∈ layer I R s m ∧ ∀ j, n ≤ j → j < m → t ∉ layer I R s j := by
  induction fuel generalizing n with
  | zero =>
    simp only [searchO] at h
    split_ifs at h with ht
    obtain rfl : n = m := by simpa using h
    exact ⟨ht, fun j h1 h2 => absurd h1 (by omega)⟩
  | succ fuel ih =>
    simp only [searchO] at h
    split_ifs at h with ht
    · obtain rfl : n = m := by simpa using h
      exact ⟨ht, fun j h1 h2 => absurd h1 (by omega)⟩
    · obtain ⟨h1, h2⟩ := ih (n := n + 1) h
      refine ⟨h1, fun j hj hjm => ?_⟩
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact ht
      · exact h2 j hlt hjm

theorem searchO_eq_none {s t : Cell} {fuel n : ℕ}
    (h : searchO I R t fuel n (layer I R s n) = none) :
    ∀ j, n ≤ j → j ≤ n + fuel → t ∉ layer I R s j := by
  induction fuel generalizing n with
  | zero =>
    simp only [searchO] at h
    split_ifs at h with ht
    intro j h1 h2
    obtain rfl : j = n := by omega
    exact ht
  | succ fuel ih =>
    simp only [searchO] at h
    split_ifs at h with ht
    intro j h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact ht
    · exact ih (n := n + 1) h j hlt (by omega)

/-! ### Correctness -/

/-- The executable `walkDistC` computes the specification `Instance.walkDist`, for every
decidable relation whose edges end in bounds. -/
theorem walkDistC_eq (hR : ∀ a b, R a b → I.InBounds b) (s t : Cell) :
    walkDistC I R s t = I.walkDist R s t := by
  rw [walkDistC]
  cases h : walkDistO I R s t with
  | some m =>
    obtain ⟨hm, hmin⟩ := searchO_eq_some I R (s := s) (n := 0) h
    obtain ⟨w, hw, hl⟩ := (mem_layer_iff I R hR s m t).1 hm
    refine le_antisymm (le_sInf ?_) ?_
    · rintro _ ⟨w', hw', rfl⟩
      rw [Nat.cast_le]
      refine Nat.le_of_not_lt fun hlt => ?_
      refine hmin (w'.length - 1) (Nat.zero_le _) hlt
        ((mem_layer_iff I R hR s _ t).2 ⟨w', hw', ?_⟩)
      have := hw'.length_pos
      omega
    · have := walkDist_le_of_isWalk hw
      simpa [hl] using this
  | none =>
    symm
    rw [walkDist_eq_top_iff]
    rintro ⟨w, hw⟩
    obtain ⟨w', hw', hnd, -⟩ := exists_nodup_isWalk hw
    have hlen := length_le_of_nodup_isWalk hR hw' hnd
    have hpos := hw'.length_pos
    exact searchO_eq_none I R (s := s) (n := 0) h (w'.length - 1) (Nat.zero_le _) (by omega)
      ((mem_layer_iff I R hR s _ t).2 ⟨w', hw', by omega⟩)

/-- Specialisation to the grid: `walkDistC` on `GridAdj` is `gridDist`. -/
theorem walkDistC_gridAdj (s t : Cell) : walkDistC I I.GridAdj s t = I.gridDist s t :=
  walkDistC_eq I I.GridAdj (fun _ _ h => h.2.2.1) s t

/-! ### Smoke test -/

/-- A `3 × 1` corridor with a port at the left end and a city at the right end. -/
private def exampleInstance : Instance where
  W := 3
  H := 1
  blocked := ∅
  ports := {(0, 0)}
  cities := {(2, 0)}
  k := 1
  k_pos := by decide
  ports_cities := by decide
  ports_unblocked := by simp
  cities_unblocked := by simp
  ports_inBounds := by simp
  cities_inBounds := by simp

-- Prints `some 2`: Mathlib's derived `Repr ℕ∞` shows `(n : ℕ∞)` as `some n` and `⊤` as
-- `none`. The `example` below checks the same value in the kernel.
#eval walkDistC exampleInstance exampleInstance.GridAdj (0, 0) (2, 0)

example : walkDistC exampleInstance exampleInstance.GridAdj (0, 0) (2, 0) = 2 := by decide

#print axioms walkDistC_eq

end Brute

end TrainNetwork
