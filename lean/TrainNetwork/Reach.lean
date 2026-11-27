/-
Layered reachability: a recursive characterisation of `walkDist ≤ n`, and the fact
that inside a `W × H` grid every finite distance is at most `W * H`.
-/
import TrainNetwork.Cost

namespace TrainNetwork
namespace Instance

variable (I : Instance)

theorem getLast?_cons_concat (x : Cell) (m : List Cell) (b : Cell) :
    (x :: (m ++ [b])).getLast? = some b := by
  induction m generalizing x with
  | nil => simp
  | cons y m ih => simpa [List.getLast?_cons_cons] using ih y

/-- Normal form of a walk: either the trivial walk `[s]`, or `s :: (m ++ [t])` with all
of `m` free. -/
theorem isWalk_iff (R : Cell → Cell → Prop) (s t : Cell) (w : List Cell) :
    I.IsWalk R s t w ↔
      (w = [s] ∧ t = s) ∨
      (∃ m, w = s :: (m ++ [t]) ∧ w.IsChain R ∧ ∀ x ∈ m, I.IsFree x) := by
  have key : ∀ (x : Cell) (m : List Cell) (b : Cell),
      (x :: (m ++ [b])).getLast? = some b ∧ (x :: (m ++ [b])).dropLast.tail = m := by
    intro x m b
    constructor
    · induction m generalizing x with
      | nil => simp
      | cons y m ih => simpa [List.getLast?_cons_cons] using ih y
    · have : (x :: (m ++ [b])).dropLast = x :: m := by
        induction m generalizing x with
        | nil => simp
        | cons y m ih => simpa using ih y
      rw [this]; rfl
  constructor
  · rintro ⟨hh, hl, hc, hf⟩
    rcases w with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp at hh
    · simp at hh hl
      left; subst hh; subst hl; simp
    · right
      simp at hh
      subst hh
      rcases List.eq_nil_or_concat (y :: rest) with h | ⟨m, b, h⟩
      · simp at h
      · rw [List.concat_eq_append] at h
        rw [h] at hl hc hf ⊢
        rw [(key x m b).1] at hl
        rw [(key x m b).2] at hf
        have hb : b = t := by simpa using hl
        subst hb
        exact ⟨m, rfl, hc, hf⟩
  · rintro (⟨rfl, rfl⟩ | ⟨m, rfl, hc, hf⟩)
    · simp [IsWalk]
    · refine ⟨by simp, (key s m t).1, hc, ?_⟩
      rw [(key s m t).2]
      exact hf

/-- `I.reach R s n v`: there is a walk from `s` to `v` of length at most `n`. -/
def reach (R : Cell → Cell → Prop) (s : Cell) : ℕ → Cell → Prop
  | 0, v => v = s
  | n + 1, v => reach R s n v ∨ ∃ u, reach R s n u ∧ (u = s ∨ I.IsFree u) ∧ R u v

theorem reach_mono {R : Cell → Cell → Prop} {s : Cell} {n m : ℕ} (h : n ≤ m) {v : Cell} :
    I.reach R s n v → I.reach R s m v := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun hv => Or.inl (ih hv)

theorem reach_self (R : Cell → Cell → Prop) (s : Cell) (n : ℕ) : I.reach R s n s :=
  I.reach_mono (Nat.zero_le n) (rfl : I.reach R s 0 s)

theorem walk_of_reach {R : Cell → Cell → Prop} {s : Cell} :
    ∀ (n : ℕ) (v : Cell), I.reach R s n v → ∃ w, I.IsWalk R s v w ∧ w.length ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have hv' : v = s := hv
    subst hv'
    exact ⟨[v], (I.isWalk_iff R v v [v]).mpr (Or.inl ⟨rfl, rfl⟩), by simp⟩
  | succ n ih =>
    intro v hv
    rcases hv with hv | ⟨u, hu, hfree, hR⟩
    · obtain ⟨w, hw, hl⟩ := ih v hv
      exact ⟨w, hw, by omega⟩
    · have two : ∀ (hR' : R s v), ∃ w, I.IsWalk R s v w ∧ w.length ≤ n + 1 + 1 := by
        intro hR'
        refine ⟨[s, v], (I.isWalk_iff R s v [s, v]).mpr (Or.inr ⟨[], rfl, ?_, by simp⟩), by simp⟩
        exact List.isChain_pair.mpr hR'
      rcases hfree with rfl | hf
      · exact two hR
      · obtain ⟨w, hw, hl⟩ := ih u hu
        rcases (I.isWalk_iff R s u w).mp hw with ⟨_, rfl⟩ | ⟨m, rfl, hc, hm⟩
        · exact two hR
        · refine ⟨s :: ((m ++ [u]) ++ [v]),
            (I.isWalk_iff R s v _).mpr (Or.inr ⟨m ++ [u], rfl, ?_, ?_⟩), ?_⟩
          · have e : s :: ((m ++ [u]) ++ [v]) = (s :: (m ++ [u])) ++ [v] := rfl
            rw [e, List.isChain_append]
            refine ⟨hc, List.isChain_singleton _, ?_⟩
            intro x hx y hy
            rw [getLast?_cons_concat] at hx
            simp at hx hy
            subst hx; subst hy
            exact hR
          · intro x hx
            rcases List.mem_append.mp hx with h | h
            · exact hm x h
            · simp at h; subst h; exact hf
          · simp at hl ⊢
            omega

theorem reach_of_chain {R : Cell → Cell → Prop} {s : Cell} :
    ∀ (m : List Cell) (n : ℕ) (v : Cell), (s :: (m ++ [v])).IsChain R →
      (∀ x ∈ m, I.IsFree x) → m.length + 2 ≤ n + 1 → I.reach R s n v := by
  intro m
  induction m using List.reverseRecOn with
  | nil =>
    intro n v hc _ hl
    have hR : R s v := List.isChain_pair.mp hc
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hl; omega⟩
    exact Or.inr ⟨s, I.reach_self R s k, Or.inl rfl, hR⟩
  | append_singleton m u ih =>
    intro n v hc hf hl
    have e : s :: ((m ++ [u]) ++ [v]) = (s :: (m ++ [u])) ++ [v] := rfl
    rw [e, List.isChain_append] at hc
    obtain ⟨hc1, -, hc3⟩ := hc
    have hR : R u v := hc3 u (by rw [getLast?_cons_concat]; simp) v (by simp)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hl; omega⟩
    have hu : I.reach R s k u :=
      ih k u hc1 (fun x hx => hf x (List.mem_append.mpr (Or.inl hx))) (by simp at hl; omega)
    exact Or.inr ⟨u, hu, Or.inr (hf u (by simp)), hR⟩

theorem reach_iff_walk (R : Cell → Cell → Prop) (s : Cell) (n : ℕ) (v : Cell) :
    I.reach R s n v ↔ ∃ w, I.IsWalk R s v w ∧ w.length ≤ n + 1 := by
  constructor
  · exact I.walk_of_reach n v
  · rintro ⟨w, hw, hl⟩
    rcases (I.isWalk_iff R s v w).mp hw with ⟨_, hvs⟩ | ⟨m, rfl, hc, hm⟩
    · rw [hvs]; exact I.reach_self R s n
    · exact I.reach_of_chain m n v hc hm (by simp at hl; omega)

theorem walkDist_le_iff (R : Cell → Cell → Prop) (s t : Cell) (n : ℕ) :
    I.walkDist R s t ≤ (n : ℕ∞) ↔ I.reach R s n t := by
  rw [reach_iff_walk]
  constructor
  · intro h
    have h' : I.walkDist R s t < ((n + 1 : ℕ) : ℕ∞) :=
      lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self n)
    unfold walkDist at h'
    rw [sInf_lt_iff] at h'
    obtain ⟨a, ⟨w, hw, rfl⟩, ha⟩ := h'
    refine ⟨w, hw, ?_⟩
    have : w.length - 1 < n + 1 := by exact_mod_cast ha
    omega
  · rintro ⟨w, hw, hl⟩
    refine le_trans (sInf_le ⟨w, hw, rfl⟩) ?_
    have : w.length - 1 ≤ n := by omega
    exact_mod_cast this

theorem walkDist_lt_top_iff (R : Cell → Cell → Prop) (s t : Cell) :
    I.walkDist R s t < ⊤ ↔ ∃ n, I.reach R s n t := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt h)
    exact ⟨m, (I.walkDist_le_iff R s t m).mp (le_of_eq hm.symm)⟩
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt ((I.walkDist_le_iff R s t n).mpr hn) (ENat.natCast_lt_top n)

/-- A growing sequence of finite sets inside `U` that stays constant once it stops
growing is constant from step `U.card` on. -/
theorem stabilise {α : Type} [DecidableEq α] (L : ℕ → Finset α) (U : Finset α)
    (hmono : ∀ n, L n ⊆ L (n + 1))
    (hstab : ∀ n, L n = L (n + 1) → L (n + 1) = L (n + 2))
    (hU : ∀ n, L n ⊆ U) (h0 : (L 0).Nonempty) :
    ∀ m, L m ⊆ L U.card := by
  have key : ∀ n, L n = L (n + 1) ∨ n + 1 ≤ (L n).card := by
    intro n
    induction n with
    | zero => right; exact Finset.card_pos.mpr h0
    | succ n ih =>
      rcases ih with h | h
      · left; exact hstab n h
      · by_cases he : L n = L (n + 1)
        · left; exact hstab n he
        · right
          have hss : L n ⊂ L (n + 1) := Finset.ssubset_iff_subset_ne.mpr ⟨hmono n, he⟩
          have := Finset.card_lt_card hss
          omega
  have hs : L U.card = L (U.card + 1) := by
    rcases key U.card with h | h
    · exact h
    · have := Finset.card_le_card (hU U.card)
      omega
  have hstep : ∀ j, L (U.card + j) = L (U.card + j + 1) := by
    intro j
    induction j with
    | zero => exact hs
    | succ j ih => exact hstab (U.card + j) ih
  have hconst : ∀ j, L (U.card + j) = L U.card := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← ih]; exact (hstep j).symm
  intro m
  by_cases hm : m ≤ U.card
  · exact monotone_nat_of_le_succ hmono hm
  · obtain ⟨j, rfl⟩ : ∃ j, m = U.card + j := ⟨m - U.card, by omega⟩
    rw [hconst j]

theorem reach_inBounds {R : Cell → Cell → Prop} {s : Cell} (hs : I.InBounds s)
    (hR : ∀ u v, R u v → I.InBounds v) : ∀ n v, I.reach R s n v → I.InBounds v := by
  intro n
  induction n with
  | zero => intro v hv; have : v = s := hv; rw [this]; exact hs
  | succ n ih =>
    intro v hv
    rcases hv with hv | ⟨u, _, _, huv⟩
    · exact ih v hv
    · exact hR u v huv

open Classical in
/-- Inside the grid, whatever is reachable is reachable within `W * H` steps. -/
theorem reach_horizon {R : Cell → Cell → Prop} {s : Cell} (hs : I.InBounds s)
    (hR : ∀ u v, R u v → I.InBounds v) :
    ∀ n v, I.reach R s n v → I.reach R s (I.W * I.H) v := by
  let U : Finset Cell := Finset.range I.W ×ˢ Finset.range I.H
  let L : ℕ → Finset Cell := fun n => U.filter (fun v => I.reach R s n v)
  have hmem : ∀ n v, v ∈ L n ↔ I.reach R s n v := by
    intro n v
    simp only [L, U, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨I.reach_inBounds hs hR n v h, h⟩⟩
  have hcard : U.card = I.W * I.H := by simp [U]
  have hsub := stabilise L U
    (fun n v hv => (hmem (n + 1) v).mpr (Or.inl ((hmem n v).mp hv)))
    (fun n he => by
      ext v
      rw [hmem, hmem]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨u, hu, hok, huv⟩)
        · exact h
        · have : u ∈ L n := by rw [he]; exact (hmem (n + 1) u).mpr hu
          exact Or.inr ⟨u, (hmem n u).mp this, hok, huv⟩)
    (fun n => Finset.filter_subset _ _)
    ⟨s, (hmem 0 s).mpr rfl⟩
  intro n v hv
  have := hsub n ((hmem n v).mpr hv)
  rw [hcard] at this
  exact (hmem _ v).mp this

end Instance
end TrainNetwork
