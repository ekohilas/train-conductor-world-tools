/-
Running time of the exhaustive solver `solveT`.

Main result: `solveT_time_le`, an **exponential** bound

    (solveT I).time ≤ 2 ^ (600 * I.size)      (at most 10 ports, at most 40 cities).

This is NOT the quasi-polynomial bound asked for in `Goal.lean`; it is what is true of
exhaustive search. The proof is bookkeeping: every timed function is bounded by a power
of `m = 32 * I.size`, and there are at most `2 ^ (4 * I.size) * 2 ^ 400` candidates.
-/
import TrainNetwork.Timed

namespace TrainNetwork

open TimeM

/-! ### Arithmetic helpers -/

theorem le_pow_of_le {m a i j : ℕ} (hm : 16 ≤ m) (h : a ≤ m ^ i) (hij : i ≤ j) :
    a ≤ m ^ j :=
  h.trans (Nat.pow_le_pow_right (by omega) hij)

theorem lin_le_pow {m a j : ℕ} (hm : 16 ≤ m) (h : a ≤ 16 * m ^ j) : a ≤ m ^ (j + 1) :=
  calc a ≤ 16 * m ^ j := h
    _ ≤ m * m ^ j := Nat.mul_le_mul_right _ hm
    _ = m ^ (j + 1) := by ring

theorem le_pow_one {m a : ℕ} (h : a ≤ m) : a ≤ m ^ 1 := by simpa using h

theorem lin_le_sq {m a : ℕ} (hm : 16 ≤ m) (h : a ≤ 16 * m) : a ≤ m ^ 2 :=
  lin_le_pow hm (by simpa using h)

theorem one_le_pow' {m : ℕ} (hm : 16 ≤ m) (i : ℕ) : 1 ≤ m ^ i :=
  Nat.one_le_pow _ _ (by omega)

/-- A loop over at most `m` elements with per-element cost at most `m ^ i`. -/
theorem comb_le {m x c i : ℕ} (hm : 16 ≤ m) (hx : x ≤ m) (hc : c ≤ m ^ i) :
    x * (c + 1) ≤ m ^ (i + 2) := by
  have h1 : 1 ≤ m ^ i := one_le_pow' hm i
  have h2 : c + 1 ≤ m ^ (i + 1) := lin_le_pow hm (by omega)
  calc x * (c + 1) ≤ m * m ^ (i + 1) := Nat.mul_le_mul hx h2
    _ = m ^ (i + 2) := by ring

/-! ### Running times of the list combinators -/

section Combinators

variable {α β : Type}

theorem filterT_time_le (p : α → TimeM Bool) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (p a).time ≤ c) → (filterT p l).time ≤ l.length * (c + 1)
  | [], _ => by simp [filterT]
  | a :: l, h => by
    have ih := filterT_time_le p c l (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ha := h a List.mem_cons_self
    have e : (l.length + 1) * (c + 1) = l.length * (c + 1) + (c + 1) := by ring
    simp only [filterT, bind_time, tick_time, pure_time, List.length_cons, e]
    omega

theorem filterT_length_le (p : α → TimeM Bool) (l : List α) :
    (filterT p l).val.length ≤ l.length := by
  rw [filterT_val]
  exact List.length_filter_le _ _

theorem mapT_time_le (f : α → TimeM β) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).time ≤ c) → (mapT f l).time ≤ l.length * (c + 1)
  | [], _ => by simp [mapT]
  | a :: l, h => by
    have ih := mapT_time_le f c l (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ha := h a List.mem_cons_self
    have e : (l.length + 1) * (c + 1) = l.length * (c + 1) + (c + 1) := by ring
    simp only [mapT, bind_time, tick_time, pure_time, List.length_cons, e]
    omega

theorem mapT_length (f : α → TimeM β) (l : List α) : (mapT f l).val.length = l.length := by
  rw [mapT_val, List.length_map]

theorem allT_time_le (p : α → TimeM Bool) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (p a).time ≤ c) → (allT p l).time ≤ l.length * (c + 1)
  | [], _ => by simp [allT]
  | a :: l, h => by
    have ih := allT_time_le p c l (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ha := h a List.mem_cons_self
    have e : (l.length + 1) * (c + 1) = l.length * (c + 1) + (c + 1) := by ring
    simp only [allT, bind_time, tick_time, pure_time, List.length_cons, e]
    omega

theorem foldlT_time_le (f : β → α → TimeM β) (c : ℕ) :
    ∀ (l : List α) (b : β), (∀ b, ∀ a ∈ l, (f b a).time ≤ c) →
      (foldlT f b l).time ≤ l.length * (c + 1)
  | [], _, _ => by simp [foldlT]
  | a :: l, b, h => by
    have ih := foldlT_time_le f c l (f b a).val
      (fun b a ha => h b a (List.mem_cons_of_mem _ ha))
    have ha := h b a List.mem_cons_self
    have e : (l.length + 1) * (c + 1) = l.length * (c + 1) + (c + 1) := by ring
    simp only [foldlT, bind_time, tick_time, List.length_cons, e]
    omega

@[simp] theorem appendT_time : ∀ l₁ l₂ : List α, (appendT l₁ l₂).time = l₁.length
  | [], l₂ => rfl
  | a :: l₁, l₂ => by
    simp only [appendT, bind_time, tick_time, pure_time, appendT_time l₁ l₂,
      List.length_cons]
    omega

theorem flatMapT_time_le (f : α → TimeM (List β)) (c d : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).time ≤ c) → (∀ a ∈ l, (f a).val.length ≤ d) →
      (flatMapT f l).time ≤ l.length * (c + d + 1)
  | [], _, _ => by simp [flatMapT]
  | a :: l, h, h' => by
    have ih := flatMapT_time_le f c d l (fun a ha => h a (List.mem_cons_of_mem _ ha))
      (fun a ha => h' a (List.mem_cons_of_mem _ ha))
    have ha := h a List.mem_cons_self
    have ha' := h' a List.mem_cons_self
    have e : (l.length + 1) * (c + d + 1) = l.length * (c + d + 1) + (c + d + 1) := by ring
    simp only [flatMapT, bind_time, tick_time, appendT_time, List.length_cons, e]
    omega

@[simp] theorem lengthT_time : ∀ l : List α, (lengthT l).time = l.length
  | [] => rfl
  | a :: l => by
    simp only [lengthT, bind_time, tick_time, pure_time, lengthT_time l, List.length_cons]
    omega

@[simp] theorem sumT_time : ∀ l : List ℕ, (sumT l).time = l.length
  | [] => rfl
  | a :: l => by
    simp only [sumT, bind_time, tick_time, pure_time, sumT_time l, List.length_cons]
    omega

@[simp] theorem memT_time [DecidableEq α] (c : ℕ) (a : α) :
    ∀ l : List α, (memT c a l).time = c * l.length
  | [] => rfl
  | b :: l => by
    simp only [memT, bind_time, tickN_time, pure_time, memT_time c a l, List.length_cons]
    ring

theorem dedupT_time_le [DecidableEq α] (c : ℕ) :
    ∀ l : List α, (dedupT c l).time ≤ l.length * (c * l.length + 1)
  | [] => by simp [dedupT]
  | a :: l => by
    have ih := dedupT_time_le c l
    have e : (l.length + 1) * (c * (l.length + 1) + 1) =
        l.length * (c * l.length + 1) + (c * l.length + 1) + (c * l.length + c) := by ring
    simp only [dedupT, bind_time, tick_time, pure_time, memT_time, List.length_cons, e]
    omega

theorem dedupT_length_le [DecidableEq α] (c : ℕ) (l : List α) :
    (dedupT c l).val.length ≤ l.length := by
  rw [dedupT_val]
  exact (List.dedup_sublist l).length_le

theorem rangeT_time_le : ∀ n : ℕ, (rangeT n).time ≤ n * (n + 1)
  | 0 => by simp [rangeT]
  | n + 1 => by
    have ih := rangeT_time_le n
    have e : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) + (n + 1) := by ring
    simp only [rangeT, bind_time, tick_time, appendT_time, rangeT_val, List.length_range, e]
    omega

/-- Quadratic loops over a list of length at most `m`. -/
theorem dedupT_time_le_pow [DecidableEq α] {m : ℕ} (hm : 16 ≤ m) (l : List α)
    (hl : l.length ≤ m) : (dedupT 2 l).time ≤ m ^ 4 := by
  refine (dedupT_time_le 2 l).trans ?_
  have h1 : 2 * l.length ≤ m ^ 2 := lin_le_sq hm (by omega)
  exact comb_le hm hl h1


theorem filterT_time_pow {m i : ℕ} (hm : 16 ≤ m) (p : α → TimeM Bool) (l : List α)
    (hl : l.length ≤ m) (h : ∀ a ∈ l, (p a).time ≤ m ^ i) :
    (filterT p l).time ≤ m ^ (i + 2) :=
  (filterT_time_le p _ l h).trans (comb_le hm hl le_rfl)

theorem mapT_time_pow {m i : ℕ} (hm : 16 ≤ m) (f : α → TimeM β) (l : List α)
    (hl : l.length ≤ m) (h : ∀ a ∈ l, (f a).time ≤ m ^ i) :
    (mapT f l).time ≤ m ^ (i + 2) :=
  (mapT_time_le f _ l h).trans (comb_le hm hl le_rfl)

theorem allT_time_pow {m i : ℕ} (hm : 16 ≤ m) (p : α → TimeM Bool) (l : List α)
    (hl : l.length ≤ m) (h : ∀ a ∈ l, (p a).time ≤ m ^ i) :
    (allT p l).time ≤ m ^ (i + 2) :=
  (allT_time_le p _ l h).trans (comb_le hm hl le_rfl)

end Combinators

/-! ### The grid -/

namespace Instance

variable (I : Instance)

theorem exists_city : ∃ c, c ∈ I.cities := by
  have h : 0 < I.cities.card := lt_of_lt_of_le I.k_pos I.k_le_cities
  exact Finset.card_pos.1 h

theorem W_pos : 0 < I.W := by
  obtain ⟨c, hc⟩ := I.exists_city
  exact lt_of_le_of_lt (Nat.zero_le _) (I.cities_inBounds c hc).1

theorem H_pos : 0 < I.H := by
  obtain ⟨c, hc⟩ := I.exists_city
  exact lt_of_le_of_lt (Nat.zero_le _) (I.cities_inBounds c hc).2

theorem W_le : I.W ≤ I.W * I.H := Nat.le_mul_of_pos_right _ I.H_pos

theorem H_le : I.H ≤ I.W * I.H := Nat.le_mul_of_pos_left _ I.W_pos

theorem WH_lt_size : I.W * I.H < I.size := Nat.lt_succ_self _

/-- The finsets of an instance have fewer than `I.size` elements; this is what the
`I.size` ticks of `memBlockedT`, `memPortsT` and `memCitiesT` pay for. -/
theorem card_le_of_inBounds (s : Finset Cell) (h : ∀ c ∈ s, c.1 < I.W ∧ c.2 < I.H) :
    s.card < I.size := by
  have hsub : s ⊆ Finset.range I.W ×ˢ Finset.range I.H := by
    intro c hc
    simp only [Finset.mem_product, Finset.mem_range]
    exact h c hc
  have := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at this
  exact lt_of_le_of_lt this I.WH_lt_size

theorem card_blocked_lt : I.blocked.card < I.size :=
  I.card_le_of_inBounds _ I.blocked_inBounds

theorem card_ports_lt : I.ports.card < I.size := I.card_le_of_inBounds _ I.ports_inBounds

theorem card_cities_lt : I.cities.card < I.size := I.card_le_of_inBounds _ I.cities_inBounds

@[simp] theorem memBlockedT_time (c : Cell) : (I.memBlockedT c).time = I.size := rfl
@[simp] theorem memPortsT_time (c : Cell) : (I.memPortsT c).time = I.size := rfl
@[simp] theorem memCitiesT_time (c : Cell) : (I.memCitiesT c).time = I.size := rfl

@[simp] theorem isOpenT_time (c : Cell) : (I.isOpenT c).time = I.size + 2 := by
  simp only [isOpenT, bind_time, tickN_time, memBlockedT_time, pure_time]
  omega

@[simp] theorem isFreeT_time (c : Cell) : (I.isFreeT c).time = 3 * I.size + 3 := by
  simp only [isFreeT, bind_time, isOpenT_time, memPortsT_time, memCitiesT_time, tick_time,
    pure_time]
  omega

@[simp] theorem gridAdjT_time (a b : Cell) : (I.gridAdjT a b).time = 2 * I.size + 20 := by
  simp only [gridAdjT, bind_time, tickN_time, isOpenT_time, pure_time]
  omega

theorem cellsT_time_le {m : ℕ} (hm : 32 * I.size ≤ m) : I.cellsT.time ≤ m ^ 4 := by
  have h16 : 16 ≤ m := by
    have := I.WH_lt_size
    omega
  have hW : I.W ≤ m := by
    have := I.W_le
    have := I.WH_lt_size
    omega
  have hH : I.H ≤ m := by
    have := I.H_le
    have := I.WH_lt_size
    omega
  simp only [cellsT, bind_time, rangeT_val]
  have h1 : (rangeT I.W).time ≤ m ^ 3 :=
    (rangeT_time_le I.W).trans (comb_le h16 hW (le_pow_one hW))
  have h2 : (rangeT I.H).time ≤ m ^ 3 :=
    (rangeT_time_le I.H).trans (comb_le h16 hH (le_pow_one hH))
  have h3 : (flatMapT (fun x => mapT (fun y => do tick; pure (x, y)) (List.range I.H))
      (List.range I.W)).time ≤ m ^ 3 := by
    refine (flatMapT_time_le _ (2 * I.H) I.H _ ?_ ?_).trans ?_
    · intro x _
      refine (mapT_time_le _ 1 _ ?_).trans ?_
      · intro y _
        simp
      · simp only [List.length_range]
        omega
    · intro x _
      rw [mapT_length, List.length_range]
    · rw [List.length_range]
      have h4 : 2 * I.H + I.H ≤ m ^ 1 := by
        rw [pow_one]
        have := I.H_le
        have := I.WH_lt_size
        omega
      exact comb_le h16 hW h4
  exact lin_le_pow h16 (by omega)

theorem gridEdgesT_time_le {m : ℕ} (hm : 32 * I.size ≤ m) (cells : List Cell)
    (hc : cells.length ≤ m) : (I.gridEdgesT cells).time ≤ m ^ 4 := by
  have h16 : 16 ≤ m := by
    have := I.WH_lt_size
    omega
  unfold gridEdgesT
  refine (flatMapT_time_le _ (m ^ 2 - 5) 4 _ ?_ ?_).trans ?_
  · intro a _
    simp only [bind_time, nbr4T, tickN_time, pure_time, pure_val, bind_val]
    have h1 : (filterT (fun b => I.gridAdjT a b) (nbr4 a)).time ≤ 4 * (2 * I.size + 20 + 1) :=
      filterT_time_le _ _ _ (fun b _ => by simp)
    have h2 : (mapT (fun b => do tick; pure (a, b))
        (filterT (fun b => I.gridAdjT a b) (nbr4 a)).val).time ≤ 4 * 2 := by
      refine (mapT_time_le _ 1 _ (fun b _ => by simp)).trans ?_
      have := filterT_length_le (fun b => I.gridAdjT a b) (nbr4 a)
      have h4 : (nbr4 a).length = 4 := rfl
      omega
    have h3 : 16 * m ≤ m ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ h16
    omega
  · intro a _
    simp only [bind_val, nbr4T, pure_val, mapT_length]
    have := filterT_length_le (fun b => I.gridAdjT a b) (nbr4 a)
    have h4 : (nbr4 a).length = 4 := rfl
    omega
  · have h3 : 16 * m ≤ m ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ h16
    have h4 : m ^ 2 - 5 + 4 ≤ m ^ 2 := by omega
    exact comb_le h16 hc h4

theorem portsT_time_le {m : ℕ} (hm : 32 * I.size ≤ m) (cells : List Cell)
    (hc : cells.length ≤ m) : (I.portsT cells).time ≤ m ^ 3 := by
  have h16 : 16 ≤ m := by
    have := I.WH_lt_size
    omega
  refine (filterT_time_le _ I.size _ (fun a _ => by simp)).trans ?_
  exact comb_le h16 hc (le_pow_one (by omega))

theorem citiesT_time_le {m : ℕ} (hm : 32 * I.size ≤ m) (cells : List Cell)
    (hc : cells.length ≤ m) : (I.citiesT cells).time ≤ m ^ 3 := by
  have h16 : 16 ≤ m := by
    have := I.WH_lt_size
    omega
  refine (filterT_time_le _ I.size _ (fun a _ => by simp)).trans ?_
  exact comb_le h16 hc (le_pow_one (by omega))

end Instance

/-! ### Distances -/

section Check

variable {I : Instance} {m : ℕ}

theorem m_ge (hm : 32 * I.size ≤ m) : 16 ≤ m := by
  have := I.WH_lt_size
  omega

theorem length_stepL_le (free : Cell → Bool) (E : List (Cell × Cell)) (first : Bool)
    (A : List Cell) : (stepL free E first A).length ≤ 2 * E.length := by
  simp only [stepL, List.length_append, List.length_map]
  have h1 := List.length_filter_le
    (fun e : Cell × Cell => decide (e.1 ∈ A) && (first || free e.1)) E
  have h2 := List.length_filter_le
    (fun e : Cell × Cell => decide (e.2 ∈ A) && (first || free e.2)) E
  omega

theorem stepT_time_le (hm : 32 * I.size ≤ m) (E : List (Cell × Cell)) (hE : E.length ≤ m)
    (A : List Cell) (hA : A.length ≤ m) (first : Bool) :
    (stepT I E first A).time ≤ m ^ 5 := by
  have h16 := m_ge hm
  have hp : ∀ x : Cell, 2 * A.length + (3 * I.size + 3 + 1) ≤ m ^ 2 := fun _ =>
    lin_le_sq h16 (by omega)
  simp only [stepT, bind_time, appendT_time, mapT_length]
  calc _ ≤ m ^ 4 + (m ^ 4 + (m ^ 4 + (m ^ 4 + m ^ 4))) := by
        gcongr
        · refine filterT_time_pow h16 _ _ hE (fun e _ => ?_)
          simpa using hp e.1
        · refine le_pow_of_le h16 (mapT_time_pow (i := 0) h16 _ _
            ((filterT_length_le _ _).trans hE) (fun e _ => by simp)) (by omega)
        · refine filterT_time_pow h16 _ _ hE (fun e _ => ?_)
          simpa using hp e.2
        · refine le_pow_of_le h16 (mapT_time_pow (i := 0) h16 _ _
            ((filterT_length_le _ _).trans hE) (fun e _ => by simp)) (by omega)
        · exact le_pow_of_le h16 (le_pow_one ((filterT_length_le _ _).trans hE)) (by omega)
    _ ≤ m ^ 5 := lin_le_pow h16 (by omega)

theorem distT_time_le (hm : 32 * I.size ≤ m) (E : List (Cell × Cell))
    (hE : 2 * E.length + 1 ≤ m) (t : Cell) :
    ∀ (f i : ℕ) (A : List Cell), A.length ≤ 2 * E.length + 1 →
      (distT I E t f i A).time ≤ (f + 1) * m ^ 6
  | 0, i, A, hA => by
    have h16 := m_ge hm
    have h1 : 1 + 2 * A.length ≤ m ^ 6 :=
      le_pow_of_le h16 (lin_le_sq h16 (by omega)) (by omega)
    simp only [distT, bind_time, tick_time, memT_time, pure_time]
    omega
  | f + 1, i, A, hA => by
    have h16 := m_ge hm
    have h1 : 1 + 2 * A.length ≤ m ^ 5 :=
      le_pow_of_le h16 (lin_le_sq h16 (by omega)) (by omega)
    have h2 : 1 + 2 * A.length + m ^ 5 ≤ m ^ 6 := lin_le_pow h16 (by omega)
    have e : (f + 1 + 1) * m ^ 6 = (f + 1) * m ^ 6 + m ^ 6 := by ring
    have h0 : 0 ≤ (f + 1) * m ^ 6 := Nat.zero_le _
    simp only [distT, bind_time, tick_time, memT_time, memT_val]
    by_cases h : t ∈ A
    · simp only [h, decide_true, ↓reduceIte, pure_time, e]
      omega
    · have hs := stepT_time_le hm E (by omega) A (by omega) (i == 0)
      have ih := distT_time_le hm E hE t f (i + 1) (stepT I E (i == 0) A).val (by
        rw [stepT_val]
        exact (length_stepL_le _ _ _ _).trans (by omega))
      simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, bind_time, e]
      omega

theorem netDistT_time_le (hm : 32 * I.size ≤ m) (E : List (Cell × Cell))
    (hE : 2 * E.length + 1 ≤ m) (s t : Cell) : (netDistT I E s t).time ≤ m ^ 8 := by
  have h16 := m_ge hm
  have hd := distT_time_le hm E hE t (2 * E.length) 0 [s] (by simp)
  have h1 : (2 * E.length + 1) * m ^ 6 ≤ m ^ 7 :=
    calc (2 * E.length + 1) * m ^ 6 ≤ m * m ^ 6 := Nat.mul_le_mul_right _ hE
      _ = m ^ 7 := by ring
  have h2 : E.length + 1 ≤ m ^ 7 := le_pow_of_le h16 (le_pow_one (by omega)) (by omega)
  simp only [netDistT, bind_time, lengthT_time, lengthT_val, tick_time]
  exact lin_le_pow h16 (by omega)

/-! ### The feasibility test and the cost -/

theorem lookupT_time_le (p : Cell) :
    ∀ ch : List (Cell × List Cell), (lookupT p ch).time ≤ 2 * ch.length
  | [] => by simp [lookupT]
  | (q, S) :: r => by
    have ih := lookupT_time_le p r
    simp only [lookupT, bind_time, tickN_time, List.length_cons]
    by_cases h : q = p
    · simp only [h, ↓reduceIte, pure_time]
      omega
    · simp only [h, ↓reduceIte]
      omega

theorem length_endsL (E : List (Cell × Cell)) : (endsL E).length = 2 * E.length := by
  simp only [endsL, List.length_append, List.length_map]
  omega

theorem endsT_time_le (hm : 16 ≤ m) (E : List (Cell × Cell)) (hE : E.length ≤ m) :
    (endsT E).time ≤ m ^ 3 := by
  simp only [endsT, bind_time, appendT_time, mapT_length]
  calc _ ≤ m ^ 2 + (m ^ 2 + m ^ 2) := by
        gcongr
        · exact mapT_time_pow (i := 0) hm _ _ hE (fun e _ => by simp)
        · exact mapT_time_pow (i := 0) hm _ _ hE (fun e _ => by simp)
        · exact le_pow_of_le hm (le_pow_one hE) (by omega)
    _ ≤ m ^ 3 := lin_le_pow hm (by omega)

theorem length_nbrL_le (E : List (Cell × Cell)) (x : Cell) :
    (nbrL E x).length ≤ 2 * E.length := by
  simp only [nbrL, List.length_append, List.length_map]
  have h1 := List.length_filter_le (fun e : Cell × Cell => decide (e.1 = x)) E
  have h2 := List.length_filter_le (fun e : Cell × Cell => decide (e.2 = x)) E
  omega

theorem nbrT_time_le (hm : 16 ≤ m) (E : List (Cell × Cell)) (hE : E.length ≤ m) (x : Cell) :
    (nbrT E x).time ≤ m ^ 4 := by
  simp only [nbrT, bind_time, appendT_time, mapT_length]
  calc _ ≤ m ^ 3 + (m ^ 3 + (m ^ 3 + (m ^ 3 + m ^ 3))) := by
        gcongr
        · exact filterT_time_pow (i := 1) hm _ _ hE (fun e _ => le_pow_one (by simp; omega))
        · exact le_pow_of_le hm (mapT_time_pow (i := 0) hm _ _
            ((filterT_length_le _ _).trans hE) (fun e _ => by simp)) (by omega)
        · exact filterT_time_pow (i := 1) hm _ _ hE (fun e _ => le_pow_one (by simp; omega))
        · exact le_pow_of_le hm (mapT_time_pow (i := 0) hm _ _
            ((filterT_length_le _ _).trans hE) (fun e _ => by simp)) (by omega)
        · exact le_pow_of_le hm (le_pow_one ((filterT_length_le _ _).trans hE)) (by omega)
    _ ≤ m ^ 4 := lin_le_pow hm (by omega)

theorem degOKT_time_le (hm : 32 * I.size ≤ m) (E : List (Cell × Cell))
    (hE : 2 * E.length ≤ m) : (degOKT I E).time ≤ m ^ 8 := by
  have h16 := m_ge hm
  have hE' : E.length ≤ m := by omega
  simp only [degOKT, bind_time, endsT_val]
  calc _ ≤ m ^ 7 + m ^ 7 := by
        gcongr
        · exact le_pow_of_le h16 (endsT_time_le h16 E hE') (by omega)
        · refine allT_time_pow (i := 5) h16 _ _ (by rw [length_endsL]; exact hE) (fun x _ => ?_)
          simp only [bind_time, Instance.isFreeT_time, nbrT_val, dedupT_val, lengthT_time,
            tick_time, pure_time]
          have h1 := nbrT_time_le h16 E hE' x
          have h2 := dedupT_time_le_pow h16 (nbrL E x) ((length_nbrL_le E x).trans hE)
          have h3 : (nbrL E x).dedup.length ≤ m ^ 4 :=
            le_pow_of_le h16 (le_pow_one (((List.dedup_sublist _).length_le.trans
              (length_nbrL_le E x)).trans hE)) (by omega)
          have h4 : 3 * I.size + 3 + 1 ≤ m ^ 4 :=
            le_pow_of_le h16 (le_pow_one (by omega)) (by omega)
          exact lin_le_pow h16 (by omega)
    _ ≤ m ^ 8 := lin_le_pow h16 (by omega)

theorem tilesT_time_le (hm : 32 * I.size ≤ m) (E : List (Cell × Cell))
    (hE : 2 * E.length ≤ m) : (tilesT I E).time ≤ m ^ 5 := by
  have h16 := m_ge hm
  have hE' : E.length ≤ m := by omega
  have hl : (endsL E).length ≤ m := by
    rw [length_endsL]
    exact hE
  simp only [tilesT, bind_time, endsT_val, filterT_val, dedupT_val, lengthT_time]
  calc _ ≤ m ^ 4 + (m ^ 4 + (m ^ 4 + m ^ 4)) := by
        gcongr
        · exact le_pow_of_le h16 (endsT_time_le h16 E hE') (by omega)
        · exact le_pow_of_le h16 (filterT_time_pow (i := 1) h16 _ _ hl
            (fun x _ => le_pow_one (by simp; omega))) (by omega)
        · exact dedupT_time_le_pow h16 _ ((List.length_filter_le _ _).trans hl)
        · exact le_pow_of_le h16 (le_pow_one (((List.dedup_sublist _).length_le.trans
            (List.length_filter_le _ _)).trans hl)) (by omega)
    _ ≤ m ^ 5 := lin_le_pow h16 (by omega)

theorem selOKT_time_le (hm : 32 * I.size ≤ m) (ge : List (Cell × Cell))
    (hge : 2 * ge.length + 1 ≤ m) (cities S : List Cell) (hc : cities.length ≤ m)
    (hS : S.length ≤ m) (p : Cell) : (selOKT I ge cities S p).time ≤ m ^ 14 := by
  have h16 := m_ge hm
  simp only [selOKT, bind_time, dedupT_val, lengthT_time, tick_time, pure_time]
  calc _ ≤ m ^ 13 + (m ^ 13 + (m ^ 13 + (m ^ 13 + (m ^ 13 + (m ^ 13 + 0))))) := by
        gcongr
        · exact le_pow_of_le h16 (allT_time_pow (i := 1) h16 _ _ hS
            (fun x _ => le_pow_one (by simp; omega))) (by omega)
        · exact le_pow_of_le h16 (dedupT_time_le_pow h16 S hS) (by omega)
        · exact le_pow_of_le h16 (le_pow_one ((List.dedup_sublist _).length_le.trans hS))
            (by omega)
        · exact one_le_pow' h16 13
        · refine le_pow_of_le h16 (allT_time_pow (i := 9) h16 _ _ hS (fun x _ => ?_)) (by omega)
          have := netDistT_time_le hm ge hge p x
          have h1 := one_le_pow' h16 8
          simp only [bind_time, tick_time, pure_time]
          exact lin_le_pow h16 (by omega)
        · refine allT_time_pow (i := 11) h16 _ _ hS (fun x _ => ?_)
          refine allT_time_pow (i := 9) h16 _ _ hc (fun y _ => ?_)
          have h1 := netDistT_time_le hm ge hge p x
          have h2 := netDistT_time_le hm ge hge p y
          have h3 : 2 * S.length + 2 ≤ m ^ 8 :=
            le_pow_of_le h16 (lin_le_sq h16 (by omega)) (by omega)
          simp only [bind_time, memT_time, tickN_time, pure_time]
          exact lin_le_pow h16 (by omega)
    _ ≤ m ^ 14 := lin_le_pow h16 (by omega)

theorem connOKT_time_le (hm : 32 * I.size ≤ m) (E : List (Cell × Cell))
    (hE : 2 * E.length + 1 ≤ m) (S : List Cell) (hS : S.length ≤ m) (p : Cell) :
    (connOKT I E S p).time ≤ m ^ 11 := by
  have h16 := m_ge hm
  refine allT_time_pow (i := 9) h16 _ _ hS (fun x _ => ?_)
  have := netDistT_time_le hm E hE p x
  have h1 := one_le_pow' h16 8
  simp only [bind_time, tick_time, pure_time]
  exact lin_le_pow h16 (by omega)

/-- A candidate whose lists have length at most `m` (up to small factors). -/
structure Small (m : ℕ) (c : Cand) : Prop where
  edges : 2 * c.edges.length + 1 ≤ m
  choice : 2 * c.choice.length ≤ m
  sel : ∀ p, (lookupL p c.choice).length ≤ m

theorem feasT_time_le (hm : 32 * I.size ≤ m) (ge : List (Cell × Cell))
    (hge : 2 * ge.length + 1 ≤ m) (ports cities : List Cell) (hp : ports.length ≤ m)
    (hc : cities.length ≤ m) (c : Cand) (hs : Small m c) :
    (feasT I ge ports cities c).time ≤ m ^ 18 := by
  have h16 := m_ge hm
  have hsz : 1 ≤ I.size := Nat.succ_le_succ (Nat.zero_le _)
  simp only [feasT, bind_time, pure_time]
  calc _ ≤ m ^ 17 + (m ^ 17 + (m ^ 17 + 0)) := by
        gcongr
        · exact le_pow_of_le h16 (allT_time_pow (i := 1) h16 _ _ (by have := hs.edges; omega)
            (fun e _ => le_pow_one (by simp; omega))) (by omega)
        · exact le_pow_of_le h16 (degOKT_time_le hm c.edges (by have := hs.edges; omega))
            (by omega)
        · refine allT_time_pow (i := 15) h16 _ _ hp (fun q _ => ?_)
          simp only [bind_time, lookupT_val, tick_time, pure_time]
          have h1 := lookupT_time_le q c.choice
          have h2 := selOKT_time_le hm ge hge cities (lookupL q c.choice) hc (hs.sel q) q
          have h3 := connOKT_time_le hm c.edges hs.edges (lookupL q c.choice) (hs.sel q) q
          have h4 : 2 * c.choice.length + 1 ≤ m ^ 14 :=
            le_pow_of_le h16 (lin_le_sq h16 (by have := hs.choice; omega)) (by omega)
          have h5 : m ^ 11 ≤ m ^ 14 := Nat.pow_le_pow_right (by omega) (by omega)
          exact lin_le_pow h16 (by omega)
    _ ≤ m ^ 18 := lin_le_pow h16 (by omega)

theorem excessT_time_le (hm : 32 * I.size ≤ m) (ge : List (Cell × Cell))
    (hge : 2 * ge.length + 1 ≤ m) (ports : List Cell) (hp : ports.length ≤ m) (c : Cand)
    (hs : Small m c) : (excessT I ge ports c).time ≤ m ^ 15 := by
  have h16 := m_ge hm
  simp only [excessT, bind_time, sumT_time, mapT_length]
  calc _ ≤ m ^ 14 + m ^ 14 := by
        gcongr
        · refine mapT_time_pow (i := 12) h16 _ _ hp (fun q _ => ?_)
          simp only [bind_time, lookupT_val, dedupT_val, sumT_time, mapT_length]
          have hd : (lookupL q c.choice).dedup.length ≤ m :=
            (List.dedup_sublist _).length_le.trans (hs.sel q)
          have h1 := lookupT_time_le q c.choice
          have h2 := dedupT_time_le_pow h16 (lookupL q c.choice) (hs.sel q)
          have h3 : (mapT (fun x => do
              let a ← netDistT I c.edges q x
              let b ← netDistT I ge q x
              tickN 3
              pure (a.getD 0 - b.getD 0)) (lookupL q c.choice).dedup).time ≤ m ^ 11 := by
            refine mapT_time_pow (i := 9) h16 _ _ hd (fun x _ => ?_)
            have h5 := netDistT_time_le hm c.edges hs.edges q x
            have h6 := netDistT_time_le hm ge hge q x
            have h7 := one_le_pow' h16 8
            simp only [bind_time, tickN_time, pure_time]
            exact lin_le_pow h16 (by omega)
          have h4 : 2 * c.choice.length + m ≤ m ^ 11 :=
            le_pow_of_le h16 (lin_le_sq h16 (by have := hs.choice; omega)) (by omega)
          have h8 : m ^ 4 ≤ m ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
          exact lin_le_pow h16 (by omega)
        · exact le_pow_of_le h16 (le_pow_one hp) (by omega)
    _ ≤ m ^ 15 := lin_le_pow h16 (by omega)

theorem costT_time_le (hm : 32 * I.size ≤ m) (ge : List (Cell × Cell))
    (hge : 2 * ge.length + 1 ≤ m) (ports : List Cell) (hp : ports.length ≤ m) (c : Cand)
    (hs : Small m c) : (costT I ge ports c).time ≤ m ^ 16 := by
  have h16 := m_ge hm
  have h1 := excessT_time_le hm ge hge ports hp c hs
  have h2 := tilesT_time_le hm c.edges (by have := hs.edges; omega)
  have h3 : m ^ 5 ≤ m ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 := one_le_pow' h16 15
  simp only [costT, bind_time, tick_time, pure_time]
  exact lin_le_pow h16 (by omega)

theorem betterT_time_le (hm : 32 * I.size ≤ m) (ge : List (Cell × Cell))
    (hge : 2 * ge.length + 1 ≤ m) (ports cities : List Cell) (hp : ports.length ≤ m)
    (hc : cities.length ≤ m) (acc : Option (Cand × (ℕ × ℕ))) (c : Cand) (hs : Small m c) :
    (betterT I ge ports cities acc c).time ≤ m ^ 19 := by
  have h16 := m_ge hm
  have h1 := feasT_time_le hm ge hge ports cities hp hc c hs
  have h2 := costT_time_le hm ge hge ports hp c hs
  have h3 : m ^ 16 ≤ m ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 := one_le_pow' h16 18
  simp only [betterT, bind_time]
  by_cases hf : (feasT I ge ports cities c).val = true
  · simp only [hf, ↓reduceIte, bind_time, tickN_time]
    cases acc with
    | none =>
      simp only [pure_time]
      exact lin_le_pow h16 (by omega)
    | some r =>
      simp only [pure_time]
      exact lin_le_pow h16 (by omega)
  · simp only [hf, Bool.false_eq_true, ↓reduceIte, pure_time]
    exact lin_le_pow h16 (by omega)

end Check

/-! ### Enumeration -/

theorem sublT_time_le {α : Type} : ∀ l : List α, (sublT l).time + 3 ≤ 4 * 2 ^ l.length
  | [] => by simp [sublT]
  | a :: l => by
    have ih := sublT_time_le l
    have h1 : (mapT (fun s => do tick; pure (a :: s)) (subl l)).time ≤ (subl l).length * (1 + 1) :=
      mapT_time_le _ 1 _ (fun s _ => by simp)
    have h2 : 1 ≤ 2 ^ l.length := Nat.one_le_two_pow
    have e : 4 * 2 ^ (l.length + 1) = 8 * 2 ^ l.length := by ring
    simp only [sublT, bind_time, tick_time, sublT_val, appendT_time, List.length_cons, e]
    rw [length_subl] at h1 ⊢
    omega

theorem length_of_mem_choicesL (sub : List (List Cell)) :
    ∀ (ps : List Cell) (ch : List (Cell × List Cell)), ch ∈ choicesL sub ps →
      ch.length = ps.length
  | [], ch, h => by
    obtain rfl : ch = [] := by simpa [choicesL] using h
    rfl
  | p :: ps, ch, h => by
    simp only [choicesL, List.mem_flatMap, List.mem_map] at h
    obtain ⟨S, -, r, hr, rfl⟩ := h
    simp [length_of_mem_choicesL sub ps r hr]

theorem lookupL_of_mem_choicesL (sub : List (List Cell)) :
    ∀ (ps : List Cell) (ch : List (Cell × List Cell)), ch ∈ choicesL sub ps →
      ∀ q, lookupL q ch = [] ∨ lookupL q ch ∈ sub
  | [], ch, h, q => by
    obtain rfl : ch = [] := by simpa [choicesL] using h
    exact Or.inl rfl
  | p :: ps, ch, h, q => by
    simp only [choicesL, List.mem_flatMap, List.mem_map] at h
    obtain ⟨S, hS, r, hr, rfl⟩ := h
    simp only [lookupL]
    by_cases hpq : p = q
    · simp only [hpq, ↓reduceIte]
      exact Or.inr hS
    · simp only [hpq, ↓reduceIte]
      exact lookupL_of_mem_choicesL sub ps r hr q

theorem choicesT_time_le (sub : List (List Cell)) (hs : 1 ≤ sub.length) :
    ∀ ps : List Cell,
      (choicesT sub ps).time ≤ (ps.length + 1) * (5 * sub.length ^ ps.length)
  | [] => by simp [choicesT]
  | p :: ps => by
    have ih := choicesT_time_le sub hs ps
    have hX : 1 ≤ sub.length ^ ps.length := Nat.one_le_pow _ _ hs
    have hf : (flatMapT (fun S => mapT (fun x => do tick; pure ((p, S) :: x))
        (choicesL sub ps)) sub).time ≤
        sub.length * (2 * sub.length ^ ps.length + sub.length ^ ps.length + 1) := by
      refine flatMapT_time_le _ _ _ _ (fun S _ => ?_) (fun S _ => ?_)
      · refine (mapT_time_le _ 1 _ (fun x _ => by simp)).trans ?_
        rw [length_choicesL]
        omega
      · rw [mapT_length, length_choicesL]
    have e1 : sub.length * (2 * sub.length ^ ps.length + sub.length ^ ps.length + 1) =
        3 * sub.length ^ (ps.length + 1) + sub.length := by ring
    have hXY : sub.length ^ ps.length ≤ sub.length ^ (ps.length + 1) :=
      Nat.pow_le_pow_right hs (Nat.le_succ _)
    have hsY : sub.length ≤ sub.length ^ (ps.length + 1) := by
      calc sub.length = 1 * sub.length := (one_mul _).symm
        _ ≤ sub.length ^ ps.length * sub.length := Nat.mul_le_mul_right _ hX
        _ = sub.length ^ (ps.length + 1) := by ring
    have h3 : (ps.length + 1) * (5 * sub.length ^ ps.length) ≤
        (ps.length + 1) * (5 * sub.length ^ (ps.length + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXY)
    have e2 : (ps.length + 1 + 1) * (5 * sub.length ^ (ps.length + 1)) =
        (ps.length + 1) * (5 * sub.length ^ (ps.length + 1)) +
          5 * sub.length ^ (ps.length + 1) := by ring
    simp only [choicesT, bind_time, tick_time, choicesT_val, List.length_cons, e2]
    rw [e1] at hf
    omega

/-! ### The solver -/

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by norm_num) h

/-- **Exponential** running-time bound for the exhaustive solver. -/
theorem solveT_time_le (I : Instance) (hP : I.ports.card ≤ 10) (hC : I.cities.card ≤ 40) :
    (solveT I).time ≤ 2 ^ (600 * I.size) := by
  have hm : 32 * I.size ≤ 32 * I.size := le_rfl
  have h16 := m_ge hm
  have hsz : 1 ≤ I.size := Nat.succ_le_succ (Nat.zero_le _)
  have hWH := I.WH_lt_size
  have hcells : I.cellsL.length ≤ 32 * I.size := by
    rw [Instance.length_cellsL]
    omega
  have hge4 : I.gridEdgesL.length ≤ 4 * I.size := by
    have := @Instance.length_gridEdgesL_le I
    omega
  have hge : 2 * I.gridEdgesL.length + 1 ≤ 32 * I.size := by omega
  have hpl : I.portsL.length ≤ 10 := by
    rw [Instance.length_portsL]
    exact hP
  have hcl : I.citiesL.length ≤ 40 := by
    rw [Instance.length_citiesL]
    exact hC
  have hcl' : I.citiesL.length ≤ 32 * I.size := by
    rw [Instance.length_citiesL]
    have := I.card_cities_lt
    omega
  have hpl' : I.portsL.length ≤ 32 * I.size := by omega
  -- the size parameter is at most a power of two
  have hm2 : 32 * I.size ≤ 2 ^ (I.size + 5) := by
    have := (Nat.lt_two_pow_self (n := I.size)).le
    calc 32 * I.size ≤ 32 * 2 ^ I.size := Nat.mul_le_mul_left _ this
      _ = 2 ^ (I.size + 5) := by ring
  have hpow : ∀ j : ℕ, (32 * I.size) ^ j ≤ 2 ^ (j * (I.size + 5)) := by
    intro j
    calc (32 * I.size) ^ j ≤ (2 ^ (I.size + 5)) ^ j := Nat.pow_le_pow_left hm2 j
      _ = 2 ^ (j * (I.size + 5)) := by rw [← pow_mul, mul_comm]
  -- the pieces
  have t1 := I.cellsT_time_le hm
  have t2 := I.gridEdgesT_time_le hm I.cellsL hcells
  have t3 := I.portsT_time_le hm I.cellsL hcells
  have t4 := I.citiesT_time_le hm I.cellsL hcells
  have t5 := sublT_time_le I.gridEdgesL
  have t6 := sublT_time_le I.citiesL
  have hsub1 : 1 ≤ (subl I.citiesL).length := by
    rw [length_subl]
    exact Nat.one_le_two_pow
  have t7 := choicesT_time_le (subl I.citiesL) hsub1 I.portsL
  -- number of choice lists
  have hchs : (choicesL (subl I.citiesL) I.portsL).length ≤ 2 ^ 400 := by
    rw [length_choicesL, length_subl, ← pow_mul]
    exact two_pow_mono (by
      calc I.citiesL.length * I.portsL.length ≤ 40 * 10 := Nat.mul_le_mul hcl hpl
        _ = 400 := by norm_num)
  -- every candidate of the loop is small
  have hsmall : ∀ E ∈ subl I.gridEdgesL, ∀ ch ∈ choicesL (subl I.citiesL) I.portsL,
      Small (32 * I.size) ⟨E, ch⟩ := by
    intro E hE ch hch
    have h1 := length_le_of_mem_subl _ _ hE
    have h2 := length_of_mem_choicesL _ _ _ hch
    refine ⟨by simp only; omega, by simp only; omega, fun q => ?_⟩
    rcases lookupL_of_mem_choicesL _ _ _ hch q with h | h
    · simp [h]
    · exact (length_le_of_mem_subl _ _ h).trans hcl'
  -- the main loop
  have t8 : (foldlT (fun acc E => foldlT (fun acc ch =>
      betterT I I.gridEdgesL I.portsL I.citiesL acc ⟨E, ch⟩) acc
        (choicesL (subl I.citiesL) I.portsL)) none (subl I.gridEdgesL)).time ≤
      (subl I.gridEdgesL).length *
        ((choicesL (subl I.citiesL) I.portsL).length * ((32 * I.size) ^ 19 + 1) + 1) := by
    refine foldlT_time_le _ _ _ none (fun b E hE => ?_)
    refine foldlT_time_le _ _ _ b (fun b' ch hch => ?_)
    exact betterT_time_le hm _ hge _ _ hpl' hcl' b' _ (hsmall E hE ch hch)
  simp only [solveT, bind_time, Instance.cellsT_val, Instance.gridEdgesT_val,
    Instance.portsT_val, Instance.citiesT_val, sublT_val, choicesT_val, lengthT_time,
    lengthT_val, tickN_time, pure_time]
  -- bound every piece by `K = 2 ^ (23 * I.size + 497)`
  have k1 : (32 * I.size) ^ 4 ≤ 2 ^ (23 * I.size + 497) :=
    (hpow 4).trans (two_pow_mono (by omega))
  have k3 : (32 * I.size) ^ 3 ≤ 2 ^ (23 * I.size + 497) :=
    (hpow 3).trans (two_pow_mono (by omega))
  have k5 : 4 * 2 ^ I.gridEdgesL.length ≤ 2 ^ (23 * I.size + 497) := by
    calc 4 * 2 ^ I.gridEdgesL.length = 2 ^ (I.gridEdgesL.length + 2) := by ring
      _ ≤ 2 ^ (23 * I.size + 497) := two_pow_mono (by omega)
  have k6 : 4 * 2 ^ I.citiesL.length ≤ 2 ^ (23 * I.size + 497) := by
    calc 4 * 2 ^ I.citiesL.length = 2 ^ (I.citiesL.length + 2) := by ring
      _ ≤ 2 ^ (23 * I.size + 497) := two_pow_mono (by omega)
  have k7 : (I.portsL.length + 1) * (5 * (subl I.citiesL).length ^ I.portsL.length) ≤
      2 ^ (23 * I.size + 497) := by
    have h1 : (subl I.citiesL).length ^ I.portsL.length ≤ 2 ^ 400 := by
      rw [← length_choicesL]
      exact hchs
    calc (I.portsL.length + 1) * (5 * (subl I.citiesL).length ^ I.portsL.length)
        ≤ 11 * (5 * 2 ^ 400) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h1)
      _ = 11 * 5 * 2 ^ 400 := (Nat.mul_assoc 11 5 (2 ^ 400)).symm
      _ ≤ 2 ^ 6 * 2 ^ 400 := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (6 + 400) := (pow_add 2 6 400).symm
      _ ≤ 2 ^ (23 * I.size + 497) := two_pow_mono (by omega)
  have k8 : (subl I.gridEdgesL).length *
      ((choicesL (subl I.citiesL) I.portsL).length * ((32 * I.size) ^ 19 + 1) + 1) ≤
      2 ^ (23 * I.size + 497) := by
    have h1 : (32 * I.size) ^ 19 + 1 ≤ 2 ^ (19 * I.size + 96) := by
      have := hpow 19
      have e : 2 ^ (19 * I.size + 96) = 2 ^ (19 * (I.size + 5)) + 2 ^ (19 * (I.size + 5)) := by
        rw [← two_mul, ← pow_succ']
        congr 1
      have h0 : 1 ≤ 2 ^ (19 * (I.size + 5)) := Nat.one_le_two_pow
      rw [e]
      omega
    have h2 : (choicesL (subl I.citiesL) I.portsL).length * ((32 * I.size) ^ 19 + 1) + 1 ≤
        2 ^ (19 * I.size + 497) := by
      have h3 : (choicesL (subl I.citiesL) I.portsL).length * ((32 * I.size) ^ 19 + 1) ≤
          2 ^ (19 * I.size + 496) := by
        calc _ ≤ 2 ^ 400 * 2 ^ (19 * I.size + 96) := Nat.mul_le_mul hchs h1
          _ = 2 ^ (400 + (19 * I.size + 96)) := (pow_add 2 400 (19 * I.size + 96)).symm
          _ ≤ 2 ^ (19 * I.size + 496) := two_pow_mono (by omega)
      have e : 2 ^ (19 * I.size + 497) = 2 ^ (19 * I.size + 496) + 2 ^ (19 * I.size + 496) := by
        rw [← two_mul, ← pow_succ']
      have h0 : 1 ≤ 2 ^ (19 * I.size + 496) := Nat.one_le_two_pow
      rw [e]
      omega
    calc _ ≤ 2 ^ (4 * I.size) * 2 ^ (19 * I.size + 497) := by
          refine Nat.mul_le_mul ?_ h2
          rw [length_subl]
          exact two_pow_mono hge4
      _ = 2 ^ (4 * I.size + (19 * I.size + 497)) :=
        (pow_add 2 (4 * I.size) (19 * I.size + 497)).symm
      _ ≤ 2 ^ (23 * I.size + 497) := two_pow_mono (by omega)
  have k9 : I.gridEdgesL.length + (I.gridEdgesL.length * I.gridEdgesL.length + 1) ≤
      2 ^ (23 * I.size + 497) := by
    have h1 : I.gridEdgesL.length * I.gridEdgesL.length ≤ (32 * I.size) * (32 * I.size) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (32 * I.size) * (32 * I.size) + (32 * I.size) + 1 ≤ (32 * I.size) ^ 3 := by
      have h3 : 16 * (32 * I.size) ^ 2 ≤ (32 * I.size) ^ 3 := by
        calc 16 * (32 * I.size) ^ 2 ≤ (32 * I.size) * (32 * I.size) ^ 2 :=
              Nat.mul_le_mul_right _ h16
          _ = (32 * I.size) ^ 3 := by ring
      have h4 : (32 * I.size) * (32 * I.size) = (32 * I.size) ^ 2 := by ring
      have h5 : 32 * I.size ≤ (32 * I.size) ^ 2 := by
        rw [← h4]
        exact Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  -- sum up
  have e : 2 ^ (23 * I.size + 501) = 16 * 2 ^ (23 * I.size + 497) := by
    rw [show 23 * I.size + 501 = 4 + (23 * I.size + 497) by omega, pow_add]
    norm_num
  calc _ ≤ 2 ^ (23 * I.size + 501) := by
        rw [e]
        omega
    _ ≤ 2 ^ (600 * I.size) := two_pow_mono (by omega)

end TrainNetwork
