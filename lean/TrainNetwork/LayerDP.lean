/-
The abstract layered dynamic programme (a shortest path in a layered graph).

Input: a list of layers `k₀, …, k_{n-1} : κ`, a list `cands : List S` of candidate
states, a self-check `selfT k s : TimeM (Option ℕ)` (cost of state `s` in layer `k`, or
`none` if `s` is not allowed there) and a link-check `linkT k s k' s' : TimeM Bool`
(may `s` in layer `k` be followed by `s'` in the next layer `k'`?).

Output of `run`: an assignment of one candidate state to every layer that passes all
checks and has minimum total cost, or `none` if there is none.

The table for a suffix of the layers holds, for every candidate state `s` of its first
layer that can be completed, the cheapest completion starting with `s`.
-/
import TrainNetwork.TimeBasic

namespace TrainNetwork
namespace LayerDP

open TimeM

variable {κ S : Type}

/-- A table entry: first state, cost of the witness, witness (one state per layer). -/
abbrev Entry (S : Type) := S × ℕ × List S

section Algorithm

variable (selfT : κ → S → TimeM (Option ℕ)) (linkT : κ → S → κ → S → TimeM Bool)

/-- Cheapest entry of `T` whose first state may follow `s`. -/
def bestLink (k : κ) (s : S) (k' : κ) : List (Entry S) → TimeM (Option (ℕ × List S))
  | [] => pure none
  | (s', c', w') :: T => do
      tick
      let r ← bestLink k s k' T
      let b ← linkT k s k' s'
      if b then
        match r with
        | none => pure (some (c', w'))
        | some (c, w) => do
            tick
            if c' ≤ c then pure (some (c', w')) else pure (some (c, w))
      else pure r

/-- Table of the last layer. -/
def initT (k : κ) : List S → TimeM (List (Entry S))
  | [] => pure []
  | s :: ss => do
      tick
      let rest ← initT k ss
      let c? ← selfT k s
      match c? with
      | none => pure rest
      | some c => do
          tick
          pure ((s, c, [s]) :: rest)

/-- Table of layer `k`, given the table `T` of the following layer `k'`. -/
def extendT (k k' : κ) (T : List (Entry S)) : List S → TimeM (List (Entry S))
  | [] => pure []
  | s :: ss => do
      tick
      let rest ← extendT k k' T ss
      let c? ← selfT k s
      match c? with
      | none => pure rest
      | some c => do
          let r ← bestLink linkT k s k' T
          match r with
          | none => pure rest
          | some (c', w') => do
              tickN 2
              pure ((s, c + c', s :: w') :: rest)

/-- Table of the first layer of `layers`, computed from the last layer backwards. -/
def tables (cands : List S) : List κ → TimeM (List (Entry S))
  | [] => pure []
  | [k] => initT selfT k cands
  | k :: k' :: ks => do
      let T ← tables cands (k' :: ks)
      extendT selfT linkT k k' T cands

/-- Cheapest entry of a table. -/
def argminT : List (Entry S) → TimeM (Option (ℕ × List S))
  | [] => pure none
  | (_, c, w) :: T => do
      tick
      let r ← argminT T
      match r with
      | none => pure (some (c, w))
      | some (c', w') => do
          tick
          if c ≤ c' then pure (some (c, w)) else pure (some (c', w'))

/-- The layered DP. -/
def run (cands : List S) (layers : List κ) : TimeM (Option (ℕ × List S)) :=
  match layers with
  | [] => pure (some (0, []))
  | _ :: _ => do
      let T ← tables selfT linkT cands layers
      argminT T

end Algorithm

section Spec

variable (selfT : κ → S → TimeM (Option ℕ)) (linkT : κ → S → κ → S → TimeM Bool)

/-- `w` gives every layer a candidate state, and all self- and link-checks pass. -/
def Valid (cands : List S) : List κ → List S → Prop
  | [], [] => True
  | k :: ks, s :: ss =>
      s ∈ cands ∧ (selfT k s).val.isSome ∧
      (match ks, ss with
        | k' :: _, s' :: _ => (linkT k s k' s').val = true
        | _, _ => True) ∧
      Valid cands ks ss
  | _, _ => False

/-- Total cost of an assignment. -/
def cost : List κ → List S → ℕ
  | k :: ks, s :: ss => (selfT k s).val.getD 0 + cost ks ss
  | _, _ => 0

variable {selfT linkT}

/-! ### `bestLink` -/

theorem bestLink_val_cons (k : κ) (s : S) (k' : κ) (s' : S) (c' : ℕ) (w' : List S)
    (T : List (Entry S)) :
    (bestLink linkT k s k' ((s', c', w') :: T)).val =
      if (linkT k s k' s').val = true then
        match (bestLink linkT k s k' T).val with
        | none => some (c', w')
        | some (c, w) => if c' ≤ c then some (c', w') else some (c, w)
      else (bestLink linkT k s k' T).val := by
  simp only [bestLink, bind_val]
  cases hb : (linkT k s k' s').val <;> cases hr : (bestLink linkT k s k' T).val
  · simp
  · simp
  · simp
  · rename_i p
    obtain ⟨c, w⟩ := p
    by_cases hc : c' ≤ c <;> simp [hc]

theorem bestLink_none {k : κ} {s : S} {k' : κ} {T : List (Entry S)}
    (h : (bestLink linkT k s k' T).val = none) :
    ∀ e ∈ T, (linkT k s k' e.1).val = false := by
  induction T with
  | nil => simp
  | cons e T ih =>
      obtain ⟨s', c', w'⟩ := e
      rw [bestLink_val_cons] at h
      cases hb : (linkT k s k' s').val
      · rw [hb] at h
        simp only [Bool.false_eq_true, ite_false] at h
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hb
        · exact ih h e he
      · rw [hb] at h
        simp only [ite_true] at h
        cases hr : (bestLink linkT k s k' T).val with
        | none => rw [hr] at h; simp at h
        | some p =>
            obtain ⟨c, w⟩ := p
            rw [hr] at h
            by_cases hc : c' ≤ c <;> simp [hc] at h

theorem bestLink_some {k : κ} {s : S} {k' : κ} {T : List (Entry S)} {c : ℕ} {w : List S}
    (h : (bestLink linkT k s k' T).val = some (c, w)) :
    (∃ s', (s', c, w) ∈ T ∧ (linkT k s k' s').val = true) ∧
      ∀ e ∈ T, (linkT k s k' e.1).val = true → c ≤ e.2.1 := by
  induction T generalizing c w with
  | nil => simp [bestLink] at h
  | cons e T ih =>
      obtain ⟨s', c', w'⟩ := e
      rw [bestLink_val_cons] at h
      cases hb : (linkT k s k' s').val
      · rw [hb] at h
        simp only [Bool.false_eq_true, ite_false] at h
        obtain ⟨⟨s'', hmem, hl⟩, hmin⟩ := ih h
        refine ⟨⟨s'', List.mem_cons_of_mem _ hmem, hl⟩, ?_⟩
        intro e he hle
        rcases List.mem_cons.mp he with rfl | he
        · simp [hb] at hle
        · exact hmin e he hle
      · rw [hb] at h
        simp only [ite_true] at h
        cases hr : (bestLink linkT k s k' T).val with
        | none =>
            rw [hr] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨⟨s', by simp, hb⟩, ?_⟩
            intro e he hle
            rcases List.mem_cons.mp he with rfl | he
            · exact le_refl _
            · have := bestLink_none hr e he
              rw [this] at hle
              exact absurd hle (by simp)
        | some p =>
            obtain ⟨c₀, w₀⟩ := p
            rw [hr] at h
            obtain ⟨⟨s'', hmem, hl⟩, hmin⟩ := ih hr
            by_cases hc : c' ≤ c₀
            · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨⟨s', by simp, hb⟩, ?_⟩
              intro e he hle
              rcases List.mem_cons.mp he with rfl | he
              · exact le_refl _
              · exact le_trans hc (hmin e he hle)
            · simp only [hc, ite_false, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨⟨s'', List.mem_cons_of_mem _ hmem, hl⟩, ?_⟩
              intro e he hle
              rcases List.mem_cons.mp he with rfl | he
              · exact le_of_lt (not_le.mp hc)
              · exact hmin e he hle

/-! ### `initT` and `extendT` -/

theorem mem_initT {k : κ} {ss : List S} {e : Entry S} :
    e ∈ (initT selfT k ss).val ↔
      ∃ s ∈ ss, ∃ c, (selfT k s).val = some c ∧ e = (s, c, [s]) := by
  induction ss with
  | nil => simp [initT]
  | cons s ss ih =>
      simp only [initT, bind_val]
      cases hc : (selfT k s).val with
      | none =>
          simp only [pure_val, List.mem_cons, exists_eq_or_imp, hc]
          simpa using ih
      | some c =>
          simp only [bind_val, pure_val, List.mem_cons, ih, exists_eq_or_imp, hc,
            Option.some.injEq]
          constructor
          · rintro (rfl | h)
            · exact Or.inl ⟨c, rfl, rfl⟩
            · exact Or.inr h
          · rintro (⟨c', rfl, rfl⟩ | h)
            · exact Or.inl rfl
            · exact Or.inr h

theorem mem_extendT {k k' : κ} {T : List (Entry S)} {ss : List S} {e : Entry S} :
    e ∈ (extendT selfT linkT k k' T ss).val ↔
      ∃ s ∈ ss, ∃ c c' w', (selfT k s).val = some c ∧
        (bestLink linkT k s k' T).val = some (c', w') ∧ e = (s, c + c', s :: w') := by
  induction ss with
  | nil => simp [extendT]
  | cons s ss ih =>
      simp only [extendT, bind_val]
      cases hc : (selfT k s).val with
      | none =>
          simp only [pure_val, List.mem_cons, exists_eq_or_imp, hc]
          simpa using ih
      | some c =>
          simp only [bind_val]
          cases hr : (bestLink linkT k s k' T).val with
          | none =>
              simp only [pure_val, List.mem_cons, exists_eq_or_imp, hc, hr]
              simpa using ih
          | some p =>
              obtain ⟨c', w'⟩ := p
              simp only [bind_val, pure_val, List.mem_cons, ih, exists_eq_or_imp, hc, hr,
                Option.some.injEq, Prod.mk.injEq]
              constructor
              · rintro (rfl | h)
                · exact Or.inl ⟨c, c', w', rfl, ⟨rfl, rfl⟩, rfl⟩
                · exact Or.inr h
              · rintro (⟨c₁, c₂, w₂, rfl, ⟨rfl, rfl⟩, rfl⟩ | h)
                · exact Or.inl rfl
                · exact Or.inr h

theorem length_initT_le (k : κ) (ss : List S) : (initT selfT k ss).val.length ≤ ss.length := by
  induction ss with
  | nil => simp [initT]
  | cons s ss ih =>
      simp only [initT, bind_val]
      cases hc : (selfT k s).val with
      | none => simp only [pure_val, List.length_cons]; omega
      | some c => simp only [bind_val, pure_val, List.length_cons]; omega

theorem length_extendT_le (k k' : κ) (T : List (Entry S)) (ss : List S) :
    (extendT selfT linkT k k' T ss).val.length ≤ ss.length := by
  induction ss with
  | nil => simp [extendT]
  | cons s ss ih =>
      simp only [extendT, bind_val]
      cases hc : (selfT k s).val with
      | none => simp only [pure_val, List.length_cons]; omega
      | some c =>
          simp only [bind_val]
          cases hr : (bestLink linkT k s k' T).val with
          | none => simp only [pure_val, List.length_cons]; omega
          | some p =>
              obtain ⟨c', w'⟩ := p
              simp only [bind_val, pure_val, List.length_cons]; omega

theorem length_tables_le (cands : List S) (layers : List κ) :
    (tables selfT linkT cands layers).val.length ≤ cands.length := by
  match layers with
  | [] => simp [tables]
  | [k] => simpa [tables] using length_initT_le k cands
  | k :: k' :: ks => simpa [tables] using length_extendT_le k k' _ cands

/-! ### The table invariant -/

/-- Every entry is a valid assignment with the stated first state and cost, and every
valid assignment is dominated by an entry with the same first state. -/
def Inv (cands : List S) (layers : List κ) (T : List (Entry S)) : Prop :=
  (∀ e ∈ T, Valid selfT linkT cands layers e.2.2 ∧ e.2.2.head? = some e.1 ∧
      cost selfT layers e.2.2 = e.2.1) ∧
  (∀ w, Valid selfT linkT cands layers w →
      ∃ e ∈ T, w.head? = some e.1 ∧ e.2.1 ≤ cost selfT layers w)

theorem valid_single {cands : List S} {k : κ} {w : List S} :
    Valid selfT linkT cands [k] w ↔ ∃ s, w = [s] ∧ s ∈ cands ∧ (selfT k s).val.isSome := by
  match w with
  | [] => simp [Valid]
  | [s] => simp [Valid]
  | s :: s' :: ss => simp [Valid]

theorem valid_cons_cons {cands : List S} {k k' : κ} {ks : List κ} {w : List S} :
    Valid selfT linkT cands (k :: k' :: ks) w ↔
      ∃ s s' ss, w = s :: s' :: ss ∧ s ∈ cands ∧ (selfT k s).val.isSome ∧
        (linkT k s k' s').val = true ∧ Valid selfT linkT cands (k' :: ks) (s' :: ss) := by
  match w with
  | [] => simp [Valid]
  | [s] => simp [Valid]
  | s :: s' :: ss => simp [Valid]

theorem tables_inv (cands : List S) (k : κ) (ks : List κ) :
    Inv (selfT := selfT) (linkT := linkT) cands (k :: ks)
      (tables selfT linkT cands (k :: ks)).val := by
  induction ks generalizing k with
  | nil =>
      constructor
      · intro e he
        simp only [tables] at he
        obtain ⟨s, hs, c, hc, rfl⟩ := mem_initT.mp he
        refine ⟨valid_single.mpr ⟨s, rfl, hs, by simp [hc]⟩, rfl, ?_⟩
        simp [cost, hc]
      · intro w hw
        obtain ⟨s, rfl, hs, hsome⟩ := valid_single.mp hw
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
        refine ⟨(s, c, [s]), ?_, rfl, ?_⟩
        · simp only [tables]
          exact mem_initT.mpr ⟨s, hs, c, hc, rfl⟩
        · simp [cost, hc]
  | cons k' ks ih =>
      obtain ⟨ih1, ih2⟩ := ih k'
      constructor
      · intro e he
        simp only [tables, bind_val] at he
        obtain ⟨s, hs, c, c', w', hc, hbest, rfl⟩ := mem_extendT.mp he
        obtain ⟨⟨s', hmem, hl⟩, -⟩ := bestLink_some hbest
        obtain ⟨hv, hhead, hcost⟩ := ih1 _ hmem
        simp only at hv hhead hcost
        obtain ⟨ss', rfl⟩ : ∃ ss', w' = s' :: ss' := by
          cases w' with
          | nil => simp at hhead
          | cons a ss' => simp at hhead; exact ⟨ss', by rw [hhead]⟩
        refine ⟨valid_cons_cons.mpr ⟨s, s', ss', rfl, hs, by simp [hc], hl, hv⟩, rfl, ?_⟩
        simp only [cost, hc, Option.getD_some] at hcost ⊢
        omega
      · intro w hw
        obtain ⟨s, s', ss, rfl, hs, hsome, hl, hv⟩ := valid_cons_cons.mp hw
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨e', he', hhead', hle'⟩ := ih2 _ hv
        have hs' : e'.1 = s' := by simpa using hhead'.symm
        cases hbest : (bestLink linkT k s k' (tables selfT linkT cands (k' :: ks)).val).val with
        | none =>
            have := bestLink_none hbest e' he'
            rw [hs', hl] at this
            exact absurd this (by simp)
        | some p =>
            obtain ⟨c₂, w₂⟩ := p
            obtain ⟨-, hmin⟩ := bestLink_some hbest
            have h2 : c₂ ≤ e'.2.1 := hmin e' he' (by rw [hs']; exact hl)
            refine ⟨(s, c + c₂, s :: w₂), ?_, rfl, ?_⟩
            · simp only [tables, bind_val]
              exact mem_extendT.mpr ⟨s, hs, c, c₂, w₂, hc, hbest, rfl⟩
            · simp only [cost, hc, Option.getD_some] at hle' ⊢
              omega

/-! ### `argminT` and the main correctness theorem -/

theorem argminT_none {T : List (Entry S)} (h : (argminT T).val = none) : T = [] := by
  cases T with
  | nil => rfl
  | cons e T =>
      obtain ⟨s, c, w⟩ := e
      simp only [argminT, bind_val] at h
      cases hr : (argminT T).val with
      | none => rw [hr] at h; simp at h
      | some p =>
          obtain ⟨c', w'⟩ := p
          rw [hr] at h
          by_cases hc : c ≤ c' <;> simp [hc] at h

theorem argminT_some {T : List (Entry S)} {c : ℕ} {w : List S}
    (h : (argminT T).val = some (c, w)) :
    (∃ s, (s, c, w) ∈ T) ∧ ∀ e ∈ T, c ≤ e.2.1 := by
  induction T generalizing c w with
  | nil => simp [argminT] at h
  | cons e T ih =>
      obtain ⟨s₀, c₀, w₀⟩ := e
      simp only [argminT, bind_val] at h
      cases hr : (argminT T).val with
      | none =>
          rw [hr] at h
          simp only [pure_val, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := argminT_none hr
          subst this
          exact ⟨⟨s₀, by simp⟩, by simp⟩
      | some p =>
          obtain ⟨c', w'⟩ := p
          rw [hr] at h
          obtain ⟨⟨s', hmem⟩, hmin⟩ := ih hr
          by_cases hc : c₀ ≤ c'
          · simp only [bind_val, hc, ite_true, pure_val, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨⟨s₀, by simp⟩, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact le_refl _
            · exact le_trans hc (hmin e he)
          · simp only [bind_val, hc, ite_false, pure_val, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨⟨s', List.mem_cons_of_mem _ hmem⟩, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact le_of_lt (not_le.mp hc)
            · exact hmin e he

/-- `run` returns a valid assignment of minimum cost. -/
theorem run_some {cands : List S} {layers : List κ} {c : ℕ} {w : List S}
    (h : (run selfT linkT cands layers).val = some (c, w)) :
    Valid selfT linkT cands layers w ∧ cost selfT layers w = c ∧
      ∀ w', Valid selfT linkT cands layers w' → c ≤ cost selfT layers w' := by
  cases layers with
  | nil =>
      simp only [run, pure_val, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [Valid], by simp [cost], fun _ _ => Nat.zero_le _⟩
  | cons k ks =>
      simp only [run, bind_val] at h
      obtain ⟨inv1, inv2⟩ := tables_inv (selfT := selfT) (linkT := linkT) cands k ks
      obtain ⟨⟨s, hmem⟩, hmin⟩ := argminT_some h
      obtain ⟨hv, -, hcost⟩ := inv1 _ hmem
      refine ⟨hv, hcost, ?_⟩
      intro w' hw'
      obtain ⟨e, he, -, hle⟩ := inv2 w' hw'
      exact le_trans (hmin e he) hle

/-- `run` returns `none` only if there is no valid assignment. -/
theorem run_none {cands : List S} {layers : List κ}
    (h : (run selfT linkT cands layers).val = none) :
    ∀ w, ¬ Valid selfT linkT cands layers w := by
  cases layers with
  | nil => simp [run] at h
  | cons k ks =>
      simp only [run, bind_val] at h
      obtain ⟨-, inv2⟩ := tables_inv (selfT := selfT) (linkT := linkT) cands k ks
      intro w hw
      obtain ⟨e, he, -, -⟩ := inv2 w hw
      rw [argminT_none h] at he
      simp at he

end Spec

section Index

variable {selfT : κ → S → TimeM (Option ℕ)} {linkT : κ → S → κ → S → TimeM Bool}

/-- `Valid`, layer by layer. -/
theorem valid_iff_getD (dk : κ) (ds : S) (cands : List S) :
    ∀ (layers : List κ) (w : List S), Valid selfT linkT cands layers w ↔
      w.length = layers.length ∧ ∀ i, i < layers.length →
        w.getD i ds ∈ cands ∧ (selfT (layers.getD i dk) (w.getD i ds)).val.isSome ∧
        (i + 1 < layers.length →
          (linkT (layers.getD i dk) (w.getD i ds) (layers.getD (i + 1) dk)
            (w.getD (i + 1) ds)).val = true)
  | [], [] => by simp [Valid]
  | [], _ :: _ => by simp [Valid]
  | _ :: _, [] => by simp [Valid]
  | k :: ks, s :: ss => by
      have ih := valid_iff_getD dk ds cands ks ss
      simp only [Valid, ih, List.length_cons, add_left_inj]
      constructor
      · rintro ⟨hs, hsome, hlink, hlen, hrest⟩
        refine ⟨hlen, ?_⟩
        intro i hi
        cases i with
        | zero =>
            refine ⟨by simpa using hs, by simpa using hsome, ?_⟩
            intro h1
            rcases ks with _ | ⟨k', ks'⟩
            · simp at h1
            · rcases ss with _ | ⟨s', ss'⟩
              · simp at hlen
              · simpa using hlink
        | succ j =>
            have := hrest j (by omega)
            simpa using this
      · rintro ⟨hlen, h⟩
        have h0 := h 0 (by omega)
        refine ⟨by simpa using h0.1, by simpa using h0.2.1, ?_, hlen, ?_⟩
        · rcases ks with _ | ⟨k', ks'⟩
          · trivial
          · rcases ss with _ | ⟨s', ss'⟩
            · simp at hlen
            · simpa using h0.2.2 (by simp)
        · intro j hj
          have := h (j + 1) (by omega)
          simpa using this

/-- `cost`, layer by layer. -/
theorem cost_eq_sum (dk : κ) (ds : S) :
    ∀ (layers : List κ) (w : List S), w.length = layers.length →
      cost selfT layers w = ∑ i ∈ Finset.range layers.length,
        (selfT (layers.getD i dk) (w.getD i ds)).val.getD 0
  | [], [], _ => by simp [cost]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | k :: ks, s :: ss, h => by
      have ih := cost_eq_sum dk ds ks ss (by simpa using h)
      simp only [cost, ih, List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

end Index

section Time

variable {selfT : κ → S → TimeM (Option ℕ)} {linkT : κ → S → κ → S → TimeM Bool}

theorem bestLink_time_le (k : κ) (s : S) (k' : κ) (T : List (Entry S)) (cL : ℕ)
    (h : ∀ e ∈ T, (linkT k s k' e.1).time ≤ cL) :
    (bestLink linkT k s k' T).time ≤ T.length * (cL + 2) := by
  induction T with
  | nil => simp [bestLink]
  | cons e T ih =>
      obtain ⟨s', c', w'⟩ := e
      have h1 : (linkT k s k' s').time ≤ cL := h (s', c', w') (by simp)
      have h2 := ih (fun e he => h e (List.mem_cons_of_mem _ he))
      simp only [bestLink, bind_time, tick_time, List.length_cons]
      cases hb : (linkT k s k' s').val <;> cases hr : (bestLink linkT k s k' T).val
      · simp only [Bool.false_eq_true, ite_false, pure_time]; nlinarith
      · simp only [Bool.false_eq_true, ite_false, pure_time]; nlinarith
      · simp only [ite_true, pure_time]; nlinarith
      · rename_i p
        obtain ⟨c, w⟩ := p
        by_cases hc : c' ≤ c <;>
          simp only [ite_true, bind_time, tick_time, hc, ite_false, pure_time] <;> nlinarith

theorem initT_time_le (k : κ) (ss : List S) (cS : ℕ)
    (h : ∀ s ∈ ss, (selfT k s).time ≤ cS) :
    (initT selfT k ss).time ≤ ss.length * (cS + 2) := by
  induction ss with
  | nil => simp [initT]
  | cons s ss ih =>
      have h1 := h s (by simp)
      have h2 := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
      simp only [initT, bind_time, tick_time, List.length_cons]
      cases hc : (selfT k s).val with
      | none => simp only [pure_time]; nlinarith
      | some c => simp only [bind_time, tick_time, pure_time]; nlinarith

theorem extendT_time_le (k k' : κ) (T : List (Entry S)) (ss : List S) (cS cL : ℕ)
    (hS : ∀ s ∈ ss, (selfT k s).time ≤ cS)
    (hL : ∀ s ∈ ss, ∀ e ∈ T, (linkT k s k' e.1).time ≤ cL) :
    (extendT selfT linkT k k' T ss).time ≤ ss.length * (cS + T.length * (cL + 2) + 3) := by
  induction ss with
  | nil => simp [extendT]
  | cons s ss ih =>
      have h1 := hS s (by simp)
      have h2 := ih (fun t ht => hS t (List.mem_cons_of_mem _ ht))
        (fun t ht => hL t (List.mem_cons_of_mem _ ht))
      have h3 := bestLink_time_le k s k' T cL (hL s (by simp))
      simp only [extendT, bind_time, tick_time, List.length_cons]
      cases hc : (selfT k s).val with
      | none => simp only [pure_time]; nlinarith
      | some c =>
          simp only [bind_time]
          cases hr : (bestLink linkT k s k' T).val with
          | none => simp only [pure_time]; nlinarith
          | some p =>
              obtain ⟨c', w'⟩ := p
              simp only [bind_time, tickN_time, pure_time]; nlinarith

theorem fst_mem_tables {cands : List S} {layers : List κ} {e : Entry S}
    (he : e ∈ (tables selfT linkT cands layers).val) : e.1 ∈ cands := by
  match layers with
  | [] => simp [tables] at he
  | [k] =>
      simp only [tables] at he
      obtain ⟨s, hs, c, -, rfl⟩ := mem_initT.mp he
      exact hs
  | k :: k' :: ks =>
      simp only [tables, bind_val] at he
      obtain ⟨s, hs, c, c', w', -, -, rfl⟩ := mem_extendT.mp he
      exact hs

theorem tables_time_le (cands : List S) (cS cL : ℕ) :
    ∀ layers : List κ,
      (∀ k ∈ layers, ∀ s ∈ cands, (selfT k s).time ≤ cS) →
      (∀ k ∈ layers, ∀ k' ∈ layers, ∀ s ∈ cands, ∀ s' ∈ cands,
        (linkT k s k' s').time ≤ cL) →
      (tables selfT linkT cands layers).time ≤
        layers.length * (cands.length * (cS + cands.length * (cL + 2) + 3))
  | [], _, _ => by simp [tables]
  | [k], hS, _ => by
      have h1 := initT_time_le (selfT := selfT) k cands cS (hS k (by simp))
      have h2 : cands.length * (cS + 2) ≤ cands.length * (cS + cands.length * (cL + 2) + 3) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [tables, List.length_cons, List.length_nil]
      omega
  | k :: k' :: ks, hS, hL => by
      have ih := tables_time_le cands cS cL (k' :: ks)
        (fun a ha => hS a (List.mem_cons_of_mem _ ha))
        (fun a ha b hb => hL a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      have hlen := length_tables_le (selfT := selfT) (linkT := linkT) cands (k' :: ks)
      have hext := extendT_time_le (selfT := selfT) (linkT := linkT) k k'
        (tables selfT linkT cands (k' :: ks)).val cands cS cL (hS k (by simp))
        (fun s hs e he => hL k (by simp) k' (by simp) s hs e.1 (fst_mem_tables he))
      simp only [tables, bind_time, List.length_cons] at ih ⊢
      have hmono : cands.length * (cS + (tables selfT linkT cands (k' :: ks)).val.length * (cL + 2) + 3)
          ≤ cands.length * (cS + cands.length * (cL + 2) + 3) := by
        apply Nat.mul_le_mul_left
        have : (tables selfT linkT cands (k' :: ks)).val.length * (cL + 2)
            ≤ cands.length * (cL + 2) := Nat.mul_le_mul_right _ hlen
        omega
      nlinarith

theorem argminT_time_le (T : List (Entry S)) : (argminT T).time ≤ 2 * T.length := by
  induction T with
  | nil => simp [argminT]
  | cons e T ih =>
      obtain ⟨s, c, w⟩ := e
      simp only [argminT, bind_time, tick_time, List.length_cons]
      cases hr : (argminT T).val with
      | none => simp only [pure_time]; omega
      | some p =>
          obtain ⟨c', w'⟩ := p
          by_cases hc : c ≤ c' <;>
            simp only [bind_time, tick_time, hc, ite_true, ite_false, pure_time] <;> omega

/-- Running time of the layered DP: `n · |cands| · (c_self + |cands| · (c_link + 2) + 3)`
plus lower-order terms. -/
theorem run_time_le (cands : List S) (cS cL : ℕ) (layers : List κ)
    (hS : ∀ k ∈ layers, ∀ s ∈ cands, (selfT k s).time ≤ cS)
    (hL : ∀ k ∈ layers, ∀ k' ∈ layers, ∀ s ∈ cands, ∀ s' ∈ cands,
      (linkT k s k' s').time ≤ cL) :
    (run selfT linkT cands layers).time ≤
      layers.length * (cands.length * (cS + cands.length * (cL + 2) + 3)) + 2 * cands.length := by
  cases layers with
  | nil => simp [run]
  | cons k ks =>
      have h1 := tables_time_le (selfT := selfT) (linkT := linkT) cands cS cL (k :: ks) hS hL
      have h2 := argminT_time_le (tables selfT linkT cands (k :: ks)).val
      have h3 := length_tables_le (selfT := selfT) (linkT := linkT) cands (k :: ks)
      simp only [run, bind_time]
      omega

end Time

end LayerDP
end TrainNetwork
