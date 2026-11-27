/-
CNF-SAT (the known problem), and a cardinality gadget (sequential counter) in CNF.
-/
import TrainNetwork.Cost

namespace TrainNetwork.Answer

/-- A literal: a variable index and a polarity (`true` = positive literal). -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- An instance of SATISFIABILITY: a conjunction of clauses. -/
structure KInstance where
  clauses : List Clause

/-- Encoding length of a literal: one sign symbol plus the variable in binary. -/
def litSize (l : Lit) : ℕ := 1 + Nat.size l.1

/-- Encoding length of a clause: its literals plus one separator. -/
def clauseSize (c : Clause) : ℕ := 1 + (c.map litSize).sum

/-- Encoding length of a formula. -/
def KInstance.size (φ : KInstance) : ℕ := (φ.clauses.map clauseSize).sum

/-- Literal `l` is true under the assignment `a`. -/
def LTrue (a : ℕ → Bool) (l : Lit) : Prop := a l.1 = l.2

/-- Clause `c` is true under `a`: some literal of it is true. -/
def CTrue (a : ℕ → Bool) (c : Clause) : Prop := ∃ l ∈ c, LTrue a l

/-- `a` satisfies every clause of `φ`. -/
def Sat (a : ℕ → Bool) (φ : List Clause) : Prop := ∀ c ∈ φ, CTrue a c

/-- The formula is satisfiable. -/
def KYes (φ : KInstance) : Prop := ∃ a : ℕ → Bool, Sat a φ.clauses

section basic
variable (a : ℕ → Bool)

@[simp] theorem cTrue_nil : CTrue a [] ↔ False := by simp [CTrue]
@[simp] theorem cTrue_cons (l : Lit) (c : Clause) :
    CTrue a (l :: c) ↔ LTrue a l ∨ CTrue a c := by simp [CTrue]
@[simp] theorem cTrue_append (c d : Clause) :
    CTrue a (c ++ d) ↔ CTrue a c ∨ CTrue a d := by
  simp [CTrue, or_and_right, exists_or]
@[simp] theorem lTrue_pos (v : ℕ) : LTrue a (v, true) ↔ a v = true := Iff.rfl
@[simp] theorem lTrue_neg (v : ℕ) : LTrue a (v, false) ↔ a v = false := Iff.rfl

@[simp] theorem sat_nil : Sat a [] := by simp [Sat]
@[simp] theorem sat_cons (c : Clause) (φ : List Clause) :
    Sat a (c :: φ) ↔ CTrue a c ∧ Sat a φ := by simp [Sat]
@[simp] theorem sat_append (φ ψ : List Clause) :
    Sat a (φ ++ ψ) ↔ Sat a φ ∧ Sat a ψ := by
  simp [Sat, or_imp, forall_and]
theorem sat_flatMap {α : Type} (l : List α) (f : α → List Clause) :
    Sat a (l.flatMap f) ↔ ∀ x ∈ l, Sat a (f x) := by
  simp only [Sat, List.mem_flatMap]
  constructor
  · intro h x hx c hc; exact h c ⟨x, hx, hc⟩
  · rintro h c ⟨x, hx, hc⟩; exact h x hx c hc
theorem sat_ite (p : Prop) [Decidable p] (φ ψ : List Clause) :
    Sat a (if p then φ else ψ) ↔ (p → Sat a φ) ∧ (¬p → Sat a ψ) := by
  split_ifs with h <;> simp [h]

end basic

/-! ### The cardinality gadget -/

/-- An item is a conjunction of literals; it is active when all of them are true. -/
def iact (a : ℕ → Bool) (it : List Lit) : Bool := it.all (fun l => a l.1 == l.2)

theorem iact_iff (a : ℕ → Bool) (it : List Lit) :
    iact a it = true ↔ ∀ l ∈ it, LTrue a l := by
  simp [iact, LTrue]

/-- Number of active items. -/
def cnt (a : ℕ → Bool) (items : List (List Lit)) : ℕ := items.countP (iact a)

/-- The clause "some literal of the item is false". -/
def negLits (it : List Lit) : Clause := it.map (fun l => (l.1, !l.2))

theorem cTrue_negLits (a : ℕ → Bool) (it : List Lit) :
    CTrue a (negLits it) ↔ iact a it = false := by
  rw [← Bool.not_eq_true, iact_iff]
  simp only [CTrue, negLits, List.mem_map, LTrue]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩ hall
    have := hall l hl
    simp at this h
    rw [this] at h
    cases hb : l.2 <;> simp [hb] at h
  · intro h
    push Not at h
    obtain ⟨l, hl, hne⟩ := h
    refine ⟨(l.1, !l.2), ⟨l, hl, rfl⟩, ?_⟩
    simp only at hne ⊢
    cases hb : l.2 <;> cases ha : a l.1 <;> simp_all

/-- Clauses of the sequential counter for item number `i`. The counter variable
`cv i j` reads "more than `j` of the first `i` items are active". -/
def counterStep (cv : ℕ → ℕ → ℕ) (B i : ℕ) (it : List Lit) : List Clause :=
  (List.range (B + 1)).flatMap fun j =>
    [[(cv i j, false), (cv (i + 1) j, true)],
     if j = 0 then negLits it ++ [(cv (i + 1) 0, true)]
     else negLits it ++ [(cv i (j - 1), false), (cv (i + 1) j, true)]]

/-- The sequential counter, started at item number `i`. -/
def counterFrom (cv : ℕ → ℕ → ℕ) (B : ℕ) : ℕ → List (List Lit) → List Clause
  | i, [] => [[(cv i B, false)]]
  | i, it :: rest => counterStep cv B i it ++ counterFrom cv B (i + 1) rest

/-- "At most `B` of the items are active." -/
def atMost (cv : ℕ → ℕ → ℕ) (B : ℕ) (items : List (List Lit)) : List Clause :=
  counterFrom cv B 0 items

theorem sat_counterStep (a : ℕ → Bool) (cv : ℕ → ℕ → ℕ) (B i : ℕ) (it : List Lit) :
    Sat a (counterStep cv B i it) ↔
      ∀ j, j ≤ B → (a (cv i j) = false ∨ a (cv (i + 1) j) = true) ∧
        (iact a it = false ∨
          (if j = 0 then a (cv (i + 1) 0) = true
           else (a (cv i (j - 1)) = false ∨ a (cv (i + 1) j) = true))) := by
  unfold counterStep
  rw [sat_flatMap]
  refine forall_congr' fun j => ?_
  rw [List.mem_range, Nat.lt_succ_iff]
  refine imp_congr_right fun _ => ?_
  by_cases h0 : j = 0 <;> simp [h0, cTrue_negLits]

theorem counterFrom_sound (a : ℕ → Bool) (cv : ℕ → ℕ → ℕ) (B : ℕ) :
    ∀ (items : List (List Lit)) (i c0 : ℕ), Sat a (counterFrom cv B i items) →
      (∀ j, j < c0 → j ≤ B → a (cv i j) = true) → c0 + cnt a items ≤ B := by
  intro items
  induction items with
  | nil =>
    intro i c0 hs hinv
    simp [counterFrom] at hs
    by_contra hlt
    have h := hinv B (by simp [cnt] at hlt; omega) le_rfl
    rw [hs] at h
    exact Bool.false_ne_true h
  | cons it rest ih =>
    intro i c0 hs hinv
    simp only [counterFrom, sat_append, sat_counterStep] at hs
    obtain ⟨hstep, hrest⟩ := hs
    have hc : cnt a (it :: rest) = cnt a rest + (if iact a it = true then 1 else 0) := by
      simp [cnt, List.countP_cons]
    rw [hc]
    have := ih (i + 1) (c0 + (if iact a it = true then 1 else 0)) hrest ?_
    · omega
    · intro j hj hjB
      obtain ⟨h1, h2⟩ := hstep j hjB
      by_cases hlt : j < c0
      · rcases h1 with h1 | h1
        · rw [hinv j hlt hjB] at h1; exact absurd h1 (by simp)
        · exact h1
      · have hact : iact a it = true := by
          by_contra hna
          simp [hna] at hj
          omega
        simp [hact] at hj h2
        have hjc : j = c0 := by omega
        by_cases h0 : j = 0
        · simp [h0] at h2; rw [h0]; exact h2
        · simp [h0] at h2
          rcases h2 with h2 | h2
          · rw [hinv (j - 1) (by omega) (by omega)] at h2; exact absurd h2 (by simp)
          · exact h2

theorem atMost_sound (a : ℕ → Bool) (cv : ℕ → ℕ → ℕ) (B : ℕ) (items : List (List Lit))
    (h : Sat a (atMost cv B items)) : cnt a items ≤ B := by
  have := counterFrom_sound a cv B items 0 0 h (by intro j hj; omega)
  omega

theorem counterFrom_complete (a : ℕ → Bool) (cv : ℕ → ℕ → ℕ) (B : ℕ) :
    ∀ (items : List (List Lit)) (i c0 : ℕ),
      (∀ d j, d ≤ items.length → a (cv (i + d) j) = decide (j < c0 + cnt a (items.take d))) →
      c0 + cnt a items ≤ B → Sat a (counterFrom cv B i items) := by
  intro items
  induction items with
  | nil =>
    intro i c0 hv hB
    have := hv 0 B le_rfl
    simp [cnt] at this hB
    simp [counterFrom]
    rw [this]
    simp
    omega
  | cons it rest ih =>
    intro i c0 hv hB
    have hc : cnt a (it :: rest) = cnt a rest + (if iact a it = true then 1 else 0) := by
      simp [cnt, List.countP_cons]
    simp only [counterFrom, sat_append, sat_counterStep]
    have h0 : ∀ j, a (cv i j) = decide (j < c0) := by
      intro j; simpa [cnt] using hv 0 j (by simp)
    have h1 : ∀ j, a (cv (i + 1) j) =
        decide (j < c0 + (if iact a it = true then 1 else 0)) := by
      intro j
      have := hv 1 j (by simp)
      simpa [cnt, List.countP_cons] using this
    constructor
    · intro j _
      rw [h0, h1, h0, h1]
      by_cases hact : iact a it = true <;> by_cases hj0 : j = 0 <;>
        simp [hact, hj0] <;> omega
    · apply ih (i + 1) (c0 + (if iact a it = true then 1 else 0))
      · intro d j hd
        have := hv (d + 1) j (by simpa using hd)
        have e : i + (d + 1) = i + 1 + d := by omega
        rw [e] at this
        rw [this]
        by_cases hact : iact a it = true <;> simp [cnt, List.countP_cons, hact] <;>
          (try omega)
      · rw [hc] at hB; omega

theorem atMost_complete (a : ℕ → Bool) (cv : ℕ → ℕ → ℕ) (B : ℕ) (items : List (List Lit))
    (hv : ∀ i j, a (cv i j) = decide (j < cnt a (items.take i)))
    (hB : cnt a items ≤ B) : Sat a (atMost cv B items) := by
  apply counterFrom_complete a cv B items 0 0
  · intro d j _; simpa using hv d j
  · omega

end TrainNetwork.Answer
