/-
The formula `enc I X K` (pure definition) and what it means, family by family, for an
assignment to satisfy it.
-/
import TrainNetwork.Encode

namespace TrainNetwork.Answer

open TrainNetwork

variable (I : Instance)

/-- Neighbours `u` of `v` that a walk from `p` may step from: `u = p` or `u` free. -/
def stepsN (p v : Cell) : List Cell := (nbrs v).filter fun u => decide (u = p) || isFreeB I u

/-- The same, restricted to steps of the grid (both cells open). -/
def stepsG (p v : Cell) : List Cell :=
  (stepsN I p v).filter fun u => isOpenB I u && isOpenB I v

/-- Clauses for the potential edge `v — u`: it joins open cells, and it makes its free
endpoints tiles. -/
def edgeAt (v u : Cell) : List Clause :=
  if isOpenB I v && isOpenB I u then
    (if isFreeB I v then [[(vEdge v u, false), (vTile v, true)]] else []) ++
    (if isFreeB I u then [[(vEdge v u, false), (vTile u, true)]] else [])
  else [[(vEdge v u, false)]]

/-- Degree clause: a free cell with four neighbours does not use all four edges. -/
def degAt (v : Cell) : List Clause :=
  if isFreeB I v && decide (1 ≤ v.1) && decide (1 ≤ v.2) then
    [[(vEdge v (v.1 + 1, v.2), false), (vEdge v (v.1, v.2 + 1), false),
      (vEdge v (v.1 - 1, v.2), false), (vEdge v (v.1, v.2 - 1), false)]]
  else []

def edgeClauses : List Clause :=
  (cells I).flatMap fun v => edgeAt I v (v.1 + 1, v.2) ++ edgeAt I v (v.1, v.2 + 1) ++ degAt I v

/-- Distance 0: only `p` itself. -/
def initClauses (p : Cell) : List Clause :=
  (cells I).flatMap fun v =>
    if v = p then [[(vGrid p 0 v, true)]]
    else [[(vGrid p 0 v, false)], [(vNet p 0 v, false)]]

/-- One step of the two reachability recurrences at cell `v`, time `t`. -/
def stepClauses (p : Cell) (t : ℕ) (v : Cell) : List Clause :=
  [(vGrid p (t + 1) v, false) :: (vGrid p t v, true) ::
      (stepsG I p v).map fun u => (vGrid p t u, true),
   [(vGrid p t v, false), (vGrid p (t + 1) v, true)]] ++
  ((stepsG I p v).map fun u => [(vGrid p t u, false), (vGrid p (t + 1) v, true)]) ++
  [(vNet p (t + 1) v, false) :: (vNet p t v, true) ::
      (stepsN I p v).map fun u => (vStep p t v u, true)] ++
  ((stepsN I p v).flatMap fun u =>
    [[(vStep p t v u, false), (vNet p t u, true)],
     [(vStep p t v u, false), (vEdge u v, true)]])

def reachClauses (p : Cell) : List Clause :=
  (List.range (I.W * I.H)).flatMap fun t => (cells I).flatMap fun v => stepClauses I p t v

/-- Chosen cities are reachable in the grid and in the network. -/
def finClauses (p : Cell) : List Clause :=
  (cityL I).flatMap fun c =>
    [[(vSel p c, false), (vGrid p (I.W * I.H) c, true)],
     [(vSel p c, false), (vNet p (I.W * I.H) c, true)]]

/-- No chosen city is farther than an unchosen one. -/
def nearClauses (p : Cell) : List Clause :=
  (cityL I).flatMap fun c => (cityL I).flatMap fun c2 =>
    (List.range (I.W * I.H + 1)).map fun t =>
      [(vSel p c, false), (vSel p c2, true), (vGrid p t c2, false), (vGrid p t c, true)]

def selItems (p : Cell) (b : Bool) : List (List Lit) := (cityL I).map fun c => [(vSel p c, b)]

/-- Exactly `k` cities are chosen. -/
def cardClauses (p : Cell) : List Clause :=
  atMost (vCount (Nat.pair 0 (cellCode p))) I.k (selItems I p true) ++
  atMost (vCount (Nat.pair 1 (cellCode p))) ((cityL I).length - I.k) (selItems I p false)

def portClauses (p : Cell) : List Clause :=
  initClauses I p ++ reachClauses I p ++ finClauses I p ++ nearClauses I p ++ cardClauses I p

/-- One item per unit of excess: `(p, c, t)` with `gridDist ≤ t < netDist`. -/
def excessItems : List (List Lit) :=
  (portL I).flatMap fun p => (cityL I).flatMap fun c =>
    (List.range (I.W * I.H)).map fun t =>
      [(vSel p c, true), (vGrid p t c, true), (vNet p t c, false)]

def tileItems : List (List Lit) := (cells I).map fun x => [(vTile x, true)]

/-- The formula. -/
def enc (X K : ℕ) : List Clause :=
  edgeClauses I ++ (portL I).flatMap (portClauses I) ++
  atMost (vCount (Nat.pair 2 0)) X (excessItems I) ++
  atMost (vCount (Nat.pair 3 0)) K (tileItems I)

/-! ### Meaning of the clause families -/

variable (a : ℕ → Bool)

theorem cTrue_map_pos {α : Type} (l : List α) (f : α → ℕ) :
    CTrue a (l.map fun u => (f u, true)) ↔ ∃ u ∈ l, a (f u) = true := by
  simp [CTrue, LTrue]

theorem sat_map {α : Type} (l : List α) (f : α → Clause) :
    Sat a (l.map f) ↔ ∀ u ∈ l, CTrue a (f u) := by
  simp [Sat]

theorem sat_edgeAt (v u : Cell) :
    Sat a (edgeAt I v u) ↔
      (¬(I.IsOpen v ∧ I.IsOpen u) → a (vEdge v u) = false) ∧
      (I.IsOpen v → I.IsOpen u → a (vEdge v u) = true →
        (I.IsFree v → a (vTile v) = true) ∧ (I.IsFree u → a (vTile u) = true)) := by
  unfold edgeAt
  rw [sat_ite, sat_append, sat_ite, sat_ite]
  simp only [Bool.and_eq_true, isOpenB_iff, isFreeB_iff, sat_cons, sat_nil, cTrue_cons,
    cTrue_nil, lTrue_neg, lTrue_pos, or_false, and_true, implies_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun hv hu he => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · rcases (h1 ⟨hv, hu⟩).1 hf with h | h
      · rw [he] at h; exact absurd h (by simp)
      · exact h
    · rcases (h1 ⟨hv, hu⟩).2 hf with h | h
      · rw [he] at h; exact absurd h (by simp)
      · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun ⟨hv, hu⟩ => ⟨fun hf => ?_, fun hf => ?_⟩, h1⟩
    · cases he : a (vEdge v u)
      · exact Or.inl rfl
      · exact Or.inr ((h2 hv hu he).1 hf)
    · cases he : a (vEdge v u)
      · exact Or.inl rfl
      · exact Or.inr ((h2 hv hu he).2 hf)

theorem sat_degAt (v : Cell) :
    Sat a (degAt I v) ↔
      (I.IsFree v → 1 ≤ v.1 → 1 ≤ v.2 →
        a (vEdge v (v.1 + 1, v.2)) = false ∨ a (vEdge v (v.1, v.2 + 1)) = false ∨
        a (vEdge v (v.1 - 1, v.2)) = false ∨ a (vEdge v (v.1, v.2 - 1)) = false) := by
  unfold degAt
  rw [sat_ite]
  simp only [Bool.and_eq_true, isFreeB_iff, decide_eq_true_eq, sat_cons, sat_nil, cTrue_cons,
    cTrue_nil, lTrue_neg, or_false, and_true, implies_true, and_imp]

theorem sat_initClauses (p : Cell) :
    Sat a (initClauses I p) ↔
      ∀ v ∈ cells I, (v = p → a (vGrid p 0 v) = true) ∧
        (v ≠ p → a (vGrid p 0 v) = false ∧ a (vNet p 0 v) = false) := by
  unfold initClauses
  rw [sat_flatMap]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [sat_ite]
  simp

theorem sat_stepClauses (p : Cell) (t : ℕ) (v : Cell) :
    Sat a (stepClauses I p t v) ↔
      ((a (vGrid p (t + 1) v) = true ↔
          a (vGrid p t v) = true ∨ ∃ u ∈ stepsG I p v, a (vGrid p t u) = true) ∧
       (a (vNet p (t + 1) v) = true →
          a (vNet p t v) = true ∨ ∃ u ∈ stepsN I p v, a (vStep p t v u) = true) ∧
       (∀ u ∈ stepsN I p v, a (vStep p t v u) = true →
          a (vNet p t u) = true ∧ a (vEdge u v) = true)) := by
  unfold stepClauses
  simp only [sat_append, sat_cons, sat_nil, sat_map, sat_flatMap, cTrue_cons, cTrue_nil,
    cTrue_map_pos, lTrue_neg, lTrue_pos, or_false, and_true]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨fun hg => ?_, ?_⟩, fun hn => ?_, fun u hu hs => ?_⟩
    · rcases h1 with h | h
      · rw [hg] at h; exact absurd h (by simp)
      · exact h
    · rintro (hg | ⟨u, hu, hg⟩)
      · rcases h2 with h | h
        · rw [hg] at h; exact absurd h (by simp)
        · exact h
      · rcases h3 u hu with h | h
        · rw [hg] at h; exact absurd h (by simp)
        · exact h
    · rcases h4 with h | h
      · rw [hn] at h; exact absurd h (by simp)
      · exact h
    · obtain ⟨h51, h52⟩ := h5 u hu
      constructor
      · rcases h51 with h | h
        · rw [hs] at h; exact absurd h (by simp)
        · exact h
      · rcases h52 with h | h
        · rw [hs] at h; exact absurd h (by simp)
        · exact h
  · rintro ⟨hg, hn, hs⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, fun u hu => ?_⟩, ?_⟩, fun u hu => ⟨?_, ?_⟩⟩
    · cases h : a (vGrid p (t + 1) v)
      · exact Or.inl rfl
      · exact Or.inr (hg.mp h)
    · cases h : a (vGrid p t v)
      · exact Or.inl rfl
      · exact Or.inr (hg.mpr (Or.inl h))
    · cases h : a (vGrid p t u)
      · exact Or.inl rfl
      · exact Or.inr (hg.mpr (Or.inr ⟨u, hu, h⟩))
    · cases h : a (vNet p (t + 1) v)
      · exact Or.inl rfl
      · exact Or.inr (hn h)
    · cases h : a (vStep p t v u)
      · exact Or.inl rfl
      · exact Or.inr (hs u hu h).1
    · cases h : a (vStep p t v u)
      · exact Or.inl rfl
      · exact Or.inr (hs u hu h).2

theorem sat_reachClauses (p : Cell) :
    Sat a (reachClauses I p) ↔
      ∀ t, t < I.W * I.H → ∀ v ∈ cells I, Sat a (stepClauses I p t v) := by
  unfold reachClauses
  simp only [sat_flatMap, List.mem_range]

theorem sat_finClauses (p : Cell) :
    Sat a (finClauses I p) ↔
      ∀ c ∈ cityL I, a (vSel p c) = true →
        a (vGrid p (I.W * I.H) c) = true ∧ a (vNet p (I.W * I.H) c) = true := by
  unfold finClauses
  rw [sat_flatMap]
  refine forall_congr' fun c => imp_congr_right fun _ => ?_
  cases h : a (vSel p c) <;> simp [h]

theorem sat_nearClauses (p : Cell) :
    Sat a (nearClauses I p) ↔
      ∀ c ∈ cityL I, ∀ c2 ∈ cityL I, ∀ t, t ≤ I.W * I.H →
        a (vSel p c) = true → a (vSel p c2) = false → a (vGrid p t c2) = true →
        a (vGrid p t c) = true := by
  unfold nearClauses
  simp only [sat_flatMap, sat_map, List.mem_range, Nat.lt_succ_iff]
  refine forall_congr' fun c => imp_congr_right fun _ => forall_congr' fun c2 =>
    imp_congr_right fun _ => forall_congr' fun t => imp_congr_right fun _ => ?_
  cases h1 : a (vSel p c) <;> cases h2 : a (vSel p c2) <;> cases h3 : a (vGrid p t c2) <;>
    simp [h1, h2, h3]

end TrainNetwork.Answer
