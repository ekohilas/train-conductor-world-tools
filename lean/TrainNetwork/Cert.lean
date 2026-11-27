/-
Distance-label certificates.

A certificate labels every grid cell with four edge bits and, for each port of the
current run, an optional pair `(d, δ)`: "this cell is at network distance at most `d`
from the port, and its predecessor on such a walk is its neighbour in direction `δ`".
All constraints are *local*: they involve one cell (`unaryT`) or two adjacent cells
(`pairT`). The cost of a certificate is a sum of per-cell costs (`cellCostT`).

This file defines labels, cell kinds, the timed check functions, and proves what the
checks mean and how long they take. Soundness and completeness of certificates with
respect to the frozen problem definition are in `Sound.lean` and `Complete.lean`.
-/
import TrainNetwork.Walks
import TrainNetwork.TimeBasic

namespace TrainNetwork

open TimeM

/-! ## Directions and neighbours -/

inductive Dir
  | R | D | L | U
  deriving DecidableEq, Repr

instance : Fintype Dir := ⟨{.R, .D, .L, .U}, by intro x; cases x <;> simp⟩

namespace Dir

def opp : Dir → Dir
  | R => L
  | D => U
  | L => R
  | U => D

@[simp] theorem opp_opp (δ : Dir) : δ.opp.opp = δ := by cases δ <;> rfl

end Dir

/-- `IsNb δ x y`: `y` is the neighbour of `x` in direction `δ`. -/
def IsNb : Dir → Cell → Cell → Prop
  | .R, x, y => y = (x.1 + 1, x.2)
  | .D, x, y => y = (x.1, x.2 + 1)
  | .L, x, y => x = (y.1 + 1, y.2)
  | .U, x, y => x = (y.1, y.2 + 1)

/-- Does `x` have a neighbour in direction `δ` at all (coordinates are naturals)? -/
def hasNb : Dir → Cell → Bool
  | .R, _ => true
  | .D, _ => true
  | .L, x => decide (0 < x.1)
  | .U, x => decide (0 < x.2)

/-- The neighbour of `x` in direction `δ` (meaningful when `hasNb δ x`). -/
def nbOf : Dir → Cell → Cell
  | .R, x => (x.1 + 1, x.2)
  | .D, x => (x.1, x.2 + 1)
  | .L, x => (x.1 - 1, x.2)
  | .U, x => (x.1, x.2 - 1)

theorem isNb_iff {δ : Dir} {x y : Cell} : IsNb δ x y ↔ hasNb δ x = true ∧ y = nbOf δ x := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  cases δ <;> simp only [IsNb, hasNb, nbOf, Prod.mk.injEq, decide_eq_true_eq, true_and] <;> omega

theorem isNb_opp {δ : Dir} {x y : Cell} : IsNb δ.opp y x ↔ IsNb δ x y := by
  cases δ <;> exact Iff.rfl

theorem isNb_unique {δ : Dir} {x y y' : Cell} (h : IsNb δ x y) (h' : IsNb δ x y') : y = y' := by
  rw [isNb_iff] at h h'
  rw [h.2, h'.2]

theorem isNb_dir_unique {δ δ' : Dir} {x y : Cell} (h : IsNb δ x y) (h' : IsNb δ' x y) :
    δ = δ' := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  cases δ <;> cases δ' <;> simp only [IsNb, Prod.mk.injEq] at h h' <;>
    first | rfl | (exfalso; omega)

theorem adjacent_iff_isNb {x y : Cell} : Adjacent x y ↔ ∃ δ, IsNb δ x y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  constructor
  · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩) <;> dsimp only at h1 h2
    · exact ⟨.D, by simp only [IsNb, Prod.mk.injEq]; omega⟩
    · exact ⟨.U, by simp only [IsNb, Prod.mk.injEq]; omega⟩
    · exact ⟨.R, by simp only [IsNb, Prod.mk.injEq]; omega⟩
    · exact ⟨.L, by simp only [IsNb, Prod.mk.injEq]; omega⟩
  · rintro ⟨δ, h⟩
    cases δ <;> simp only [IsNb, Prod.mk.injEq] at h <;> simp only [Adjacent] <;> omega

theorem adjacent_symm {x y : Cell} (h : Adjacent x y) : Adjacent y x := by
  obtain ⟨δ, hδ⟩ := adjacent_iff_isNb.mp h
  exact adjacent_iff_isNb.mpr ⟨δ.opp, isNb_opp.mpr hδ⟩

theorem Instance.GridAdj.symm {I : Instance} {x y : Cell} (h : I.GridAdj x y) : I.GridAdj y x :=
  ⟨adjacent_symm h.1, h.2.2, h.2.1⟩

theorem Solution.NetAdj.symm {σ : Solution} {x y : Cell} (h : σ.NetAdj x y) : σ.NetAdj y x :=
  Or.symm h

theorem Solution.mem_neighbours {σ : Solution} {x y : Cell} :
    y ∈ σ.neighbours x ↔ σ.NetAdj x y := by
  unfold Solution.neighbours Solution.NetAdj
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · rw [Finset.mem_filter] at he
      obtain ⟨he, rfl⟩ := he
      exact Or.inl he
    · rw [Finset.mem_filter] at he
      obtain ⟨he, rfl⟩ := he
      exact Or.inr he
  · rintro (h | h)
    · exact Or.inl ⟨(x, y), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨(y, x), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

/-! ## Labels and kinds -/

/-- A port entry of a label: `none`, or `(d, δ)` = distance bound and predecessor
direction. -/
abbrev DEntry := Option (ℕ × Dir)

/-- The label of one cell. -/
structure Lab where
  eR : Bool
  eD : Bool
  eL : Bool
  eU : Bool
  ds : List DEntry

instance : Inhabited Lab := ⟨⟨false, false, false, false, []⟩⟩

namespace Lab

/-- Edge bit in direction `δ`. -/
def edge (a : Lab) : Dir → Bool
  | .R => a.eR
  | .D => a.eD
  | .L => a.eL
  | .U => a.eU

/-- Number of set edge bits. -/
def deg (a : Lab) : ℕ := a.eR.toNat + a.eD.toNat + a.eL.toNat + a.eU.toNat

/-- Is some edge bit set? -/
def any (a : Lab) : Bool := a.eR || a.eD || a.eL || a.eU

/-- Entry for port index `j` (`none` beyond the end of the list). -/
def d (a : Lab) (j : ℕ) : DEntry := a.ds.getD j none

theorem any_iff (a : Lab) : a.any = true ↔ ∃ δ, a.edge δ = true := by
  constructor
  · intro h
    simp only [any, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact ⟨.R, h⟩
    · exact ⟨.D, h⟩
    · exact ⟨.L, h⟩
    · exact ⟨.U, h⟩
  · rintro ⟨δ, h⟩
    cases δ <;> simp only [edge] at h <;> simp [any, h]

theorem deg_eq_card (a : Lab) :
    a.deg = (Finset.univ.filter (fun δ : Dir => a.edge δ = true)).card := by
  obtain ⟨eR, eD, eL, eU, ds⟩ := a
  cases eR <;> cases eD <;> cases eL <;> cases eU <;> rfl

end Lab

/-- What a cell is, from the point of view of port index `j`. -/
structure PKind where
  /-- the cell is port `j` itself -/
  src : Bool
  /-- walks from port `j` may pass through the cell (it is free, or it is port `j`) -/
  transit : Bool
  /-- `some g`: the cell is a city chosen for port `j`, at grid distance `g` -/
  dem : Option ℕ

instance : Inhabited PKind := ⟨⟨false, false, none⟩⟩

/-- Everything the checks need to know about a cell. -/
structure Kind where
  free : Bool
  aR : Bool
  aD : Bool
  aL : Bool
  aU : Bool
  pp : List PKind

instance : Inhabited Kind := ⟨⟨false, false, false, false, false, []⟩⟩

namespace Kind

/-- May the cell have a network edge in direction `δ`? -/
def allow (k : Kind) : Dir → Bool
  | .R => k.aR
  | .D => k.aD
  | .L => k.aL
  | .U => k.aU

/-- Port data for port index `j`. -/
def p (k : Kind) (j : ℕ) : PKind := k.pp.getD j default

end Kind

/-! ## The local checks -/

/-- Unary condition on the entry of one port. -/
def entryOK (a : Lab) (pk : PKind) (en : DEntry) : Bool :=
  (match en with
    | none => !pk.src
    | some (d, δ) => if pk.src then d == 0 else (a.edge δ && decide (1 ≤ d))) &&
  (pk.dem.isNone || en.isSome)

/-- Unary condition on the entries of ports `0, …, q-1`. -/
def entriesT (k : Kind) (a : Lab) : ℕ → TimeM Bool
  | 0 => pure true
  | j + 1 => do
      -- two list accesses at index `j`, two comparisons of distances, bookkeeping
      tickN (2 * j + 6)
      let r ← entriesT k a j
      pure (entryOK a (k.p j) (a.d j) && r)

theorem entriesT_val (k : Kind) (a : Lab) (q : ℕ) :
    (entriesT k a q).val = true ↔ ∀ j, j < q → entryOK a (k.p j) (a.d j) = true := by
  induction q with
  | zero => simp [entriesT]
  | succ q ih =>
      simp only [entriesT, bind_val, pure_val, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h2 j h
        · exact h1
      · intro h
        exact ⟨h q (Nat.lt_succ_self q), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

theorem entriesT_time (k : Kind) (a : Lab) (q : ℕ) :
    (entriesT k a q).time ≤ q * (2 * q + 6) := by
  induction q with
  | zero => simp [entriesT]
  | succ q ih =>
      simp only [entriesT, bind_time, tickN_time, pure_time]
      nlinarith

/-- All unary conditions of a cell: edges only where allowed, degree cap `β` on free
cells, and the port entries. -/
def unaryT (β : ℕ) (k : Kind) (a : Lab) : TimeM Bool := do
  -- length of `k.pp`, three additions and one comparison for the degree, bookkeeping
  tickN (k.pp.length + 8)
  let r ← entriesT k a k.pp.length
  pure ((!a.eR || k.aR) && (!a.eD || k.aD) && (!a.eL || k.aL) && (!a.eU || k.aU) &&
        (!k.free || decide (a.deg ≤ β)) && r)

/-- Meaning of `unaryT`. -/
structure UnaryOK (β : ℕ) (k : Kind) (a : Lab) : Prop where
  mask : ∀ δ, a.edge δ = true → k.allow δ = true
  deg : k.free = true → a.deg ≤ β
  entries : ∀ j, j < k.pp.length → entryOK a (k.p j) (a.d j) = true

theorem unaryT_val (β : ℕ) (k : Kind) (a : Lab) :
    (unaryT β k a).val = true ↔ UnaryOK β k a := by
  simp only [unaryT, bind_val, pure_val, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, entriesT_val]
  constructor
  · rintro ⟨⟨⟨⟨⟨hR, hD⟩, hL⟩, hU⟩, hdeg⟩, hen⟩
    refine ⟨?_, ?_, hen⟩
    · intro δ hδ
      cases δ <;> simp only [Lab.edge] at hδ <;> simp only [Kind.allow]
      · rcases hR with h | h
        · rw [h] at hδ; exact absurd hδ (by simp)
        · exact h
      · rcases hD with h | h
        · rw [h] at hδ; exact absurd hδ (by simp)
        · exact h
      · rcases hL with h | h
        · rw [h] at hδ; exact absurd hδ (by simp)
        · exact h
      · rcases hU with h | h
        · rw [h] at hδ; exact absurd hδ (by simp)
        · exact h
    · intro hf
      rcases hdeg with h | h
      · rw [h] at hf; exact absurd hf (by simp)
      · exact h
  · rintro ⟨hmask, hdeg, hen⟩
    have key : ∀ δ, a.edge δ = false ∨ k.allow δ = true := by
      intro δ
      cases h : a.edge δ
      · exact Or.inl rfl
      · exact Or.inr (hmask δ h)
    refine ⟨⟨⟨⟨⟨key .R, key .D⟩, key .L⟩, key .U⟩, ?_⟩, hen⟩
    cases h : k.free
    · exact Or.inl rfl
    · exact Or.inr (hdeg h)

theorem unaryT_time (β : ℕ) (k : Kind) (a : Lab) :
    (unaryT β k a).time ≤ k.pp.length + 8 + k.pp.length * (2 * k.pp.length + 6) := by
  have := entriesT_time k a k.pp.length
  simp only [unaryT, bind_time, tickN_time, pure_time]
  omega

/-- Predecessor condition: if the entry `ea` of cell `a` names direction `δ` and `a` is
not the port itself, then the neighbour `b` in that direction must be passable and carry
the entry `d - 1`. -/
def predOK (δ : Dir) (pa : PKind) (ea : DEntry) (pb : PKind) (eb : DEntry) : Bool :=
  match ea with
  | some (d, δ') =>
      if δ' = δ ∧ pa.src = false then
        pb.transit && (match eb with
          | some (d', _) => d' + 1 == d
          | none => false)
      else true
  | none => true

/-- Both predecessor conditions between `a` and its `δ`-neighbour `b`, for port `j`. -/
def predAt (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) (j : ℕ) : Bool :=
  predOK δ (ka.p j) (a.d j) (kb.p j) (b.d j) && predOK δ.opp (kb.p j) (b.d j) (ka.p j) (a.d j)

def predsT (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) : ℕ → TimeM Bool
  | 0 => pure true
  | j + 1 => do
      -- four list accesses at index `j`, two additions, two comparisons, bookkeeping
      tickN (4 * j + 10)
      let r ← predsT δ ka a kb b j
      pure (predAt δ ka a kb b j && r)

theorem predsT_val (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) (q : ℕ) :
    (predsT δ ka a kb b q).val = true ↔ ∀ j, j < q → predAt δ ka a kb b j = true := by
  induction q with
  | zero => simp [predsT]
  | succ q ih =>
      simp only [predsT, bind_val, pure_val, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h2 j h
        · exact h1
      · intro h
        exact ⟨h q (Nat.lt_succ_self q), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

theorem predsT_time (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) (q : ℕ) :
    (predsT δ ka a kb b q).time ≤ q * (4 * q + 10) := by
  induction q with
  | zero => simp [predsT]
  | succ q ih =>
      simp only [predsT, bind_time, tickN_time, pure_time]
      nlinarith

/-- All conditions between a cell `a` and its neighbour `b` in direction `δ`: the two
edge bits agree, and the predecessor conditions hold for every port. -/
def pairT (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) : TimeM Bool := do
  tickN (ka.pp.length + 2)
  let r ← predsT δ ka a kb b ka.pp.length
  pure ((a.edge δ == b.edge δ.opp) && r)

/-- Meaning of `pairT`. -/
structure PairOK (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) : Prop where
  edge : a.edge δ = b.edge δ.opp
  preds : ∀ j, j < ka.pp.length → predAt δ ka a kb b j = true

theorem pairT_val (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) :
    (pairT δ ka a kb b).val = true ↔ PairOK δ ka a kb b := by
  simp only [pairT, bind_val, pure_val, Bool.and_eq_true, beq_iff_eq, predsT_val]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.edge, h.preds⟩⟩

theorem pairT_time (δ : Dir) (ka : Kind) (a : Lab) (kb : Kind) (b : Lab) :
    (pairT δ ka a kb b).time ≤ ka.pp.length + 2 + ka.pp.length * (4 * ka.pp.length + 10) := by
  have := predsT_time δ ka a kb b ka.pp.length
  simp only [pairT, bind_time, tickN_time, pure_time]
  omega

/-- Certified excess of port `j` at a cell: `d - g` if the cell is a chosen city of the
port (at grid distance `g`) and its entry is `(d, _)`. -/
def excAt (k : Kind) (a : Lab) (j : ℕ) : ℕ :=
  match (k.p j).dem, a.d j with
  | some g, some (d, _) => d - g
  | _, _ => 0

def excT (k : Kind) (a : Lab) : ℕ → TimeM ℕ
  | 0 => pure 0
  | j + 1 => do
      -- two list accesses at index `j`, one subtraction, one addition, bookkeeping
      tickN (2 * j + 6)
      let r ← excT k a j
      pure (excAt k a j + r)

theorem excT_val (k : Kind) (a : Lab) (q : ℕ) :
    (excT k a q).val = ∑ j ∈ Finset.range q, excAt k a j := by
  induction q with
  | zero => simp [excT]
  | succ q ih =>
      simp only [excT, bind_val, pure_val, ih, Finset.sum_range_succ]
      omega

theorem excT_time (k : Kind) (a : Lab) (q : ℕ) : (excT k a q).time ≤ q * (2 * q + 6) := by
  induction q with
  | zero => simp [excT]
  | succ q ih =>
      simp only [excT, bind_time, tickN_time, pure_time]
      nlinarith

/-- Is the cell a track tile of the certificate? -/
def tileAt (k : Kind) (a : Lab) : ℕ := if k.free && a.any then 1 else 0

/-- Cost of a cell: `excess · M + tile`. -/
def cellCostT (M : ℕ) (k : Kind) (a : Lab) : TimeM ℕ := do
  -- length of `k.pp`, one multiplication, one addition, bookkeeping
  tickN (k.pp.length + 4)
  let e ← excT k a k.pp.length
  pure (e * M + tileAt k a)

theorem cellCostT_val (M : ℕ) (k : Kind) (a : Lab) :
    (cellCostT M k a).val = (∑ j ∈ Finset.range k.pp.length, excAt k a j) * M + tileAt k a := by
  simp [cellCostT, excT_val]

theorem cellCostT_time (M : ℕ) (k : Kind) (a : Lab) :
    (cellCostT M k a).time ≤ k.pp.length + 4 + k.pp.length * (2 * k.pp.length + 6) := by
  have := excT_time k a k.pp.length
  simp only [cellCostT, bind_time, tickN_time, pure_time]
  omega

/-- A common bound for the running time of `unaryT`, `pairT` and `cellCostT` on cells
with at most `q` ports. -/
def cellBound (q : ℕ) : ℕ := 7 * (q + 2) * (q + 2)

theorem unaryT_time_le {β : ℕ} {k : Kind} {a : Lab} {q : ℕ} (h : k.pp.length ≤ q) :
    (unaryT β k a).time ≤ cellBound q := by
  have h1 := unaryT_time β k a
  have h2 : k.pp.length * (2 * k.pp.length + 6) ≤ q * (2 * q + 6) :=
    Nat.mul_le_mul h (by omega)
  simp only [cellBound]
  nlinarith

theorem pairT_time_le {δ : Dir} {ka : Kind} {a : Lab} {kb : Kind} {b : Lab} {q : ℕ}
    (h : ka.pp.length ≤ q) : (pairT δ ka a kb b).time ≤ cellBound q := by
  have h1 := pairT_time δ ka a kb b
  have h2 : ka.pp.length * (4 * ka.pp.length + 10) ≤ q * (4 * q + 10) :=
    Nat.mul_le_mul h (by omega)
  simp only [cellBound]
  nlinarith

theorem cellCostT_time_le {M : ℕ} {k : Kind} {a : Lab} {q : ℕ} (h : k.pp.length ≤ q) :
    (cellCostT M k a).time ≤ cellBound q := by
  have h1 := cellCostT_time M k a
  have h2 : k.pp.length * (2 * k.pp.length + 6) ≤ q * (2 * q + 6) :=
    Nat.mul_le_mul h (by omega)
  simp only [cellBound]
  nlinarith

/-! ## Kinds of the cells of an instance -/

/-- The ports of a run with their demands: port cell, and the cities chosen for it
together with their grid distance. -/
abbrev PD := List (Cell × List (Cell × ℕ))

instance (I : Instance) (x : Cell) : Decidable (I.IsOpen x) := by
  unfold Instance.IsOpen Instance.InBounds; infer_instance

instance (I : Instance) (x : Cell) : Decidable (I.IsFree x) := by
  unfold Instance.IsFree Instance.InBounds Instance.IsTerminal; infer_instance

/-- An upper bound on the number of primitive steps of one `IsOpen`/`IsFree` test: two
coordinate comparisons, and a linear scan of each of the three finite sets (two `ℕ`
comparisons per element). -/
def scanCost (I : Instance) : ℕ := 2 * (I.blocked.card + I.ports.card + I.cities.card) + 4

/-- Per-port data of cell `x`, where `fr` says whether `x` is free. -/
def pkOf (fr : Bool) (x : Cell) (e : Cell × List (Cell × ℕ)) : PKind :=
  ⟨decide (x = e.1), fr || decide (x = e.1), (tlookup x e.2).val⟩

def ppT (fr : Bool) (x : Cell) : PD → TimeM (List PKind)
  | [] => pure []
  | (p, dl) :: pd => do
      -- two coordinate comparisons, one allocation, bookkeeping
      tickN 4
      let g ← tlookup x dl
      let rest ← ppT fr x pd
      pure (⟨decide (x = p), fr || decide (x = p), g⟩ :: rest)

theorem ppT_val (fr : Bool) (x : Cell) (pd : PD) : (ppT fr x pd).val = pd.map (pkOf fr x) := by
  induction pd with
  | nil => rfl
  | cons e pd ih =>
      obtain ⟨p, dl⟩ := e
      simp [ppT, ih, pkOf]

theorem ppT_time (fr : Bool) (x : Cell) (pd : PD) (c : ℕ)
    (h : ∀ e ∈ pd, e.2.length ≤ c) : (ppT fr x pd).time ≤ pd.length * (3 * c + 4) := by
  induction pd with
  | nil => simp [ppT]
  | cons e pd ih =>
      obtain ⟨p, dl⟩ := e
      have h1 : dl.length ≤ c := h (p, dl) (by simp)
      have h2 := ih (fun e he => h e (List.mem_cons_of_mem _ he))
      have h3 := tlookup_time_le x dl
      simp only [ppT, bind_time, tickN_time, pure_time, List.length_cons]
      nlinarith

/-- May cell `x` have a network edge in direction `δ`: the neighbour exists and both
cells are open. -/
def allowOf (I : Instance) (x : Cell) (δ : Dir) : Bool :=
  decide (I.IsOpen x) && hasNb δ x && decide (I.IsOpen (nbOf δ x))

/-- The kind of cell `x` in the run with port data `pd`. -/
def kindT (I : Instance) (pd : PD) (x : Cell) : TimeM Kind := do
  -- six open/free tests, four neighbour coordinates and boundary tests, bookkeeping
  tickN (6 * scanCost I + 16)
  let pp ← ppT (decide (I.IsFree x)) x pd
  pure { free := decide (I.IsFree x)
         aR := allowOf I x .R
         aD := allowOf I x .D
         aL := allowOf I x .L
         aU := allowOf I x .U
         pp := pp }

/-- The kind of a cell (the value computed by `kindT`). -/
def kindOf (I : Instance) (pd : PD) (x : Cell) : Kind := (kindT I pd x).val

theorem kindOf_free (I : Instance) (pd : PD) (x : Cell) :
    (kindOf I pd x).free = true ↔ I.IsFree x := by
  simp [kindOf, kindT]

theorem kindOf_pp (I : Instance) (pd : PD) (x : Cell) :
    (kindOf I pd x).pp = pd.map (pkOf (decide (I.IsFree x)) x) := by
  simp [kindOf, kindT, ppT_val]

theorem kindOf_pp_length (I : Instance) (pd : PD) (x : Cell) :
    (kindOf I pd x).pp.length = pd.length := by
  simp [kindOf_pp]

theorem kindOf_p (I : Instance) (pd : PD) (x : Cell) {j : ℕ} {e : Cell × List (Cell × ℕ)}
    (h : pd[j]? = some e) : (kindOf I pd x).p j = pkOf (decide (I.IsFree x)) x e := by
  simp [Kind.p, kindOf_pp, List.getD_eq_getElem?_getD, h]

theorem kindOf_allow (I : Instance) (pd : PD) (x : Cell) (δ : Dir) :
    (kindOf I pd x).allow δ = true ↔ ∃ y, IsNb δ x y ∧ I.GridAdj x y := by
  have h0 : (kindOf I pd x).allow δ = allowOf I x δ := by
    cases δ <;> rfl
  rw [h0]
  simp only [allowOf, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨ho, hnb⟩, ho'⟩
    have hnb' : IsNb δ x (nbOf δ x) := isNb_iff.mpr ⟨hnb, rfl⟩
    exact ⟨nbOf δ x, hnb', adjacent_iff_isNb.mpr ⟨δ, hnb'⟩, ho, ho'⟩
  · rintro ⟨y, hnb, -, ho, ho'⟩
    obtain ⟨h1, rfl⟩ := isNb_iff.mp hnb
    exact ⟨⟨ho, h1⟩, ho'⟩

theorem kindT_time (I : Instance) (pd : PD) (x : Cell) (c : ℕ)
    (h : ∀ e ∈ pd, e.2.length ≤ c) :
    (kindT I pd x).time ≤ 6 * scanCost I + 16 + pd.length * (3 * c + 4) := by
  have := ppT_time (decide (I.IsFree x)) x pd c h
  simp only [kindT, bind_time, tickN_time, pure_time]
  omega

end TrainNetwork
