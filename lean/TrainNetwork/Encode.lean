/-
The CNF encoding of the decision problem: variable numbering, the executable tests on
cells, and the lists the encoding ranges over.
-/
import TrainNetwork.Sat
import TrainNetwork.Reach

namespace TrainNetwork.Answer

open TrainNetwork

/-! ### Variable numbering -/

/-- Code of a cell. -/
def cellCode (c : Cell) : ℕ := Nat.pair c.1 c.2

/-- Inverse of `cellCode`. -/
def cellOf (n : ℕ) : Cell := n.unpair

@[simp] theorem cellOf_cellCode (c : Cell) : cellOf (cellCode c) = c := by
  simp [cellOf, cellCode]

theorem cellCode_inj {u v : Cell} : cellCode u = cellCode v ↔ u = v := by
  constructor
  · intro h
    have := congrArg cellOf h
    simpa using this
  · rintro rfl; rfl

/-- "The network has an edge between `u` and `v`" (symmetric in `u`, `v`). -/
def vEdge (u v : Cell) : ℕ :=
  Nat.pair 0 (Nat.pair (min (cellCode u) (cellCode v)) (max (cellCode u) (cellCode v)))

/-- "Port `p` chooses city `c`." -/
def vSel (p c : Cell) : ℕ := Nat.pair 1 (Nat.pair (cellCode p) (cellCode c))

/-- "`gridDist p v ≤ t`." -/
def vGrid (p : Cell) (t : ℕ) (v : Cell) : ℕ :=
  Nat.pair 2 (Nat.pair (cellCode p) (Nat.pair t (cellCode v)))

/-- "`netDist p v ≤ t`." -/
def vNet (p : Cell) (t : ℕ) (v : Cell) : ℕ :=
  Nat.pair 3 (Nat.pair (cellCode p) (Nat.pair t (cellCode v)))

/-- "`v` is reached from `p` within `t + 1` network steps, the last one from `u`." -/
def vStep (p : Cell) (t : ℕ) (v u : Cell) : ℕ :=
  Nat.pair 4 (Nat.pair (cellCode p) (Nat.pair t (Nat.pair (cellCode v) (cellCode u))))

/-- "`x` is a track tile." -/
def vTile (x : Cell) : ℕ := Nat.pair 5 (cellCode x)

/-- Counter variable `(i, j)` of the cardinality gadget number `tag`. -/
def vCount (tag i j : ℕ) : ℕ := Nat.pair 6 (Nat.pair tag (Nat.pair i j))

theorem vEdge_comm (u v : Cell) : vEdge u v = vEdge v u := by
  simp [vEdge, min_comm, max_comm]

/-! ### Executable tests on cells -/

variable (I : Instance)

/-- `IsOpen` as a Boolean test: two comparisons and one set lookup. -/
def isOpenB (c : Cell) : Bool :=
  decide (c.1 < I.W) && decide (c.2 < I.H) && !decide (c ∈ I.blocked)

/-- `IsFree` as a Boolean test. -/
def isFreeB (c : Cell) : Bool :=
  isOpenB I c && !decide (c ∈ I.ports) && !decide (c ∈ I.cities)

theorem isOpenB_iff (c : Cell) : isOpenB I c = true ↔ I.IsOpen c := by
  simp [isOpenB, Instance.IsOpen, Instance.InBounds, and_assoc]

theorem isFreeB_iff (c : Cell) : isFreeB I c = true ↔ I.IsFree c := by
  simp [isFreeB, isOpenB, Instance.IsFree, Instance.IsTerminal, Instance.InBounds, and_assoc]

theorem IsFree.isOpen {c : Cell} (h : I.IsFree c) : I.IsOpen c := ⟨h.1, h.2.1⟩

/-! ### Lists the encoding ranges over -/

/-- All cells of the grid. -/
def cells : List Cell := (List.range I.W) ×ˢ (List.range I.H)

theorem mem_cells (c : Cell) : c ∈ cells I ↔ I.InBounds c := by
  obtain ⟨x, y⟩ := c
  simp [cells, Instance.InBounds]

theorem nodup_cells : (cells I).Nodup :=
  List.Nodup.product List.nodup_range List.nodup_range

/-- The ports, as a list. -/
def portL : List Cell := (cells I).filter fun c => decide (c ∈ I.ports)

/-- The cities, as a list. -/
def cityL : List Cell := (cells I).filter fun c => decide (c ∈ I.cities)

theorem mem_portL (c : Cell) : c ∈ portL I ↔ c ∈ I.ports := by
  simp only [portL, List.mem_filter, mem_cells, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨I.ports_inBounds c h, h⟩⟩

theorem mem_cityL (c : Cell) : c ∈ cityL I ↔ c ∈ I.cities := by
  simp only [cityL, List.mem_filter, mem_cells, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨I.cities_inBounds c h, h⟩⟩

theorem nodup_portL : (portL I).Nodup := (nodup_cells I).filter _
theorem nodup_cityL : (cityL I).Nodup := (nodup_cells I).filter _

theorem cityL_toFinset : (cityL I).toFinset = I.cities := by
  ext c; simp [mem_cityL]

theorem portL_toFinset : (portL I).toFinset = I.ports := by
  ext c; simp [mem_portL]

theorem cityL_length : (cityL I).length = I.cities.card := by
  rw [← cityL_toFinset, List.toFinset_card_of_nodup (nodup_cityL I)]

/-- The (at most four) grid neighbours of a cell. -/
def nbrs (v : Cell) : List Cell :=
  (v.1 + 1, v.2) :: (v.1, v.2 + 1) ::
    ((if 1 ≤ v.1 then [(v.1 - 1, v.2)] else []) ++ (if 1 ≤ v.2 then [(v.1, v.2 - 1)] else []))

theorem mem_nbrs {u v : Cell} : u ∈ nbrs v ↔ Adjacent u v := by
  obtain ⟨x, y⟩ := u
  obtain ⟨x', y'⟩ := v
  simp only [nbrs, List.mem_cons, List.mem_append, Prod.mk.injEq, Adjacent]
  split_ifs <;> simp <;> omega

theorem adjacent_comm {u v : Cell} : Adjacent u v ↔ Adjacent v u := by
  unfold Adjacent; constructor <;> intro h <;> omega

end TrainNetwork.Answer
