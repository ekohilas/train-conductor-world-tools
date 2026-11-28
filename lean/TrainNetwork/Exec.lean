/-
Executable (list-based) versions of the definitions in `Problem.lean`, with proofs that
they agree with the frozen noncomputable ones.

* `Instance.isOpenB / isFreeB / gridAdjB` : Boolean tests for `IsOpen / IsFree / GridAdj`.
* `Instance.cellsL / gridEdgesL / portsL / citiesL` : the grid as lists.
* `Instance.gridDistO` : computable `gridDist`.
* `Cand` : a candidate solution given by lists; `Cand.toSolution` reads it as a
  `Solution`.
* `feasB`, `costN` : a Boolean feasibility test and a cost in `ℕ × ℕ`, with
  `feasB_iff` and `cost_eq` relating them to `Solution.Feasible` and `Solution.cost`.

Nothing in this file is timed; the `TimeM` versions live in `Timed.lean`.
-/
import TrainNetwork.Walks

namespace TrainNetwork

instance : DecidableRel Adjacent := fun a b => by
  unfold Adjacent
  infer_instance

namespace Instance

variable (I : Instance)

def isOpenB (c : Cell) : Bool :=
  decide (c.1 < I.W) && decide (c.2 < I.H) && !decide (c ∈ I.blocked)

def isFreeB (c : Cell) : Bool :=
  I.isOpenB c && !decide (c ∈ I.ports) && !decide (c ∈ I.cities)

def gridAdjB (a b : Cell) : Bool :=
  decide (Adjacent a b) && I.isOpenB a && I.isOpenB b

variable {I}

theorem isOpenB_iff {c : Cell} : I.isOpenB c = true ↔ I.IsOpen c := by
  simp [isOpenB, IsOpen, InBounds, and_assoc]

theorem isFreeB_iff {c : Cell} : I.isFreeB c = true ↔ I.IsFree c := by
  simp [isFreeB, isOpenB, IsFree, InBounds, IsTerminal, and_assoc, not_or]

theorem gridAdjB_iff {a b : Cell} : I.gridAdjB a b = true ↔ I.GridAdj a b := by
  simp [gridAdjB, GridAdj, isOpenB_iff, and_assoc]

variable (I)

/-- All in-bounds cells. -/
def cellsL : List Cell :=
  (List.range I.W).flatMap (fun x => (List.range I.H).map (fun y => (x, y)))

/-- The four potential neighbours of a cell (with truncated subtraction; the spurious
ones are removed by the adjacency test in `gridEdgesL`). -/
def nbr4 (a : Cell) : List Cell :=
  [(a.1 + 1, a.2), (a.1 - 1, a.2), (a.1, a.2 + 1), (a.1, a.2 - 1)]

/-- All ordered pairs of grid-adjacent open cells. -/
def gridEdgesL : List (Cell × Cell) :=
  I.cellsL.flatMap (fun a => ((nbr4 a).filter (fun b => I.gridAdjB a b)).map (fun b => (a, b)))

def portsL : List Cell := I.cellsL.filter (fun c => decide (c ∈ I.ports))

def citiesL : List Cell := I.cellsL.filter (fun c => decide (c ∈ I.cities))

variable {I}

theorem mem_cellsL {c : Cell} : c ∈ I.cellsL ↔ I.InBounds c := by
  obtain ⟨x, y⟩ := c
  simp [cellsL, InBounds]

theorem length_cellsL : I.cellsL.length = I.W * I.H := by
  simp [cellsL, List.length_flatMap]

theorem mem_nbr4_of_adjacent {a b : Cell} (h : Adjacent a b) : b ∈ nbr4 a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [Adjacent] at h
  simp only [nbr4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem mem_gridEdgesL {a b : Cell} : (a, b) ∈ I.gridEdgesL ↔ I.GridAdj a b := by
  simp only [gridEdgesL, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨a', -, b', ⟨-, hadj⟩, rfl, rfl⟩
    exact gridAdjB_iff.1 hadj
  · intro h
    exact ⟨a, mem_cellsL.2 h.2.1.1, b, ⟨mem_nbr4_of_adjacent h.1, gridAdjB_iff.2 h⟩, rfl, rfl⟩

theorem adjacent_symm {a b : Cell} (h : Adjacent a b) : Adjacent b a := by
  simp only [Adjacent] at h ⊢
  omega

theorem gridAdj_symm {a b : Cell} (h : I.GridAdj a b) : I.GridAdj b a :=
  ⟨adjacent_symm h.1, h.2.2, h.2.1⟩

theorem gridAdj_eq_listAdj : I.GridAdj = ListAdj I.gridEdgesL := by
  funext a b
  apply propext
  simp only [ListAdj, mem_gridEdgesL]
  exact ⟨Or.inl, fun h => h.elim id gridAdj_symm⟩

theorem length_gridEdgesL_le : I.gridEdgesL.length ≤ 4 * (I.W * I.H) := by
  have h : ∀ l : List Cell, (l.flatMap (fun a =>
      ((nbr4 a).filter (fun b => I.gridAdjB a b)).map (fun b => (a, b)))).length ≤
      4 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      have h4 : ((nbr4 a).filter (fun b => I.gridAdjB a b)).length ≤ 4 :=
        (List.length_filter_le _ _).trans (by simp [nbr4])
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      omega
  have := h I.cellsL
  rwa [length_cellsL] at this

theorem mem_portsL {p : Cell} : p ∈ I.portsL ↔ p ∈ I.ports := by
  simp only [portsL, List.mem_filter, decide_eq_true_eq, mem_cellsL, and_iff_right_iff_imp]
  exact fun h => I.ports_inBounds p h

theorem mem_citiesL {c : Cell} : c ∈ I.citiesL ↔ c ∈ I.cities := by
  simp only [citiesL, List.mem_filter, decide_eq_true_eq, mem_cellsL, and_iff_right_iff_imp]
  exact fun h => I.cities_inBounds c h

theorem nodup_cellsL : I.cellsL.Nodup := by
  unfold cellsL
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · exact List.Nodup.map (fun a b h => (Prod.mk.inj h).2) List.nodup_range
  · refine List.Nodup.pairwise_of_forall_ne List.nodup_range ?_
    intro x _ x' _ hne
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range, not_exists,
      not_and, forall_exists_index, and_imp]
    rintro c y - rfl y' - h
    exact hne (Prod.mk.inj h).1.symm

theorem nodup_portsL : I.portsL.Nodup := nodup_cellsL.filter _

theorem toFinset_portsL : I.portsL.toFinset = I.ports := by
  ext p
  simp [mem_portsL]

theorem length_portsL : I.portsL.length = I.ports.card := by
  rw [← toFinset_portsL, List.toFinset_card_of_nodup nodup_portsL]

theorem nodup_citiesL : I.citiesL.Nodup := nodup_cellsL.filter _

theorem length_citiesL : I.citiesL.length = I.cities.card := by
  have : I.citiesL.toFinset = I.cities := by
    ext p
    simp [mem_citiesL]
  rw [← this, List.toFinset_card_of_nodup nodup_citiesL]

variable (I)

/-- Computable `gridDist`. -/
def gridDistO (s t : Cell) : Option ℕ := netDistO I.isFreeB I.gridEdgesL s t

variable {I}

theorem gridDist_eq (s t : Cell) : I.gridDist s t = optENat (I.gridDistO s t) := by
  unfold gridDist gridDistO
  rw [gridAdj_eq_listAdj]
  exact walkDist_eq_optENat (fun _ => isFreeB_iff) _ _ _

end Instance

/-! ### Candidates -/

/-- A candidate solution in list form: a list of ordered cell pairs, and an association
list giving the chosen cities of each port. -/
structure Cand where
  edges : List (Cell × Cell)
  choice : List (Cell × List Cell)

/-- Association-list lookup; a missing key reads as the empty list. -/
def lookupL (p : Cell) : List (Cell × List Cell) → List Cell
  | [] => []
  | (q, S) :: r => if q = p then S else lookupL p r

namespace Cand

variable (c : Cand)

/-- The cities chosen for port `p`. -/
def sel (p : Cell) : List Cell := lookupL p c.choice

/-- A candidate read as a `Solution`. -/
def toSolution : Solution := ⟨c.edges.toFinset, fun p => (c.sel p).toFinset⟩

theorem netAdj_eq : c.toSolution.NetAdj = ListAdj c.edges := by
  funext a b
  simp [Solution.NetAdj, toSolution, ListAdj]

theorem netDist_eq (I : Instance) (s t : Cell) :
    c.toSolution.netDist I s t = optENat (netDistO I.isFreeB c.edges s t) := by
  unfold Solution.netDist
  rw [netAdj_eq]
  exact walkDist_eq_optENat (fun _ => Instance.isFreeB_iff) _ _ _

end Cand

/-- All endpoints of an edge list (with repetitions). -/
def endsL (E : List (Cell × Cell)) : List Cell := E.map Prod.fst ++ E.map Prod.snd

/-- All network neighbours of `x` (with repetitions). -/
def nbrL (E : List (Cell × Cell)) (x : Cell) : List Cell :=
  (E.filter (fun e => decide (e.1 = x))).map Prod.snd ++
  (E.filter (fun e => decide (e.2 = x))).map Prod.fst

theorem neighbours_eq (c : Cand) (x : Cell) :
    c.toSolution.neighbours x = (nbrL c.edges x).toFinset := by
  ext y
  simp only [Solution.neighbours, Cand.toSolution, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, List.mem_toFinset, nbrL, List.toFinset_append, List.mem_map,
    List.mem_filter, decide_eq_true_eq]

theorem nbrL_eq_nil {E : List (Cell × Cell)} {x : Cell} (h : x ∉ endsL E) : nbrL E x = [] := by
  simp only [endsL, List.mem_append, List.mem_map, not_or, not_exists, not_and] at h
  simp only [nbrL, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  exact ⟨fun e he h1 => h.1 e he h1, fun e he h2 => h.2 e he h2⟩

/-- Degree test: every free endpoint has at most three distinct neighbours. -/
def degOK (I : Instance) (E : List (Cell × Cell)) : Bool :=
  (endsL E).all (fun x => !I.isFreeB x || decide ((nbrL E x).dedup.length ≤ 3))

theorem degOK_iff (I : Instance) (c : Cand) :
    degOK I c.edges = true ↔ ∀ x, I.IsFree x → (c.toSolution.neighbours x).card ≤ 3 := by
  simp only [degOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    neighbours_eq, List.card_toFinset]
  constructor
  · intro h x hx
    by_cases hmem : x ∈ endsL c.edges
    · rcases h x hmem with h1 | h1
      · rw [← Bool.not_eq_true, Instance.isFreeB_iff] at h1
        exact absurd hx h1
      · exact h1
    · simp [nbrL_eq_nil hmem]
  · intro h x _
    by_cases hx : I.IsFree x
    · exact Or.inr (h x hx)
    · left
      rw [← Bool.not_eq_true, Instance.isFreeB_iff]
      exact hx

/-- Number of track tiles. -/
def tilesN (I : Instance) (E : List (Cell × Cell)) : ℕ :=
  ((endsL E).filter I.isFreeB).dedup.length

theorem tiles_card_eq (I : Instance) (c : Cand) :
    (c.toSolution.tiles I).card = tilesN I c.edges := by
  unfold tilesN
  rw [← List.card_toFinset]
  congr 1
  ext x
  simp only [Solution.tiles, Cand.toSolution, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image, List.mem_toFinset, endsL, List.mem_filter, List.mem_append,
    List.mem_map, Instance.isFreeB_iff]

/-- `≤` on `Option ℕ` read as extended naturals. -/
def leO : Option ℕ → Option ℕ → Bool
  | _, none => true
  | none, some _ => false
  | some a, some b => decide (a ≤ b)

theorem leO_iff {a b : Option ℕ} : leO a b = true ↔ optENat a ≤ optENat b := by
  cases a <;> cases b <;> simp [leO]

/-- Selection test for port `p`: the chosen cities are a valid nearest choice. -/
def selOK (I : Instance) (c : Cand) (p : Cell) : Bool :=
  (c.sel p).all (fun x => decide (x ∈ I.cities)) &&
  decide ((c.sel p).dedup.length = I.k) &&
  (c.sel p).all (fun x => (I.gridDistO p x).isSome) &&
  (c.sel p).all (fun x => I.citiesL.all (fun y =>
    decide (y ∈ c.sel p) || leO (I.gridDistO p x) (I.gridDistO p y)))

theorem selOK_iff (I : Instance) (c : Cand) (p : Cell) :
    selOK I c p = true ↔ I.IsNearestChoice p (c.toSolution.choice p) := by
  simp only [selOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    leO_iff, Instance.IsNearestChoice, Cand.toSolution, List.card_toFinset,
    List.mem_toFinset, Instance.gridDist_eq, optENat_lt_top, Instance.mem_citiesL,
    Finset.subset_iff, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro h x hx y hy hny
    exact (h x hx y hy).resolve_left hny
  · intro h x hx y hy
    by_cases hmem : y ∈ c.sel p
    · exact Or.inl hmem
    · exact Or.inr (h x hx y hy hmem)

/-- Connectivity test for port `p`. -/
def connOK (I : Instance) (c : Cand) (p : Cell) : Bool :=
  (c.sel p).all (fun x => (netDistO I.isFreeB c.edges p x).isSome)

theorem connOK_iff (I : Instance) (c : Cand) (p : Cell) :
    connOK I c p = true ↔ ∀ x ∈ c.toSolution.choice p, c.toSolution.netDist I p x < ⊤ := by
  simp only [connOK, List.all_eq_true, Cand.netDist_eq, optENat_lt_top]
  simp [Cand.toSolution]

/-- Boolean feasibility test. -/
def feasB (I : Instance) (c : Cand) : Bool :=
  c.edges.all (fun e => I.gridAdjB e.1 e.2) && degOK I c.edges &&
  I.portsL.all (fun p => selOK I c p && connOK I c p)

theorem feasB_iff (I : Instance) (c : Cand) :
    feasB I c = true ↔ c.toSolution.Feasible I := by
  unfold feasB Solution.Feasible
  rw [Bool.and_eq_true, Bool.and_eq_true, degOK_iff]
  simp only [List.all_eq_true, Bool.and_eq_true, selOK_iff, connOK_iff,
    Instance.mem_portsL, Instance.gridAdjB_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun e he => h1 e ?_, h2, fun p hp => (h3 p hp).1, fun p hp => (h3 p hp).2⟩
    simpa [Cand.toSolution] using he
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨fun e he => h1 e ?_, h2⟩, fun p hp => ⟨h3 p hp, h4 p hp⟩⟩
    simpa [Cand.toSolution] using he

/-- Excess of one pair. -/
def pairEx (I : Instance) (c : Cand) (p x : Cell) : ℕ :=
  (netDistO I.isFreeB c.edges p x).getD 0 - (I.gridDistO p x).getD 0

/-- Total excess. -/
def excessN (I : Instance) (c : Cand) : ℕ :=
  (I.portsL.map (fun p => ((c.sel p).dedup.map (fun x => pairEx I c p x)).sum)).sum

theorem excess_eq (I : Instance) (c : Cand) (hf : c.toSolution.Feasible I) :
    c.toSolution.excess I = (excessN I c : ℕ∞) := by
  obtain ⟨-, -, h3, h4⟩ := hf
  unfold Solution.excess excessN
  rw [← Instance.toFinset_portsL, List.sum_toFinset _ Instance.nodup_portsL,
    Nat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hp' : p ∈ I.ports := Instance.mem_portsL.1 hp
  have hsel : c.toSolution.choice p = (c.sel p).dedup.toFinset := by
    simp [Cand.toSolution]
  simp only [Function.comp]
  rw [hsel, List.sum_toFinset _ (List.nodup_dedup _), Nat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hx' : x ∈ c.toSolution.choice p := by
    rw [hsel]
    simpa using hx
  have hg := (h3 p hp').2.2.1 x hx'
  have hn := h4 p hp' x hx'
  rw [Instance.gridDist_eq, optENat_lt_top] at hg
  rw [Cand.netDist_eq, optENat_lt_top] at hn
  simp only [Function.comp, pairEx, Cand.netDist_eq, Instance.gridDist_eq]
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hg
  rw [ha, hb]
  simp

/-- Cost in `ℕ × ℕ`: (total excess, number of tiles). -/
def costN (I : Instance) (c : Cand) : ℕ × ℕ := (excessN I c, tilesN I c.edges)

theorem cost_eq (I : Instance) (c : Cand) (hf : c.toSolution.Feasible I) :
    c.toSolution.cost I = toLex (((costN I c).1 : ℕ∞), (costN I c).2) := by
  unfold Solution.cost costN
  rw [excess_eq I c hf, tiles_card_eq]

/-- Lexicographic `≤` on `ℕ × ℕ`. -/
def lexLe (a b : ℕ × ℕ) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

theorem lexLe_iff (a b : ℕ × ℕ) :
    lexLe a b = true ↔
      (toLex ((a.1 : ℕ∞), a.2) : Lex (ℕ∞ × ℕ)) ≤ toLex ((b.1 : ℕ∞), b.2) := by
  rw [Prod.Lex.toLex_le_toLex]
  simp [lexLe]

theorem lexLe_total (a b : ℕ × ℕ) : lexLe a b = true ∨ lexLe b a = true := by
  simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem lexLe_trans {a b c : ℕ × ℕ} (h1 : lexLe a b = true) (h2 : lexLe b c = true) :
    lexLe a c = true := by
  simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem lexLe_refl (a : ℕ × ℕ) : lexLe a a = true := by
  simp [lexLe]

end TrainNetwork
