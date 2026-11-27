/-
An exhaustive solver `Brute.bruteSolve` for the Train Network Problem, with a proof that
it returns an optimal solution, or `none` exactly when the instance is infeasible
(`bruteSolve_correct`). It is a plain function, deliberately not in `TimeM`: it
enumerates exponentially many candidates and no running-time claim is made for it.

Construction:

* computable mirrors (`gridDistC`, `netDistC`, `neighboursC`, `tilesC`, `FeasibleC`,
  `costC`) of the noncomputable definitions of `TrainNetwork.Problem`, each proven
  equal to the original;
* `candidates I`: every subset of the grid edges in canonical orientation (`allEdges`),
  paired with every assignment of a set of cities to each port (`allChoices`);
* `bruteSolve I`: the first cost-minimal feasible candidate.

The key lemma is `exists_candidate`: every feasible solution has a candidate twin that
is feasible and has the same cost. Feasibility and cost only depend on a solution
through its adjacency relation `NetAdj` and its `choice` at the ports
(`Solution.Feasible.congr`, `Solution.cost_congr`), and the twin agrees on both.
-/
import TrainNetwork.Brute.Dist

namespace TrainNetwork

/-! ### Computable decidability of `NetAdj` -/

instance Solution.NetAdj.instDecidableRel (σ : Solution) : DecidableRel σ.NetAdj := fun a b => by
  unfold Solution.NetAdj; infer_instance

/-! ### Facts about the frozen definitions (no decidability needed) -/

namespace Instance

variable {I : Instance} {a b : Cell}

theorem GridAdj.symm (h : I.GridAdj a b) : I.GridAdj b a := by
  obtain ⟨hadj, ha, hb⟩ := h
  refine ⟨?_, hb, ha⟩
  unfold Adjacent at hadj ⊢
  omega

end Instance

namespace Solution

variable {I : Instance} {σ τ : Solution} {a b x y c : Cell}

theorem NetAdj.symm (h : σ.NetAdj a b) : σ.NetAdj b a :=
  Or.symm h

theorem mem_neighbours : y ∈ σ.neighbours x ↔ σ.NetAdj x y := by
  simp only [neighbours, NetAdj, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨e, ⟨he, rfl⟩, rfl⟩ | ⟨e, ⟨he, rfl⟩, rfl⟩)
    · exact Or.inl he
    · exact Or.inr he
  · rintro (h | h)
    · exact Or.inl ⟨(x, y), ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨(y, x), ⟨h, rfl⟩, rfl⟩

theorem mem_tiles : c ∈ σ.tiles I ↔ I.IsFree c ∧ ∃ y, σ.NetAdj c y := by
  simp only [tiles, NetAdj, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨e, he, rfl⟩ | ⟨e, he, rfl⟩, hfree⟩
    · exact ⟨hfree, e.2, Or.inl he⟩
    · exact ⟨hfree, e.1, Or.inr he⟩
  · rintro ⟨hfree, y, h | h⟩
    · exact ⟨Or.inl ⟨(c, y), h, rfl⟩, hfree⟩
    · exact ⟨Or.inr ⟨(y, c), h, rfl⟩, hfree⟩

/-- If all edges are grid edges, network adjacency implies grid adjacency. -/
theorem netAdj_gridAdj (h : ∀ e ∈ σ.edges, I.GridAdj e.1 e.2) (hab : σ.NetAdj a b) :
    I.GridAdj a b := by
  rcases hab with h1 | h1
  · exact h _ h1
  · exact (h _ h1).symm

theorem netAdj_inBounds (h : ∀ e ∈ σ.edges, I.GridAdj e.1 e.2) (a b : Cell)
    (hab : σ.NetAdj a b) : I.InBounds b :=
  (netAdj_gridAdj h hab).2.2.1

/-! Everything below only depends on `σ` through `σ.NetAdj` and `σ.choice` at the ports. -/

theorem neighbours_congr (hN : ∀ a b, σ.NetAdj a b ↔ τ.NetAdj a b) (x : Cell) :
    σ.neighbours x = τ.neighbours x := by
  ext y
  rw [mem_neighbours, mem_neighbours, hN]

theorem tiles_congr (hN : ∀ a b, σ.NetAdj a b ↔ τ.NetAdj a b) : σ.tiles I = τ.tiles I := by
  ext c
  simp only [mem_tiles, hN]

theorem netDist_congr (hN : ∀ a b, σ.NetAdj a b ↔ τ.NetAdj a b) (s t : Cell) :
    σ.netDist I s t = τ.netDist I s t :=
  Instance.walkDist_congr hN

theorem Feasible.congr (hN : ∀ a b, σ.NetAdj a b ↔ τ.NetAdj a b)
    (hc : ∀ p ∈ I.ports, σ.choice p = τ.choice p) (h : τ.Feasible I) : σ.Feasible I := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun e he => ?_, fun x hx => ?_, fun p hp => ?_, fun p hp c hc' => ?_⟩
  · exact netAdj_gridAdj h1 ((hN e.1 e.2).1 (Or.inl he))
  · rw [neighbours_congr hN]
    exact h2 x hx
  · rw [hc p hp]
    exact h3 p hp
  · rw [netDist_congr hN]
    exact h4 p hp c (hc p hp ▸ hc')

theorem cost_congr (hN : ∀ a b, σ.NetAdj a b ↔ τ.NetAdj a b)
    (hc : ∀ p ∈ I.ports, σ.choice p = τ.choice p) : σ.cost I = τ.cost I := by
  have hex : σ.excess I = τ.excess I := by
    unfold excess
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hc p hp]
    exact Finset.sum_congr rfl fun c _ => by rw [netDist_congr hN]
  rw [cost, cost, hex, tiles_congr hN]

end Solution

namespace Brute

open Instance Solution

/-! ### Computable mirrors of the frozen definitions -/

/-- Executable `Instance.gridDist`. -/
def gridDistC (I : Instance) (s t : Cell) : ℕ∞ := walkDistC I I.GridAdj s t

/-- Executable `Solution.netDist` (correct when all edges are grid edges). -/
def netDistC (I : Instance) (σ : Solution) (s t : Cell) : ℕ∞ := walkDistC I σ.NetAdj s t

/-- Executable `Solution.neighbours`. -/
def neighboursC (σ : Solution) (x : Cell) : Finset Cell :=
  (σ.edges.filter (fun e => e.1 = x)).image Prod.snd ∪
  (σ.edges.filter (fun e => e.2 = x)).image Prod.fst

/-- Executable `Solution.tiles`. -/
def tilesC (I : Instance) (σ : Solution) : Finset Cell :=
  (σ.edges.image Prod.fst ∪ σ.edges.image Prod.snd).filter (fun c => I.IsFree c)

theorem gridDistC_eq (I : Instance) (s t : Cell) : gridDistC I s t = I.gridDist s t :=
  walkDistC_gridAdj I s t

theorem netDistC_eq (I : Instance) (σ : Solution) (h : ∀ e ∈ σ.edges, I.GridAdj e.1 e.2)
    (s t : Cell) : netDistC I σ s t = σ.netDist I s t :=
  walkDistC_eq I σ.NetAdj (netAdj_inBounds h) s t

theorem neighboursC_eq (σ : Solution) (x : Cell) : neighboursC σ x = σ.neighbours x := by
  ext y
  simp [neighboursC, neighbours]

theorem tilesC_eq (I : Instance) (σ : Solution) : tilesC I σ = σ.tiles I := by
  ext c
  simp [tilesC, tiles]

/-- Computable restatement of `Solution.Feasible`. -/
def FeasibleC (I : Instance) (σ : Solution) : Prop :=
  (∀ e ∈ σ.edges, I.GridAdj e.1 e.2) ∧
  (∀ x ∈ cells I, I.IsFree x → (neighboursC σ x).card ≤ 3) ∧
  (∀ p ∈ I.ports, σ.choice p ⊆ I.cities ∧ (σ.choice p).card = I.k ∧
      (∀ c ∈ σ.choice p, gridDistC I p c < ⊤) ∧
      (∀ c ∈ σ.choice p, ∀ c' ∈ I.cities, c' ∉ σ.choice p →
        gridDistC I p c ≤ gridDistC I p c')) ∧
  (∀ p ∈ I.ports, ∀ c ∈ σ.choice p, netDistC I σ p c < ⊤)

instance FeasibleC.instDecidable (I : Instance) (σ : Solution) : Decidable (FeasibleC I σ) := by
  unfold FeasibleC; infer_instance

theorem feasibleC_iff (I : Instance) (σ : Solution) : FeasibleC I σ ↔ σ.Feasible I := by
  unfold FeasibleC Feasible
  refine and_congr_right fun h1 => and_congr ?_ (and_congr ?_ ?_)
  · simp only [neighboursC_eq]
    constructor
    · intro h x hx
      exact h x ((mem_cells I x).2 hx.1) hx
    · intro h x _ hx
      exact h x hx
  · simp only [gridDistC_eq, IsNearestChoice]
  · simp only [netDistC_eq I σ h1]

instance Feasible.instDecidable (I : Instance) (σ : Solution) : Decidable (σ.Feasible I) :=
  decidable_of_iff _ (feasibleC_iff I σ)

/-- Executable `Solution.cost` (correct when all edges are grid edges). -/
def costC (I : Instance) (σ : Solution) : Lex (ℕ∞ × ℕ) :=
  toLex (∑ p ∈ I.ports, ∑ c ∈ σ.choice p, (netDistC I σ p c - gridDistC I p c),
    (tilesC I σ).card)

theorem costC_eq (I : Instance) (σ : Solution) (h : ∀ e ∈ σ.edges, I.GridAdj e.1 e.2) :
    costC I σ = σ.cost I := by
  simp only [costC, cost, excess, netDistC_eq I σ h, gridDistC_eq, tilesC_eq]

/-! ### Enumerating candidate solutions -/

/-- Grid edges in canonical orientation (to the right / downwards). -/
def allEdges (I : Instance) : List (Cell × Cell) :=
  (cells I).flatMap fun c =>
    ([(c.1 + 1, c.2), (c.1, c.2 + 1)].filter fun c' => I.GridAdj c c').map fun c' => (c, c')

theorem mem_allEdges {I : Instance} {a b : Cell} :
    (a, b) ∈ allEdges I ↔ I.GridAdj a b ∧ (b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1)) := by
  simp only [allEdges, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨c, -, c', ⟨hc', hadj⟩, rfl, rfl⟩
    exact ⟨hadj, hc'⟩
  · rintro ⟨hadj, hb⟩
    exact ⟨a, (mem_cells I a).2 hadj.2.1.1, b, ⟨hb, hadj⟩, rfl, rfl⟩

theorem gridAdj_of_mem_allEdges {I : Instance} {e : Cell × Cell} (h : e ∈ allEdges I) :
    I.GridAdj e.1 e.2 :=
  (mem_allEdges.1 h).1

/-- Every grid edge appears in `allEdges` in one of its two orientations. -/
theorem mem_allEdges_or_swap {I : Instance} {a b : Cell} (h : I.GridAdj a b) :
    (a, b) ∈ allEdges I ∨ (b, a) ∈ allEdges I := by
  have hadj := h.1
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [Adjacent] at hadj
  rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl (mem_allEdges.2 ⟨h, Or.inr (Prod.ext h1.symm h2.symm)⟩)
  · exact Or.inr (mem_allEdges.2 ⟨h.symm, Or.inr (Prod.ext h1 h2.symm)⟩)
  · exact Or.inl (mem_allEdges.2 ⟨h, Or.inl (Prod.ext h2.symm h1.symm)⟩)
  · exact Or.inr (mem_allEdges.2 ⟨h.symm, Or.inl (Prod.ext h2.symm h1)⟩)

/-- The ports, as a list. -/
def portsL (I : Instance) : List Cell := (cells I).filter (· ∈ I.ports)

theorem mem_portsL {I : Instance} {p : Cell} : p ∈ portsL I ↔ p ∈ I.ports := by
  simp only [portsL, List.mem_filter, decide_eq_true_eq, mem_cells]
  exact ⟨fun h => h.2, fun h => ⟨I.ports_inBounds p h, h⟩⟩

theorem portsL_nodup (I : Instance) : (portsL I).Nodup :=
  (cells_nodup I).filter _

/-- All sets of cities. -/
def citySubsets (I : Instance) : List (Finset Cell) :=
  ((cells I).filter (· ∈ I.cities)).sublists.map List.toFinset

theorem mem_citySubsets_of_subset {I : Instance} {S : Finset Cell} (h : S ⊆ I.cities) :
    S ∈ citySubsets I := by
  refine List.mem_map.2 ⟨((cells I).filter (· ∈ I.cities)).filter (· ∈ S),
    List.mem_sublists.2 List.filter_sublist, ?_⟩
  ext c
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_cells]
  exact ⟨fun h' => h'.2, fun hc => ⟨⟨I.cities_inBounds c (h hc), h hc⟩, hc⟩⟩

/-- All assignments of a set of cities to each cell of the given list (and `∅` to every
other cell). -/
def allChoices (I : Instance) : List Cell → List (Cell → Finset Cell)
  | [] => [fun _ => ∅]
  | p :: ps =>
    (citySubsets I).flatMap fun S => (allChoices I ps).map fun f => Function.update f p S

theorem exists_mem_allChoices {I : Instance} (g : Cell → Finset Cell) :
    ∀ ps : List Cell, (∀ p ∈ ps, g p ⊆ I.cities) →
      ∃ f ∈ allChoices I ps, ∀ p ∈ ps, f p = g p
  | [], _ => ⟨fun _ => ∅, by simp [allChoices], by simp⟩
  | p :: ps, h => by
    obtain ⟨f, hf, hfg⟩ :=
      exists_mem_allChoices g ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨Function.update f p (g p), ?_, fun q hq => ?_⟩
    · exact List.mem_flatMap.2 ⟨g p, mem_citySubsets_of_subset (h p List.mem_cons_self),
        List.mem_map.2 ⟨f, hf, rfl⟩⟩
    · by_cases hqp : q = p
      · subst hqp
        exact Function.update_self ..
      · rw [Function.update_of_ne hqp]
        exact hfg q ((List.mem_cons.1 hq).resolve_left hqp)

/-- Candidate solutions: any set of canonically oriented grid edges, with any assignment
of city sets to the ports. -/
def candidates (I : Instance) : List Solution :=
  (allEdges I).sublists.flatMap fun es =>
    (allChoices I (portsL I)).map fun f => ⟨es.toFinset, f⟩

/-- Normalisation: every feasible solution has a candidate twin that is feasible and has
the same cost. -/
theorem exists_candidate (I : Instance) (τ : Solution) (h : τ.Feasible I) :
    ∃ σ ∈ candidates I, σ.Feasible I ∧ σ.cost I = τ.cost I := by
  obtain ⟨f, hf, hfτ⟩ := exists_mem_allChoices (I := I) τ.choice (portsL I)
    fun p hp => (h.2.2.1 p (mem_portsL.1 hp)).1
  let es := (allEdges I).filter fun e => e ∈ τ.edges ∨ (e.2, e.1) ∈ τ.edges
  have hN : ∀ a b, (Solution.mk es.toFinset f).NetAdj a b ↔ τ.NetAdj a b := by
    intro a b
    simp only [NetAdj, List.mem_toFinset, es, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩)
      · exact Or.inl h1
      · exact Or.inr h1
      · exact Or.inr h1
      · exact Or.inl h1
    · intro hab
      rcases mem_allEdges_or_swap (netAdj_gridAdj h.1 hab) with h1 | h1
      · exact Or.inl ⟨h1, hab⟩
      · exact Or.inr ⟨h1, hab.symm⟩
  have hc : ∀ p ∈ I.ports, (Solution.mk es.toFinset f).choice p = τ.choice p :=
    fun p hp => hfτ p (mem_portsL.2 hp)
  refine ⟨⟨es.toFinset, f⟩, ?_, Feasible.congr hN hc h, cost_congr hN hc⟩
  exact List.mem_flatMap.2 ⟨es, List.mem_sublists.2 List.filter_sublist,
    List.mem_map.2 ⟨f, hf, rfl⟩⟩

/-! ### The solver -/

/-- Exhaustive search. A plain function, deliberately NOT in `TimeM`: no running-time
claim is made for it. -/
def bruteSolve (I : Instance) : Option Solution :=
  List.argmin (costC I) ((candidates I).filter fun σ => FeasibleC I σ)

private theorem mem_filter_candidates {I : Instance} {σ : Solution} (hσ : σ ∈ candidates I)
    (hf : σ.Feasible I) : σ ∈ (candidates I).filter fun σ => FeasibleC I σ :=
  List.mem_filter.2 ⟨hσ, decide_eq_true ((feasibleC_iff I σ).2 hf)⟩

/-- `bruteSolve` only returns optimal solutions. -/
theorem isOptimal_of_bruteSolve_eq_some {I : Instance} {σ : Solution}
    (h : bruteSolve I = some σ) : IsOptimal I σ := by
  have hσ := List.argmin_mem h
  have hσF : σ.Feasible I :=
    (feasibleC_iff I σ).1 (of_decide_eq_true (List.mem_filter.1 hσ).2)
  refine ⟨hσF, fun τ hτ => ?_⟩
  obtain ⟨σ', hσ', hf', hcost⟩ := exists_candidate I τ hτ
  have hle := List.le_of_mem_argmin (mem_filter_candidates hσ' hf') h
  rwa [costC_eq I σ hσF.1, costC_eq I σ' hf'.1, hcost] at hle

/-- `bruteSolve` returns `none` only on infeasible instances. -/
theorem not_feasible_of_bruteSolve_eq_none {I : Instance} (h : bruteSolve I = none) :
    ¬ ∃ σ : Solution, σ.Feasible I := by
  have hnil : ((candidates I).filter fun σ => FeasibleC I σ) = [] := List.argmin_eq_none.1 h
  rintro ⟨τ, hτ⟩
  obtain ⟨σ, hσ, hf, -⟩ := exists_candidate I τ hτ
  have hmem := mem_filter_candidates hσ hf
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

/-- `bruteSolve` returns an optimal solution, or `none` exactly when the instance is
infeasible. -/
theorem bruteSolve_correct (I : Instance) :
    match bruteSolve I with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I := by
  cases h : bruteSolve I with
  | none => exact not_feasible_of_bruteSolve_eq_none h
  | some σ => exact isOptimal_of_bruteSolve_eq_some h

/-- (excess, tiles) of the optimum, for `#eval`. -/
def bruteCost (I : Instance) : Option (ℕ∞ × ℕ) :=
  (bruteSolve I).map fun σ => ofLex (costC I σ)

/-! ### Smoke tests -/

/-- (a) The shape of the frozen `tinyInstance`: a `3 × 1` corridor. -/
private def exampleA : Instance where
  W := 3
  H := 1
  blocked := ∅
  ports := {(0, 0)}
  cities := {(2, 0)}
  k := 1
  k_pos := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide

/-- (b) A plus shape: every grid distance is finite, but the centre cell would need four
neighbours, so the instance is infeasible. -/
private def exampleB : Instance where
  W := 3
  H := 3
  blocked := {(0, 0), (2, 0), (0, 2), (2, 2)}
  ports := {(0, 1)}
  cities := {(1, 0), (2, 1), (1, 2)}
  k := 3
  k_pos := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide

/-- (c) A `3 × 2` grid with one port and two cities, both of which must be served. -/
private def exampleC : Instance where
  W := 3
  H := 2
  blocked := ∅
  ports := {(0, 0)}
  cities := {(2, 0), (2, 1)}
  k := 2
  k_pos := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide

-- Output format: `some (excess, tiles)`, where Mathlib's `Repr ℕ∞` shows `(n : ℕ∞)` as
-- `some n` and `⊤` as `none`; an outer `none` means "infeasible".
#eval bruteCost exampleA -- some (some 0, 1)
#eval bruteCost exampleB -- none
#eval bruteCost exampleC -- some (some 0, 2)

#print axioms bruteSolve_correct

end Brute

end TrainNetwork
