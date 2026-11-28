/-
Search over a list of candidates, and the exhaustive candidate list.

* `best` / `solveFrom` : pick the cheapest feasible candidate of a list.
* `Complete`           : a candidate list dominates every feasible solution.
* `solveFrom_correct`  : on a complete list, `solveFrom` meets the specification of
                         `Goal.lean` (optimal solution, or `none` iff infeasible).
                         This holds for *any* complete list, so the open question of
                         `Goal.lean` is exactly: is there a complete list that can be
                         produced and searched in quasi-polynomial time?
* `allCands`           : every edge subset of the grid times every choice function.
* `allCands_complete`  : the exhaustive list is complete.

Nothing in this file is timed; the `TimeM` versions live in `Timed.lean`.
-/
import TrainNetwork.Exec

namespace TrainNetwork

/-! ### Picking the best feasible candidate -/

/-- One step of the search: keep the better of the accumulator and `c`. -/
def better (I : Instance) (acc : Option (Cand × (ℕ × ℕ))) (c : Cand) :
    Option (Cand × (ℕ × ℕ)) :=
  if feasB I c then
    match acc with
    | none => some (c, costN I c)
    | some (b, cb) => if lexLe cb (costN I c) then some (b, cb) else some (c, costN I c)
  else acc

/-- The cheapest feasible candidate of `cs`, with its cost. -/
def best (I : Instance) (cs : List Cand) : Option (Cand × (ℕ × ℕ)) :=
  cs.foldl (better I) none

/-- Invariant of the search. -/
def Good (I : Instance) (cs : List Cand) : Option (Cand × (ℕ × ℕ)) → Prop
  | none => ∀ c ∈ cs, feasB I c = false
  | some (b, cb) => b ∈ cs ∧ feasB I b = true ∧ cb = costN I b ∧
      ∀ c ∈ cs, feasB I c = true → lexLe cb (costN I c) = true

theorem good_better (I : Instance) (pre : List Cand) (acc : Option (Cand × (ℕ × ℕ)))
    (c : Cand) (h : Good I pre acc) : Good I (pre ++ [c]) (better I acc c) := by
  unfold better
  by_cases hc : feasB I c = true
  · simp only [hc, ↓reduceIte]
    match acc, h with
    | none, h =>
      refine ⟨by simp, hc, rfl, ?_⟩
      intro d hd hdf
      rcases List.mem_append.1 hd with hd | hd
      · rw [h d hd] at hdf
        exact absurd hdf (by simp)
      · obtain rfl : d = c := by simpa using hd
        exact lexLe_refl _
    | some (b, cb), ⟨hb1, hb2, hb3, hb4⟩ =>
      by_cases hle : lexLe cb (costN I c) = true
      · simp only [hle, ↓reduceIte]
        refine ⟨List.mem_append_left _ hb1, hb2, hb3, ?_⟩
        intro d hd hdf
        rcases List.mem_append.1 hd with hd | hd
        · exact hb4 d hd hdf
        · obtain rfl : d = c := by simpa using hd
          exact hle
      · simp only [hle, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simp, hc, rfl, ?_⟩
        intro d hd hdf
        rcases List.mem_append.1 hd with hd | hd
        · exact lexLe_trans ((lexLe_total _ _).resolve_left hle) (hb4 d hd hdf)
        · obtain rfl : d = c := by simpa using hd
          exact lexLe_refl _
  · have hc' : feasB I c = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    match acc, h with
    | none, h =>
      intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact h d hd
      · obtain rfl : d = c := by simpa using hd
        exact hc'
    | some (b, cb), ⟨hb1, hb2, hb3, hb4⟩ =>
      refine ⟨List.mem_append_left _ hb1, hb2, hb3, ?_⟩
      intro d hd hdf
      rcases List.mem_append.1 hd with hd | hd
      · exact hb4 d hd hdf
      · obtain rfl : d = c := by simpa using hd
        rw [hc'] at hdf
        exact absurd hdf (by simp)

theorem good_foldl (I : Instance) :
    ∀ (cs pre : List Cand) (acc : Option (Cand × (ℕ × ℕ))), Good I pre acc →
      Good I (pre ++ cs) (cs.foldl (better I) acc)
  | [], pre, acc, h => by simpa using h
  | c :: cs, pre, acc, h => by
    have := good_foldl I cs (pre ++ [c]) (better I acc c) (good_better I pre acc c h)
    simpa using this

theorem best_good (I : Instance) (cs : List Cand) : Good I cs (best I cs) := by
  have := good_foldl I cs [] none (by simp [Good])
  simpa [best] using this

/-- Search a candidate list and return the cheapest feasible candidate as a solution. -/
def solveFrom (I : Instance) (cs : List Cand) : Option Solution :=
  (best I cs).map (fun r => r.1.toSolution)

/-- `cs` dominates every feasible solution. -/
def Complete (I : Instance) (cs : List Cand) : Prop :=
  ∀ τ : Solution, τ.Feasible I →
    ∃ c ∈ cs, c.toSolution.Feasible I ∧ c.toSolution.cost I ≤ τ.cost I

/-- On a complete candidate list the search meets the specification of `Goal.lean`. -/
theorem solveFrom_correct (I : Instance) (cs : List Cand) (h : Complete I cs) :
    match solveFrom I cs with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I := by
  have hg := best_good I cs
  unfold solveFrom
  cases hb : best I cs with
  | none =>
    rw [hb] at hg
    simp only [Option.map_none]
    rintro ⟨τ, hτ⟩
    obtain ⟨c, hc, hcf, -⟩ := h τ hτ
    have := hg c hc
    rw [← Bool.not_eq_true, feasB_iff] at this
    exact this hcf
  | some r =>
    obtain ⟨b, cb⟩ := r
    rw [hb] at hg
    obtain ⟨-, hb2, hb3, hb4⟩ := hg
    simp only [Option.map_some]
    have hbf := (feasB_iff I b).1 hb2
    refine ⟨hbf, fun τ hτ => ?_⟩
    obtain ⟨c, hc, hcf, hcle⟩ := h τ hτ
    refine le_trans ?_ hcle
    rw [cost_eq I b hbf, cost_eq I c hcf, ← lexLe_iff, ← hb3]
    exact hb4 c hc ((feasB_iff I c).2 hcf)

/-! ### Feasibility and cost only depend on the edges and on the choice at ports -/

theorem Solution.feasible_congr {I : Instance} {σ τ : Solution} (he : σ.edges = τ.edges)
    (hc : ∀ p ∈ I.ports, σ.choice p = τ.choice p) : σ.Feasible I ↔ τ.Feasible I := by
  obtain ⟨E, ch⟩ := σ
  obtain ⟨E', ch'⟩ := τ
  obtain rfl : E = E' := he
  have hc' : ∀ p ∈ I.ports, ch p = ch' p := hc
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun p hp => ?_, fun p hp x hx => ?_⟩
    · have := h3 p hp
      simp only [hc' p hp] at this
      exact this
    · have := h4 p hp x (by simp only [hc' p hp]; exact hx)
      exact this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun p hp => ?_, fun p hp x hx => ?_⟩
    · have := h3 p hp
      simp only [← hc' p hp] at this
      exact this
    · have := h4 p hp x (by simp only [← hc' p hp]; exact hx)
      exact this

theorem Solution.cost_congr {I : Instance} {σ τ : Solution} (he : σ.edges = τ.edges)
    (hc : ∀ p ∈ I.ports, σ.choice p = τ.choice p) : σ.cost I = τ.cost I := by
  obtain ⟨E, ch⟩ := σ
  obtain ⟨E', ch'⟩ := τ
  obtain rfl : E = E' := he
  have hc' : ∀ p ∈ I.ports, ch p = ch' p := hc
  have hex : Solution.excess I ⟨E, ch⟩ = Solution.excess I ⟨E, ch'⟩ := by
    unfold Solution.excess
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hc' p hp]
    rfl
  unfold Solution.cost
  rw [hex]
  rfl

/-! ### The exhaustive candidate list -/

/-- All sublists of a list. -/
def subl {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => subl l ++ (subl l).map (fun s => a :: s)

theorem filter_mem_subl {α : Type} (p : α → Bool) : ∀ l : List α, l.filter p ∈ subl l
  | [] => by simp [subl]
  | a :: l => by
    have ih := filter_mem_subl p l
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h]
      exact List.mem_append_right _ (List.mem_map.2 ⟨_, ih, rfl⟩)
    · rw [List.filter_cons_of_neg h]
      exact List.mem_append_left _ ih

theorem length_subl {α : Type} : ∀ l : List α, (subl l).length = 2 ^ l.length
  | [] => rfl
  | a :: l => by
    simp only [subl, List.length_append, List.length_map, length_subl l, List.length_cons]
    omega

theorem length_le_of_mem_subl {α : Type} :
    ∀ (l : List α) (s : List α), s ∈ subl l → s.length ≤ l.length
  | [], s, h => by
    obtain rfl : s = [] := by simpa [subl] using h
    simp
  | a :: l, s, h => by
    rcases List.mem_append.1 h with h | h
    · exact (length_le_of_mem_subl l s h).trans (by simp)
    · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 h
      simpa using length_le_of_mem_subl l s' hs'

/-- All association lists that give every port of `ps` one of the lists in `sub`. -/
def choicesL (sub : List (List Cell)) : List Cell → List (List (Cell × List Cell))
  | [] => [[]]
  | p :: ps => sub.flatMap (fun S => (choicesL sub ps).map (fun r => (p, S) :: r))

theorem map_mem_choicesL {sub : List (List Cell)} (f : Cell → List Cell)
    (hf : ∀ p, f p ∈ sub) : ∀ ps : List Cell, ps.map (fun p => (p, f p)) ∈ choicesL sub ps
  | [] => by simp [choicesL]
  | p :: ps => by
    simp only [choicesL, List.map_cons, List.mem_flatMap, List.mem_map]
    exact ⟨f p, hf p, _, map_mem_choicesL f hf ps, rfl⟩

theorem lookupL_map (f : Cell → List Cell) :
    ∀ (ps : List Cell) (p : Cell), p ∈ ps → lookupL p (ps.map (fun q => (q, f q))) = f p
  | [], p, h => by simp at h
  | q :: ps, p, h => by
    simp only [List.map_cons, lookupL]
    by_cases hq : q = p
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      exact lookupL_map f ps p ((List.mem_cons.1 h).resolve_left (fun h' => hq h'.symm))

theorem length_choicesL (sub : List (List Cell)) :
    ∀ ps : List Cell, (choicesL sub ps).length = sub.length ^ ps.length
  | [] => by simp [choicesL]
  | p :: ps => by
    have h : ∀ l : List (List Cell),
        (l.flatMap (fun S => (choicesL sub ps).map (fun r => (p, S) :: r))).length =
          l.length * (choicesL sub ps).length := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, ih,
          List.length_cons]
        ring
    rw [choicesL, h, length_choicesL sub ps, List.length_cons, pow_succ]
    ring

/-- Every edge subset of the grid, with every choice of city lists for the ports. -/
def allCands (I : Instance) : List Cand :=
  (subl I.gridEdgesL).flatMap (fun E =>
    (choicesL (subl I.citiesL) I.portsL).map (fun ch => (⟨E, ch⟩ : Cand)))

theorem allCands_complete (I : Instance) : Complete I (allCands I) := by
  intro τ hτ
  let f : Cell → List Cell := fun p => I.citiesL.filter (fun x => decide (x ∈ τ.choice p))
  let c : Cand := ⟨I.gridEdgesL.filter (fun e => decide (e ∈ τ.edges)),
    I.portsL.map (fun p => (p, f p))⟩
  have he : c.toSolution.edges = τ.edges := by
    ext ⟨a, b⟩
    simp only [Cand.toSolution, c, List.mem_toFinset, List.mem_filter,
      Instance.mem_gridEdgesL, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun h => hτ.1 _ h
  have hc : ∀ p ∈ I.ports, c.toSolution.choice p = τ.choice p := by
    intro p hp
    have hsel : c.sel p = f p := lookupL_map f _ p (Instance.mem_portsL.2 hp)
    ext x
    simp only [Cand.toSolution, hsel, f, List.mem_toFinset, List.mem_filter,
      Instance.mem_citiesL, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun h => (hτ.2.2.1 p hp).1 h
  refine ⟨c, ?_, (Solution.feasible_congr he hc).2 hτ, le_of_eq (Solution.cost_congr he hc)⟩
  simp only [allCands, List.mem_flatMap, List.mem_map]
  exact ⟨_, filter_mem_subl _ _, _, map_mem_choicesL f (fun p => filter_mem_subl _ _) _, rfl⟩

/-- The exhaustive solver, as a pure function. -/
def solvePure (I : Instance) : Option Solution := solveFrom I (allCands I)

theorem solvePure_correct (I : Instance) :
    match solvePure I with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I :=
  solveFrom_correct I _ (allCands_complete I)

end TrainNetwork
