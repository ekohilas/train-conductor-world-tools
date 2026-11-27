/-
Soundness of the encoding: a satisfying assignment of `enc I X K` yields a feasible
solution with excess `≤ X` and at most `K` tiles.
-/
import TrainNetwork.Formula

namespace TrainNetwork.Answer

open TrainNetwork

variable (I : Instance) (a : ℕ → Bool)

/-- The adjacency relation encoded by the edge variables. -/
def EAdj (x y : Cell) : Prop :=
  Adjacent x y ∧ I.IsOpen x ∧ I.IsOpen y ∧ a (vEdge x y) = true

/-- The solution encoded by an assignment. -/
def decSol : Solution where
  edges := ((cells I).flatMap fun v => [(v, (v.1 + 1, v.2)), (v, (v.1, v.2 + 1))]).toFinset.filter
    fun e => a (vEdge e.1 e.2) = true
  choice := fun p => I.cities.filter fun c => a (vSel p c) = true

theorem mem_decSol_edges (x y : Cell) :
    (x, y) ∈ (decSol I a).edges ↔
      (I.InBounds x ∧ (y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1))) ∧ a (vEdge x y) = true := by
  simp only [decSol, Finset.mem_filter, List.mem_toFinset, List.mem_flatMap, mem_cells,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩, he⟩
    · exact ⟨⟨hv, Or.inl rfl⟩, he⟩
    · exact ⟨⟨hv, Or.inr rfl⟩, he⟩
  · rintro ⟨⟨hx, (rfl | rfl)⟩, he⟩
    · exact ⟨⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩, he⟩
    · exact ⟨⟨x, hx, Or.inr ⟨rfl, rfl⟩⟩, he⟩

theorem sat_edgeClauses :
    Sat a (edgeClauses I) ↔ ∀ v ∈ cells I,
      Sat a (edgeAt I v (v.1 + 1, v.2)) ∧ Sat a (edgeAt I v (v.1, v.2 + 1)) ∧
      Sat a (degAt I v) := by
  unfold edgeClauses
  simp only [sat_flatMap, sat_append, and_assoc]

/-- Under the edge clauses, an edge variable that is true joins two open cells, and
its free endpoints are marked as tiles. -/
theorem edge_facts (hE : Sat a (edgeClauses I)) {x y : Cell} (hadj : Adjacent x y)
    (hx : I.InBounds x) (hy : I.InBounds y) (he : a (vEdge x y) = true) :
    (I.IsOpen x ∧ I.IsOpen y) ∧ (I.IsFree x → a (vTile x) = true) := by
  rw [sat_edgeClauses] at hE
  have key : ∀ v u : Cell, I.InBounds v → (u = (v.1 + 1, v.2) ∨ u = (v.1, v.2 + 1)) →
      a (vEdge v u) = true →
      (I.IsOpen v ∧ I.IsOpen u) ∧ (I.IsFree v → a (vTile v) = true) ∧
        (I.IsFree u → a (vTile u) = true) := by
    intro v u hv hu he
    have h := hE v ((mem_cells I v).mpr hv)
    have h' : Sat a (edgeAt I v u) := by
      rcases hu with rfl | rfl
      · exact h.1
      · exact h.2.1
    rw [sat_edgeAt] at h'
    have hopen : I.IsOpen v ∧ I.IsOpen u := by
      by_contra hno
      rw [h'.1 hno] at he
      exact absurd he (by simp)
    exact ⟨hopen, h'.2 hopen.1 hopen.2 he⟩
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  have hcase : ((y1, y2) = (x1 + 1, x2) ∨ (y1, y2) = (x1, x2 + 1)) ∨
      ((x1, x2) = (y1 + 1, y2) ∨ (x1, x2) = (y1, y2 + 1)) := by
    simp only [Adjacent, Prod.mk.injEq] at hadj ⊢
    omega
  rcases hcase with h | h
  · obtain ⟨h1, h2, _⟩ := key (x1, x2) (y1, y2) hx h he
    exact ⟨h1, h2⟩
  · rw [vEdge_comm] at he
    obtain ⟨h1, _, h3⟩ := key (y1, y2) (x1, x2) hy h he
    exact ⟨⟨h1.2, h1.1⟩, h3⟩

theorem netAdj_decSol (hE : Sat a (edgeClauses I)) (x y : Cell) :
    (decSol I a).NetAdj x y ↔ EAdj I a x y := by
  unfold Solution.NetAdj EAdj
  rw [mem_decSol_edges, mem_decSol_edges]
  constructor
  · rintro (⟨⟨hx, hy⟩, he⟩ | ⟨⟨hy, hx⟩, he⟩)
    · have hadj : Adjacent x y := by
        rcases hy with rfl | rfl <;> simp [Adjacent]
      have hopen : ¬¬(I.IsOpen x ∧ I.IsOpen y) := by
        intro hno
        have h := (sat_edgeClauses I a).mp hE x ((mem_cells I x).mpr hx)
        have h' : Sat a (edgeAt I x y) := by
          rcases hy with rfl | rfl
          · exact h.1
          · exact h.2.1
        rw [sat_edgeAt] at h'
        rw [h'.1 hno] at he
        exact absurd he (by simp)
      have hopen' := not_not.mp hopen
      exact ⟨hadj, hopen'.1, hopen'.2, he⟩
    · have hadj : Adjacent x y := by
        rcases hx with rfl | rfl <;> simp [Adjacent]
      have hopen : ¬¬(I.IsOpen y ∧ I.IsOpen x) := by
        intro hno
        have h := (sat_edgeClauses I a).mp hE y ((mem_cells I y).mpr hy)
        have h' : Sat a (edgeAt I y x) := by
          rcases hx with rfl | rfl
          · exact h.1
          · exact h.2.1
        rw [sat_edgeAt] at h'
        rw [h'.1 hno] at he
        exact absurd he (by simp)
      have hopen' := not_not.mp hopen
      exact ⟨hadj, hopen'.2, hopen'.1, by rw [vEdge_comm]; exact he⟩
  · rintro ⟨hadj, hx, hy, he⟩
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    have hcase : ((y1, y2) = (x1 + 1, x2) ∨ (y1, y2) = (x1, x2 + 1)) ∨
        ((x1, x2) = (y1 + 1, y2) ∨ (x1, x2) = (y1, y2 + 1)) := by
      simp only [Adjacent, Prod.mk.injEq] at hadj ⊢
      omega
    rcases hcase with h | h
    · exact Or.inl ⟨⟨hx.1, h⟩, he⟩
    · exact Or.inr ⟨⟨hy.1, h⟩, by rw [vEdge_comm]; exact he⟩

theorem mem_neighbours (σ : Solution) (x y : Cell) :
    y ∈ σ.neighbours x ↔ σ.NetAdj x y := by
  unfold Solution.neighbours Solution.NetAdj
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨e, ⟨h, rfl⟩, rfl⟩ | ⟨e, ⟨h, rfl⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨(x, y), ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨(y, x), ⟨h, rfl⟩, rfl⟩

theorem degree_le (hE : Sat a (edgeClauses I)) (x : Cell) (hx : I.IsFree x) :
    ((decSol I a).neighbours x).card ≤ 3 := by
  have hsub : (decSol I a).neighbours x ⊆
      ((nbrs x).filter fun y => a (vEdge x y)).toFinset := by
    intro y hy
    rw [mem_neighbours, netAdj_decSol I a hE] at hy
    simp only [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_nbrs.mpr (adjacent_comm.mp hy.1), hy.2.2.2⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (List.toFinset_card_le _) ?_)
  have hdeg := ((sat_edgeClauses I a).mp hE x ((mem_cells I x).mpr hx.1)).2.2
  rw [sat_degAt] at hdeg
  by_cases h1 : 1 ≤ x.1
  · by_cases h2 : 1 ≤ x.2
    · have hlen : (nbrs x).length = 4 := by simp [nbrs, h1, h2]
      have hlt : ((nbrs x).filter fun y => a (vEdge x y)).length < (nbrs x).length := by
        rw [List.length_filter_lt_length_iff_exists]
        rcases hdeg hx h1 h2 with h | h | h | h
        · exact ⟨(x.1 + 1, x.2), by simp [nbrs], by simp [h]⟩
        · exact ⟨(x.1, x.2 + 1), by simp [nbrs], by simp [h]⟩
        · exact ⟨(x.1 - 1, x.2), by simp [nbrs, h1], by simp [h]⟩
        · exact ⟨(x.1, x.2 - 1), by simp [nbrs, h2], by simp [h]⟩
      omega
    · have hlen : (nbrs x).length = 3 := by simp [nbrs, h1, h2]
      have := List.length_filter_le (fun y => a (vEdge x y)) (nbrs x)
      omega
  · have hlen : (nbrs x).length ≤ 3 := by
      by_cases h2 : 1 ≤ x.2 <;> simp [nbrs, h1, h2]
    have := List.length_filter_le (fun y => a (vEdge x y)) (nbrs x)
    omega

theorem mem_stepsN (p u v : Cell) :
    u ∈ stepsN I p v ↔ Adjacent u v ∧ (u = p ∨ I.IsFree u) := by
  simp [stepsN, mem_nbrs, isFreeB_iff]

theorem mem_stepsG (p u v : Cell) :
    u ∈ stepsG I p v ↔ (u = p ∨ I.IsFree u) ∧ I.GridAdj u v := by
  simp only [stepsG, List.mem_filter, mem_stepsN, Bool.and_eq_true, isOpenB_iff,
    Instance.GridAdj]
  tauto

theorem step_src_mem {p : Cell} (hp : p ∈ I.ports) {u : Cell} (h : u = p ∨ I.IsFree u) :
    u ∈ cells I := by
  rw [mem_cells]
  rcases h with rfl | h
  · exact I.ports_inBounds u hp
  · exact h.1

/-- The grid variables are exact: `g(p, t, v)` holds iff `v` is within grid distance `t`
of `p`. -/
theorem grid_reach {p : Cell} (hp : p ∈ I.ports) (hinit : Sat a (initClauses I p))
    (hreach : Sat a (reachClauses I p)) :
    ∀ t, t ≤ I.W * I.H → ∀ v ∈ cells I,
      (a (vGrid p t v) = true ↔ I.reach I.GridAdj p t v) := by
  intro t
  induction t with
  | zero =>
    intro _ v hv
    have h := (sat_initClauses I a p).mp hinit v hv
    show _ ↔ v = p
    by_cases hvp : v = p
    · exact ⟨fun _ => hvp, fun _ => h.1 hvp⟩
    · simp [(h.2 hvp).1, hvp]
  | succ t ih =>
    intro ht v hv
    have hstep := ((sat_stepClauses I a p t v).mp
      ((sat_reachClauses I a p).mp hreach t (by omega) v hv)).1
    rw [hstep]
    show _ ↔ (I.reach I.GridAdj p t v ∨
      ∃ u, I.reach I.GridAdj p t u ∧ (u = p ∨ I.IsFree u) ∧ I.GridAdj u v)
    rw [ih (by omega) v hv]
    apply or_congr_right
    constructor
    · rintro ⟨u, hu, hg⟩
      rw [mem_stepsG] at hu
      exact ⟨u, (ih (by omega) u (step_src_mem I hp hu.1)).mp hg, hu.1, hu.2⟩
    · rintro ⟨u, hr, hok, hadj⟩
      exact ⟨u, (mem_stepsG I p u v).mpr ⟨hok, hadj⟩,
        (ih (by omega) u (step_src_mem I hp hok)).mpr hr⟩

/-- The network variables are sound: `r(p, t, v)` implies that `v` is within network
distance `t` of `p`. -/
theorem net_reach (hE : Sat a (edgeClauses I)) {p : Cell} (hp : p ∈ I.ports)
    (hinit : Sat a (initClauses I p)) (hreach : Sat a (reachClauses I p)) :
    ∀ t, t ≤ I.W * I.H → ∀ v ∈ cells I,
      a (vNet p t v) = true → I.reach (EAdj I a) p t v := by
  intro t
  induction t with
  | zero =>
    intro _ v hv hn
    have h := (sat_initClauses I a p).mp hinit v hv
    show v = p
    by_contra hvp
    rw [(h.2 hvp).2] at hn
    exact absurd hn (by simp)
  | succ t ih =>
    intro ht v hv hn
    have hstep := ((sat_stepClauses I a p t v).mp
      ((sat_reachClauses I a p).mp hreach t (by omega) v hv)).2
    rcases hstep.1 hn with h | ⟨u, hu, hs⟩
    · exact Or.inl (ih (by omega) v hv h)
    · obtain ⟨hnu, he⟩ := hstep.2 u hu hs
      rw [mem_stepsN] at hu
      have hu' := step_src_mem I hp hu.2
      have hopen := (edge_facts I a hE hu.1 ((mem_cells I u).mp hu') ((mem_cells I v).mp hv) he).1
      exact Or.inr ⟨u, ih (by omega) u hu' hnu, hu.2, hu.1, hopen.1, hopen.2, he⟩

end TrainNetwork.Answer
