/-
Generic `TimeM` building blocks: every loop iteration and every produced list cell is
charged at least one `tick`. For each combinator we prove what value it computes and an
upper bound on its running time.

Convention used throughout the development: the specification of a `TimeM` program is
its `.val`; there is no separate "pure" copy of the algorithms.
-/
import TrainNetwork.Cost

namespace TrainNetwork
namespace TimeM

variable {α β : Type}

/-- Map `f` over a list: one tick per element, plus the cost of `f`. -/
def tmapM (f : α → TimeM β) : List α → TimeM (List β)
  | [] => pure []
  | a :: l => do
      tick
      let b ← f a
      let bs ← tmapM f l
      pure (b :: bs)

@[simp] theorem tmapM_val (f : α → TimeM β) (l : List α) :
    (tmapM f l).val = l.map (fun a => (f a).val) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [tmapM, ih]

theorem tmapM_time_le (f : α → TimeM β) (l : List α) (c : ℕ)
    (h : ∀ a ∈ l, (f a).time ≤ c) : (tmapM f l).time ≤ l.length * (c + 1) := by
  induction l with
  | nil => simp [tmapM]
  | cons a l ih =>
      have h1 := h a (by simp)
      have h2 := ih (fun b hb => h b (by simp [hb]))
      simp only [tmapM, bind_time, tick_time, pure_time, List.length_cons]
      nlinarith

/-- Filter a list by a `TimeM` predicate: one tick per element, plus the cost of `p`. -/
def tfilterM (p : α → TimeM Bool) : List α → TimeM (List α)
  | [] => pure []
  | a :: l => do
      tick
      let b ← p a
      let r ← tfilterM p l
      pure (if b then a :: r else r)

@[simp] theorem tfilterM_val (p : α → TimeM Bool) (l : List α) :
    (tfilterM p l).val = l.filter (fun a => (p a).val) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [tfilterM, bind_val, pure_val, ih, List.filter_cons]

theorem tfilterM_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ)
    (h : ∀ a ∈ l, (p a).time ≤ c) : (tfilterM p l).time ≤ l.length * (c + 1) := by
  induction l with
  | nil => simp [tfilterM]
  | cons a l ih =>
      have h1 := h a (by simp)
      have h2 := ih (fun b hb => h b (by simp [hb]))
      simp only [tfilterM, bind_time, tick_time, pure_time, List.length_cons]
      nlinarith

/-- All ways of picking one element from each list (`List.sections`). One tick per
produced list cell, and the final flattening is charged at its output length. -/
def tsections : List (List α) → TimeM (List (List α))
  | [] => pure [[]]
  | l :: L => do
      tick
      let S ← tsections L
      let r ← tmapM (fun s => tmapM (fun a => pure (a :: s)) l) S
      tickN (S.length * l.length)
      pure r.flatten

@[simp] theorem tsections_val (L : List (List α)) : (tsections L).val = L.sections := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      simp [tsections, ih, List.sections, List.flatMap_def]

/-- `∏ (|l| + 1)` over the lists of `L`; a convenient upper bound for `|sections L|`. -/
def prodSucc (L : List (List α)) : ℕ := (L.map (fun l => l.length + 1)).prod

theorem prodSucc_pos (L : List (List α)) : 0 < prodSucc L := by
  induction L with
  | nil => simp [prodSucc]
  | cons l L ih => simp only [prodSucc, List.map_cons, List.prod_cons] at *; positivity

theorem length_sections_le (L : List (List α)) : L.sections.length ≤ prodSucc L := by
  induction L with
  | nil => simp [prodSucc, List.sections]
  | cons l L ih =>
      have : (l :: L).sections.length = L.sections.length * l.length := by
        simp [List.sections, List.length_flatMap, List.map_const', List.sum_replicate]
      rw [this]
      simp only [prodSucc, List.map_cons, List.prod_cons] at *
      nlinarith

theorem tsections_time_le (L : List (List α)) :
    (tsections L).time ≤ 3 * L.length * prodSucc L := by
  induction L with
  | nil => simp [tsections]
  | cons l L ih =>
      have hS := length_sections_le L
      have hpos := prodSucc_pos L
      have hinner : ∀ s ∈ L.sections,
          (tmapM (fun a => (pure (a :: s) : TimeM (List α))) l).time ≤ l.length := by
        intro s _
        have := tmapM_time_le (fun a => (pure (a :: s) : TimeM (List α))) l 0 (by simp)
        simpa using this
      have hmap := tmapM_time_le (fun s => tmapM (fun a => (pure (a :: s) : TimeM (List α))) l)
        L.sections l.length hinner
      simp only [tsections, bind_time, tick_time, pure_time, tickN_time, tsections_val,
        List.length_cons]
      have hP : prodSucc (l :: L) = (l.length + 1) * prodSucc L := by
        simp [prodSucc]
      rw [hP]
      nlinarith

/-- All sublists (`List.sublists'`): one tick per produced list, appends charged at the
length of the left operand. -/
def tsublists : List α → TimeM (List (List α))
  | [] => pure [[]]
  | a :: l => do
      tick
      let S ← tsublists l
      let S' ← tmapM (fun s => pure (a :: s)) S
      tickN (S.length + 1)
      pure (S ++ S')

@[simp] theorem tsublists_val (l : List α) : (tsublists l).val = l.sublists' := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [tsublists, ih, List.sublists'_cons]

theorem tsublists_time_le (l : List α) : (tsublists l).time ≤ 4 * 2 ^ l.length := by
  induction l with
  | nil => simp [tsublists]
  | cons a l ih =>
      have hmap := tmapM_time_le (fun s => (pure (a :: s) : TimeM (List α))) l.sublists' 0
        (by simp)
      have hlen : l.sublists'.length = 2 ^ l.length := List.length_sublists' l
      have hpos : 0 < 2 ^ l.length := by positivity
      simp only [tsublists, bind_time, tick_time, pure_time, tickN_time, tsublists_val,
        List.length_cons, pow_succ]
      rw [hlen] at hmap ⊢
      omega

/-- Association-list lookup keyed by cells: three ticks per visited entry (two `ℕ`
comparisons and one list step). -/
def tlookup (x : Cell) : List (Cell × β) → TimeM (Option β)
  | [] => pure none
  | (y, v) :: l => do
      tickN 3
      if x = y then pure (some v) else tlookup x l

theorem tlookup_some {x : Cell} {l : List (Cell × β)} {v : β}
    (h : (tlookup x l).val = some v) : (x, v) ∈ l := by
  induction l with
  | nil => simp [tlookup] at h
  | cons e l ih =>
      obtain ⟨y, u⟩ := e
      by_cases hxy : x = y
      · simp [tlookup, hxy] at h
        simp [hxy, h]
      · simp only [tlookup, bind_val, hxy, ↓reduceIte] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem tlookup_none {x : Cell} {l : List (Cell × β)}
    (h : (tlookup x l).val = none) (v : β) : (x, v) ∉ l := by
  induction l with
  | nil => simp
  | cons e l ih =>
      obtain ⟨y, u⟩ := e
      by_cases hxy : x = y
      · simp [tlookup, hxy] at h
      · simp only [tlookup, bind_val, hxy, ↓reduceIte] at h
        intro hmem
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact hxy (by simpa using congrArg Prod.fst h1)
        · exact ih h h1

theorem tlookup_of_mem {x : Cell} {l : List (Cell × β)} {v : β}
    (hnd : (l.map Prod.fst).Nodup) (h : (x, v) ∈ l) : (tlookup x l).val = some v := by
  cases hres : (tlookup x l).val with
  | none => exact absurd h (tlookup_none hres v)
  | some u =>
      have hu := tlookup_some hres
      have : u = v := by
        by_contra hne
        have := List.inj_on_of_nodup_map hnd hu h rfl
        exact hne (by simpa using congrArg Prod.snd this)
      rw [this]

theorem tlookup_time_le (x : Cell) (l : List (Cell × β)) :
    (tlookup x l).time ≤ 3 * l.length := by
  induction l with
  | nil => simp [tlookup]
  | cons e l ih =>
      obtain ⟨y, u⟩ := e
      by_cases hxy : x = y
      · simp [tlookup, hxy]
      · simp only [tlookup, bind_time, tickN_time, hxy, ↓reduceIte, List.length_cons]
        omega

end TimeM
end TrainNetwork
