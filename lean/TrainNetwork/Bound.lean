/-
Running time and output size of `toK`: generic loop lemmas.
-/
import TrainNetwork.Gen

namespace TrainNetwork.Answer

open TrainNetwork TimeM

theorem forL_nil_time {α β : Type} (f : α → TimeM (List β)) : (forL [] f).time = 1 := rfl

theorem forL_cons_time {α β : Type} (a : α) (t : List α) (f : α → TimeM (List β)) :
    (forL (a :: t) f).time = 1 + (f a).time + (forL t f).time + (f a).val.length := by
  simp only [forL, bind_time, tick_time, tickN_time, pure_time]
  omega

/-- A loop whose body costs at most `B` and never outputs more than it costs. -/
theorem forL_time_le {α β : Type} (l : List α) (f : α → TimeM (List β)) (B : ℕ)
    (hB : ∀ a ∈ l, (f a).time ≤ B) (hg : ∀ a ∈ l, (f a).val.length ≤ (f a).time) :
    (forL l f).time ≤ l.length * (2 * B + 1) + 1 := by
  induction l with
  | nil => simp [forL_nil_time]
  | cons a t ih =>
    have h1 := hB a (by simp)
    have h2 := hg a (by simp)
    have ih' := ih (fun x hx => hB x (by simp [hx])) (fun x hx => hg x (by simp [hx]))
    rw [forL_cons_time, List.length_cons]
    have e : (t.length + 1) * (2 * B + 1) = t.length * (2 * B + 1) + (2 * B + 1) := by ring
    rw [e]
    omega

theorem forL_len_le_time {α β : Type} (l : List α) (f : α → TimeM (List β))
    (hg : ∀ a ∈ l, (f a).val.length ≤ (f a).time) :
    (forL l f).val.length ≤ (forL l f).time := by
  induction l with
  | nil => simp [forL_nil_time]
  | cons a t ih =>
    have h2 := hg a (by simp)
    have ih' := ih (fun x hx => hg x (by simp [hx]))
    rw [forL_cons_time]
    simp only [forL_val, List.flatMap_cons, List.length_append] at ih' ⊢
    omega

theorem forL_len_le_mul {α β : Type} (l : List α) (f : α → TimeM (List β)) (L : ℕ)
    (h : ∀ a ∈ l, (f a).val.length ≤ L) : (forL l f).val.length ≤ l.length * L := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h2 := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [forL_val, List.flatMap_cons, List.length_append, List.length_cons] at ih' ⊢
    have e : (t.length + 1) * L = t.length * L + L := by ring
    rw [e]
    omega

/-- The same bound with the list length replaced by an upper bound `n`. -/
theorem forL_time_le' {α β : Type} (l : List α) (f : α → TimeM (List β)) (n B : ℕ)
    (hl : l.length ≤ n) (hn : 1 ≤ n) (hB1 : 1 ≤ B)
    (hB : ∀ a ∈ l, (f a).time ≤ B) (hg : ∀ a ∈ l, (f a).val.length ≤ (f a).time) :
    (forL l f).time ≤ 4 * n * B := by
  have h := forL_time_le l f B hB hg
  have h1 : l.length * (2 * B + 1) ≤ n * (2 * B + 1) := Nat.mul_le_mul_right _ hl
  have h2 : n ≤ n * B := Nat.le_mul_of_pos_right n hB1
  have h3 : 1 ≤ n * B := Nat.mul_pos hn hB1
  have e : n * (2 * B + 1) = 2 * (n * B) + n := by ring
  have e2 : 4 * n * B = 4 * (n * B) := by ring
  rw [e2]
  omega

@[simp] theorem wsize_nil : wsize [] = 0 := rfl

@[simp] theorem wsize_append (φ ψ : List Clause) : wsize (φ ++ ψ) = wsize φ + wsize ψ := by
  simp [wsize]

theorem length_le_wsize (φ : List Clause) : φ.length ≤ wsize φ := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc : 1 ≤ clauseSize c := by unfold clauseSize; omega
    simp only [wsize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- A loop of honest generators is honest: it is charged at least its output size. -/
theorem forL_wsize {α : Type} (l : List α) (f : α → TimeM (List Clause))
    (h : ∀ a ∈ l, wsize (f a).val ≤ (f a).time) :
    wsize (forL l f).val ≤ (forL l f).time := by
  induction l with
  | nil => simp [forL_nil_time]
  | cons a t ih =>
    have h2 := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [forL_cons_time]
    simp only [forL_val, List.flatMap_cons, wsize_append] at ih' ⊢
    omega

theorem block_time (c : ℕ) (φ : List Clause) :
    (block c φ).time = c + 32 * lits φ + wsize φ := by
  simp [block]

theorem block_wsize (c : ℕ) (φ : List Clause) : wsize (block c φ).val ≤ (block c φ).time := by
  rw [block_time, block_val]; omega

theorem appendM_time {β : Type} (a b : TimeM (List β)) :
    (appendM a b).time = a.time + b.time + a.val.length := by
  simp only [appendM, bind_time, tickN_time, pure_time]
  omega

end TrainNetwork.Answer
