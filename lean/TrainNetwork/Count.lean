/-
Small counting lemmas used on both sides of the correctness proof.
-/
import TrainNetwork.Formula

namespace TrainNetwork.Answer

open TrainNetwork

theorem countP_range_eq_card (q : ℕ → Bool) (T : ℕ) :
    (List.range T).countP q = (((List.range T).filter q).toFinset).card := by
  rw [List.countP_eq_length_filter,
    List.toFinset_card_of_nodup (List.nodup_range.filter _)]

/-- If `q` holds on `[d, n)` and `n ≤ T`, then it holds at least `n - d` times below `T`. -/
theorem le_countP_range (q : ℕ → Bool) (d n T : ℕ) (hn : n ≤ T)
    (hq : ∀ t, d ≤ t → t < n → q t = true) : n - d ≤ (List.range T).countP q := by
  rw [countP_range_eq_card, ← Nat.card_Ico d n]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_Ico] at ht
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
  exact ⟨by omega, hq t ht.1 ht.2⟩

/-- If `q` holds only on `[d, n)`, then it holds at most `n - d` times. -/
theorem countP_range_le (q : ℕ → Bool) (d n T : ℕ)
    (hq : ∀ t, t < T → q t = true → d ≤ t ∧ t < n) : (List.range T).countP q ≤ n - d := by
  rw [countP_range_eq_card, ← Nat.card_Ico d n]
  apply Finset.card_le_card
  intro t ht
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at ht
  rw [Finset.mem_Ico]
  exact hq t ht.1 ht.2

theorem list_sum_le_cast {α : Type} (l : List α) (F : α → ℕ∞) (f : α → ℕ)
    (h : ∀ x ∈ l, F x ≤ (f x : ℕ∞)) : (l.map F).sum ≤ (((l.map f).sum : ℕ) : ℕ∞) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem cast_le_list_sum {α : Type} (l : List α) (F : α → ℕ∞) (f : α → ℕ)
    (h : ∀ x ∈ l, (f x : ℕ∞) ≤ F x) : (((l.map f).sum : ℕ) : ℕ∞) ≤ (l.map F).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

variable (I : Instance) (a : ℕ → Bool)

theorem cnt_selItems (p : Cell) (b : Bool) :
    cnt a (selItems I p b) = (cityL I).countP fun c => a (vSel p c) == b := by
  simp only [cnt, selItems, List.countP_map]
  congr 1
  funext c
  simp [iact]

theorem cnt_tileItems : cnt a (tileItems I) = (cells I).countP fun x => a (vTile x) := by
  simp only [cnt, tileItems, List.countP_map]
  congr 1
  funext c
  simp [iact]

/-- The predicate counted by the excess gadget for the pair `(p, c)` at time `t`. -/
def exPred (p c : Cell) (t : ℕ) : Bool :=
  a (vSel p c) && a (vGrid p t c) && !a (vNet p t c)

theorem cnt_excessItems :
    cnt a (excessItems I) =
      ((portL I).map fun p => ((cityL I).map fun c =>
        (List.range (I.W * I.H)).countP (exPred a p c)).sum).sum := by
  unfold cnt excessItems
  rw [List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  rw [List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp]
  rw [List.countP_map]
  congr 1
  funext t
  simp [iact, exPred, Bool.and_assoc]

/-- Sum over the ports as a list sum. -/
theorem sum_ports {M : Type} [AddCommMonoid M] (F : Cell → M) :
    ∑ p ∈ I.ports, F p = ((portL I).map F).sum := by
  rw [← portL_toFinset, List.sum_toFinset _ (nodup_portL I)]

/-- Sum over the cities as a list sum. -/
theorem sum_cities {M : Type} [AddCommMonoid M] (F : Cell → M) :
    ∑ c ∈ I.cities, F c = ((cityL I).map F).sum := by
  rw [← cityL_toFinset, List.sum_toFinset _ (nodup_cityL I)]

end TrainNetwork.Answer
