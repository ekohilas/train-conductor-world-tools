/-
Running time of `toK`: every generator is charged at least its output size, and the
total charge is polynomial.
-/
import TrainNetwork.BlockSize

namespace TrainNetwork.Answer

open TrainNetwork TimeM

/-- A generator of clauses is honest when it is charged at least its output size. -/
def Hon (m : TimeM (List Clause)) : Prop := wsize m.val ≤ m.time

theorem hon_good {m : TimeM (List Clause)} (h : Hon m) : m.val.length ≤ m.time :=
  le_trans (length_le_wsize _) h

theorem hon_block (c : ℕ) (φ : List Clause) : Hon (block c φ) := block_wsize c φ

theorem hon_forL {α : Type} (l : List α) (f : α → TimeM (List Clause))
    (h : ∀ a ∈ l, Hon (f a)) : Hon (forL l f) := forL_wsize l f h

theorem hon_appendM {a b : TimeM (List Clause)} (ha : Hon a) (hb : Hon b) :
    Hon (appendM a b) := by
  unfold Hon at *
  rw [appendM_time, appendM_val, wsize_append]
  omega

theorem hon_bind {α : Type} (a : TimeM α) (f : α → TimeM (List Clause))
    (h : Hon (f a.val)) : Hon (a >>= f) := by
  unfold Hon at *
  rw [bind_val, bind_time]
  omega

theorem hon_counterM (cv : ℕ → ℕ → ℕ) (B : ℕ) :
    ∀ (items : List (List Lit)) (i : ℕ), Hon (counterM cv B i items) := by
  intro items
  induction items with
  | nil => intro i; exact hon_block _ _
  | cons it rest ih =>
    intro i
    have h1 : Hon (forL (List.range (B + 1)) fun j =>
        block 8 [[(cv i j, false), (cv (i + 1) j, true)],
          if j = 0 then negLits it ++ [(cv (i + 1) 0, true)]
          else negLits it ++ [(cv i (j - 1), false), (cv (i + 1) j, true)]]) :=
      hon_forL _ _ fun j _ => hon_block _ _
    have h2 := ih (i + 1)
    unfold Hon at *
    simp only [counterM, rangeM, bind_val, bind_time, ret_val, ret_time, pure_val, pure_time,
      tick_time, tickN_time, wsize_append]
    omega

theorem hon_edgeM (I : Instance) (cs : List Cell) : Hon (edgeM I cs) :=
  hon_forL _ _ fun _ _ => hon_block _ _

theorem hon_initM (cs : List Cell) (p : Cell) : Hon (initM cs p) :=
  hon_forL _ _ fun _ _ => hon_block _ _

theorem hon_reachM (I : Instance) (cs : List Cell) (p : Cell) : Hon (reachM I cs p) :=
  hon_bind _ _ (hon_forL _ _ fun _ _ => hon_forL _ _ fun _ _ => hon_block _ _)

theorem hon_finM (I : Instance) (cl : List Cell) (p : Cell) : Hon (finM I cl p) :=
  hon_forL _ _ fun _ _ => hon_block _ _

theorem hon_nearM (I : Instance) (cl : List Cell) (p : Cell) : Hon (nearM I cl p) :=
  hon_bind _ _ (hon_forL _ _ fun _ _ => hon_forL _ _ fun _ _ => hon_forL _ _ fun _ _ =>
    hon_block _ _)

theorem hon_cardM (I : Instance) (cl : List Cell) (p : Cell) : Hon (cardM I cl p) :=
  hon_bind _ _ (hon_bind _ _ (hon_bind _ _
    (hon_appendM (hon_counterM _ _ _ _) (hon_counterM _ _ _ _))))

theorem hon_portM (I : Instance) (cs cl : List Cell) (p : Cell) : Hon (portM I cs cl p) :=
  hon_appendM (hon_initM cs p) (hon_appendM (hon_reachM I cs p) (hon_appendM (hon_finM I cl p)
    (hon_appendM (hon_nearM I cl p) (hon_cardM I cl p))))

theorem hon_toKgen (I : Instance) (X K : ℕ) : Hon (toKgen I X K) := by
  have h1 := hon_edgeM I (cellsM I).val
  have h2 := hon_forL (filterM (cellsM I).val I.ports).val
    (portM I (cellsM I).val (filterM (cellsM I).val I.cities).val)
    (fun p _ => hon_portM I _ _ p)
  have h3 := hon_counterM (vCount (Nat.pair 2 0)) X
    (excessItemsM I (filterM (cellsM I).val I.ports).val
      (filterM (cellsM I).val I.cities).val).val 0
  have h4 := hon_counterM (vCount (Nat.pair 3 0)) K (tileItemsM (cellsM I).val).val 0
  unfold Hon at *
  simp only [toKgen, bind_val, bind_time, pure_val, pure_time, tickN_time, wsize_append]
  omega

/-- The output of `toK` is no larger than its running time. -/
theorem toK_size_le_time (I : Instance) (X K : ℕ) :
    (toK I X K).val.size ≤ (toK I X K).time := by
  have h := hon_toKgen I X K
  unfold Hon at h
  simp only [toK, bind_val, bind_time, pure_val, pure_time]
  unfold KInstance.size
  exact le_trans h (by omega)

/-! ### Time bounds -/

theorem Q_pos (M : ℕ) : 1 ≤ Q M := by unfold Q; omega

theorem good_block (c : ℕ) (φ : List Clause) : (block c φ).val.length ≤ (block c φ).time :=
  hon_good (hon_block c φ)

theorem pos4 {n B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) : 1 ≤ 4 * n * B :=
  Nat.mul_pos (Nat.mul_pos (by norm_num) hn) hB

section time
variable (I : Instance) {n M : ℕ} (hn : 1 ≤ n) (hM : 3 ≤ M)
include hn hM

theorem edgeM_time (cs : List Cell) (hcs : cs.length ≤ n)
    (hcsB : ∀ v ∈ cs, v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M) : (edgeM I cs).time ≤ 4 * n * Q M :=
  forL_time_le' cs _ n (Q M) hcs hn (Q_pos M)
    (fun v hv => edge_block_le I hM v (hcsB v hv)) (fun _ _ => good_block _ _)

theorem initM_time (cs : List Cell) (p : Cell) (hcs : cs.length ≤ n)
    (hcsB : ∀ v ∈ cs, v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M) (hp : CellB M p) :
    (initM cs p).time ≤ 4 * n * Q M :=
  forL_time_le' cs _ n (Q M) hcs hn (Q_pos M)
    (fun v hv => init_block_le hM hp
      ⟨by have := hcsB v hv; omega, by have := hcsB v hv; omega⟩)
    (fun _ _ => good_block _ _)

theorem reachM_time (cs : List Cell) (p : Cell) (hcs : cs.length ≤ n)
    (hcsB : ∀ v ∈ cs, v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M) (hp : CellB M p)
    (hT : I.W * I.H + 1 ≤ n) (hTM : I.W * I.H ≤ M) :
    (reachM I cs p).time ≤ n + 4 * n * (4 * n * Q M) := by
  simp only [reachM, rangeM, bind_time, ret_time, ret_val]
  refine Nat.add_le_add hT (forL_time_le' _ _ n _ (by simp; omega) hn (pos4 hn (Q_pos M))
    (fun t ht => forL_time_le' cs _ n (Q M) hcs hn (Q_pos M)
      (fun v hv => step_block_le I hM hp (hcsB v hv) (by rw [List.mem_range] at ht; omega))
      (fun _ _ => good_block _ _))
    (fun _ _ => hon_good (hon_forL _ _ fun _ _ => hon_block _ _)))

theorem finM_time (cl : List Cell) (p : Cell) (hcl : cl.length ≤ n)
    (hclB : ∀ c ∈ cl, CellB M c) (hp : CellB M p) (hTM : I.W * I.H ≤ M) :
    (finM I cl p).time ≤ 4 * n * Q M :=
  forL_time_le' cl _ n (Q M) hcl hn (Q_pos M)
    (fun c hc => fin_block_le I hM hp (hclB c hc) hTM) (fun _ _ => good_block _ _)

theorem nearM_time (cl : List Cell) (p : Cell) (hcl : cl.length ≤ n)
    (hclB : ∀ c ∈ cl, CellB M c) (hp : CellB M p)
    (hT : I.W * I.H + 1 ≤ n) (hTM : I.W * I.H ≤ M) :
    (nearM I cl p).time ≤ (n + 1) + 4 * n * (4 * n * (4 * n * Q M)) := by
  simp only [nearM, rangeM, bind_time, ret_time, ret_val]
  refine Nat.add_le_add (by omega) (forL_time_le' cl _ n _ hcl hn
    (pos4 hn (pos4 hn (Q_pos M)))
    (fun c hc => forL_time_le' cl _ n _ hcl hn (pos4 hn (Q_pos M))
      (fun c2 hc2 => forL_time_le' _ _ n (Q M) (by simp; omega) hn (Q_pos M)
        (fun t ht => near_block_le hM hp (hclB c hc) (hclB c2 hc2)
          (by rw [List.mem_range] at ht; omega))
        (fun _ _ => good_block _ _))
      (fun _ _ => hon_good (hon_forL _ _ fun _ _ => hon_block _ _)))
    (fun _ _ => hon_good (hon_forL _ _ fun _ _ => hon_forL _ _ fun _ _ => hon_block _ _)))

omit hM in
theorem counterM_time (cv : ℕ → ℕ → ℕ) (B : ℕ) (hB : B + 1 ≤ n) :
    ∀ (items : List (List Lit)) (i : ℕ),
      (∀ it ∈ items, it.length ≤ 3 ∧ ∀ l ∈ it, Nat.size l.1 ≤ 32 * M) →
      (∀ i' j', i' ≤ i + items.length → j' ≤ B → Nat.size (cv i' j') ≤ 32 * M) →
      (counterM cv B i items).time ≤ items.length * (11 * n * Q M) + Q M := by
  intro items
  induction items with
  | nil =>
    intro i _ hcv
    have := counter_final_block_le cv i B (hcv i B (by simp) le_rfl)
    simpa [counterM] using this
  | cons it rest ih =>
    intro i hit hcv
    have hx := forL_time_le' (List.range (B + 1)) (fun j =>
        block 8 [[(cv i j, false), (cv (i + 1) j, true)],
          if j = 0 then negLits it ++ [(cv (i + 1) 0, true)]
          else negLits it ++ [(cv i (j - 1), false), (cv (i + 1) j, true)]]) n (Q M)
      (by simpa using hB) hn (Q_pos M)
      (fun j hj => counter_step_block_le cv i j it (hit it (by simp))
        (fun i' j' hi hj' => hcv i' j' (by simp; omega)
          (by rw [List.mem_range] at hj; omega)))
      (fun _ _ => good_block _ _)
    have hxl := forL_len_le_time (List.range (B + 1)) (fun j =>
        block 8 [[(cv i j, false), (cv (i + 1) j, true)],
          if j = 0 then negLits it ++ [(cv (i + 1) 0, true)]
          else negLits it ++ [(cv i (j - 1), false), (cv (i + 1) j, true)]])
      (fun _ _ => good_block _ _)
    have ih' := ih (i + 1) (fun it' h => hit it' (by simp [h]))
      (fun i' j' hi hj => hcv i' j' (by simp; omega) hj)
    have h1 : n ≤ n * Q M := Nat.le_mul_of_pos_right n (Q_pos M)
    have h2 : 1 ≤ n * Q M := Nat.mul_pos hn (Q_pos M)
    simp only [counterM, rangeM, bind_time, ret_time, ret_val, tick_time, tickN_time,
      pure_time, List.length_cons]
    nlinarith [hx, hxl, ih', h1, h2, hB]

omit hM in
theorem selItemsM_time (cl : List Cell) (p : Cell) (b : Bool) (hcl : cl.length ≤ n) :
    (selItemsM cl p b).time ≤ 4 * n * 32 :=
  forL_time_le' cl _ n 32 hcl hn (by norm_num) (fun _ _ => by simp) (fun _ _ => by simp)

omit hn hM in
theorem selItemsM_len (cl : List Cell) (p : Cell) (b : Bool) :
    (selItemsM cl p b).val.length ≤ cl.length := by
  have := forL_len_le_mul cl (fun c => ret 32 [[(vSel p c, b)]]) 1 (fun _ _ => by simp)
  simpa [selItemsM] using this

omit hn in
theorem selItemsM_items (cl : List Cell) (p : Cell) (b : Bool) (hp : CellB M p)
    (hclB : ∀ c ∈ cl, CellB M c) :
    ∀ it ∈ (selItemsM cl p b).val, it.length ≤ 3 ∧ ∀ l ∈ it, Nat.size l.1 ≤ 32 * M := by
  intro it hit
  simp only [selItemsM, forL_val, ret_val, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hit
  obtain ⟨c, hc, rfl⟩ := hit
  refine ⟨by simp, ?_⟩
  intro l hl
  simp at hl
  subst hl
  exact sz_vSel hM hp (hclB c hc)

/-- Bound for a counter over at most `n` items. -/
def bCnt (n q : ℕ) : ℕ := n * (11 * n * q) + q

def bCard (n q : ℕ) : ℕ := 4 * n * 32 + (4 * n * 32 + ((n + 2) + (2 * bCnt n q + bCnt n q)))

def bPort (n q : ℕ) : ℕ :=
  2 * (4 * n * q) + (2 * (n + 4 * n * (4 * n * q)) + (2 * (4 * n * q) +
    (2 * ((n + 1) + 4 * n * (4 * n * (4 * n * q))) + bCard n q)))

theorem cardM_time (cl : List Cell) (p : Cell) (hcl : cl.length + 1 ≤ n)
    (hclB : ∀ c ∈ cl, CellB M c) (hp : CellB M p) (hk : I.k + 1 ≤ n) (hnM : n ≤ M) :
    (cardM I cl p).time ≤ bCard n (Q M) := by
  have t1 := selItemsM_time hn cl p true (by omega)
  have t0 := selItemsM_time hn cl p false (by omega)
  have l1 := selItemsM_len cl p true
  have l0 := selItemsM_len cl p false
  have c1 := counterM_time hn (M := M) (vCount (Nat.pair 0 (cellCode p))) I.k hk
    (selItemsM cl p true).val 0 (selItemsM_items hM cl p true hp hclB)
    (fun i' j' hi hj => sz_vCount hM (sz_tag hM (by norm_num) hp) (by omega) (by omega))
  have c0 := counterM_time hn (M := M) (vCount (Nat.pair 1 (cellCode p))) (cl.length - I.k)
    (by omega) (selItemsM cl p false).val 0 (selItemsM_items hM cl p false hp hclB)
    (fun i' j' hi hj => sz_vCount hM (sz_tag hM (by norm_num) hp) (by omega) (by omega))
  have g1 := hon_good (hon_counterM (vCount (Nat.pair 0 (cellCode p))) I.k
    (selItemsM cl p true).val 0)
  have m1 : (selItemsM cl p true).val.length * (11 * n * Q M) ≤ n * (11 * n * Q M) :=
    Nat.mul_le_mul_right _ (by omega)
  have m0 : (selItemsM cl p false).val.length * (11 * n * Q M) ≤ n * (11 * n * Q M) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [cardM, bind_time, ret_time, ret_val, appendM_time]
  unfold bCard bCnt
  omega

theorem portM_time (cs cl : List Cell) (p : Cell) (hcs : cs.length + 1 ≤ n)
    (hcsB : ∀ v ∈ cs, v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M) (hcl : cl.length + 1 ≤ n)
    (hclB : ∀ c ∈ cl, CellB M c) (hp : CellB M p) (hk : I.k + 1 ≤ n) (hnM : n ≤ M)
    (hT : I.W * I.H + 1 ≤ n) (hTM : I.W * I.H ≤ M) :
    (portM I cs cl p).time ≤ bPort n (Q M) := by
  have a1 := initM_time hn hM cs p (by omega) hcsB hp
  have a2 := reachM_time I hn hM cs p (by omega) hcsB hp hT hTM
  have a3 := finM_time I hn hM cl p (by omega) hclB hp hTM
  have a4 := nearM_time I hn hM cl p (by omega) hclB hp hT hTM
  have a5 := cardM_time I hn hM cl p hcl hclB hp hk hnM
  have g1 := hon_good (hon_initM cs p)
  have g2 := hon_good (hon_reachM I cs p)
  have g3 := hon_good (hon_finM I cl p)
  have g4 := hon_good (hon_nearM I cl p)
  simp only [portM, appendM_time]
  unfold bPort
  omega

omit hM in
theorem one_le_bPort (q : ℕ) (hq : 1 ≤ q) : 1 ≤ bPort n q := by
  have := pos4 hn hq
  unfold bPort
  omega

omit hM in
theorem excessItemsM_time (pl cl : List Cell) (hpl : pl.length ≤ n) (hcl : cl.length ≤ n)
    (hT : I.W * I.H + 1 ≤ n) :
    (excessItemsM I pl cl).time ≤ n + 4 * n * (4 * n * (4 * n * 96)) := by
  simp only [excessItemsM, rangeM, bind_time, ret_time, ret_val]
  refine Nat.add_le_add hT (forL_time_le' pl _ n _ hpl hn
    (pos4 hn (pos4 hn (by norm_num)))
    (fun p _ => forL_time_le' cl _ n _ hcl hn (pos4 hn (by norm_num))
      (fun c _ => forL_time_le' _ _ n 96 (by simp; omega) hn (by norm_num)
        (fun _ _ => by simp) (fun _ _ => by simp))
      (fun _ _ => forL_len_le_time _ _ (fun _ _ => by simp)))
    (fun _ _ => forL_len_le_time _ _ (fun _ _ => forL_len_le_time _ _ (fun _ _ => by simp))))

omit hn hM in
theorem excessItemsM_len (pl cl : List Cell) (hpl : pl.length ≤ n) (hcl : cl.length ≤ n)
    (hT : I.W * I.H + 1 ≤ n) :
    (excessItemsM I pl cl).val.length ≤ n * (n * (n * 1)) := by
  simp only [excessItemsM, rangeM, bind_val, ret_val]
  refine le_trans (forL_len_le_mul pl _ (n * (n * 1)) (fun p _ =>
    le_trans (forL_len_le_mul cl _ (n * 1) (fun c _ =>
      le_trans (forL_len_le_mul _ _ 1 (fun _ _ => by simp))
        (Nat.mul_le_mul_right _ (by simp; omega))))
      (Nat.mul_le_mul_right _ hcl))) (Nat.mul_le_mul_right _ hpl)

omit hn in
theorem excessItemsM_items (pl cl : List Cell) (hplB : ∀ p ∈ pl, CellB M p)
    (hclB : ∀ c ∈ cl, CellB M c) (hTM : I.W * I.H ≤ M) :
    ∀ it ∈ (excessItemsM I pl cl).val,
      it.length ≤ 3 ∧ ∀ l ∈ it, Nat.size l.1 ≤ 32 * M := by
  intro it hit
  simp only [excessItemsM, rangeM, bind_val, ret_val, forL_val, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range] at hit
  obtain ⟨p, hp, c, hc, t, ht, rfl⟩ := hit
  refine ⟨by simp, ?_⟩
  intro l hl
  simp at hl
  rcases hl with rfl | rfl | rfl
  · exact sz_vSel hM (hplB p hp) (hclB c hc)
  · exact sz_vGrid hM (hplB p hp) (by omega) (hclB c hc)
  · exact sz_vNet hM (hplB p hp) (by omega) (hclB c hc)

omit hM in
theorem tileItemsM_time (cs : List Cell) (hcs : cs.length ≤ n) :
    (tileItemsM cs).time ≤ 4 * n * 32 :=
  forL_time_le' cs _ n 32 hcs hn (by norm_num) (fun _ _ => by simp) (fun _ _ => by simp)

omit hn hM in
theorem tileItemsM_len (cs : List Cell) : (tileItemsM cs).val.length ≤ cs.length := by
  have := forL_len_le_mul cs (fun x => ret 32 [[(vTile x, true)]]) 1 (fun _ _ => by simp)
  simpa [tileItemsM] using this

omit hn in
theorem tileItemsM_items (cs : List Cell) (hcsB : ∀ v ∈ cs, CellB M v) :
    ∀ it ∈ (tileItemsM cs).val, it.length ≤ 3 ∧ ∀ l ∈ it, Nat.size l.1 ≤ 32 * M := by
  intro it hit
  simp only [tileItemsM, forL_val, ret_val, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hit
  obtain ⟨x, hx, rfl⟩ := hit
  refine ⟨by simp, ?_⟩
  intro l hl
  simp at hl
  subst hl
  exact sz_vTile hM (hcsB x hx)

omit hM in
theorem cellsM_time (hW : I.W ≤ n) (hH : I.H ≤ n) :
    (cellsM I).time ≤ (n + 1) + ((n + 1) + 4 * n * (4 * n * 1)) := by
  simp only [cellsM, rangeM, bind_time, ret_time, ret_val]
  refine Nat.add_le_add (by omega) (Nat.add_le_add (by omega)
    (forL_time_le' _ _ n _ (by simpa using hW) hn (pos4 hn le_rfl)
      (fun x _ => forL_time_le' _ _ n 1 (by simpa using hH) hn le_rfl
        (fun _ _ => by simp) (fun _ _ => by simp))
      (fun _ _ => forL_len_le_time _ _ (fun _ _ => by simp))))

omit hM in
theorem filterM_time (l : List Cell) (s : Finset Cell) (hl : l.length ≤ n) :
    (filterM l s).time ≤ 4 * n * 1 :=
  forL_time_le' l _ n 1 hl hn le_rfl (fun _ _ => by simp)
    (fun c _ => by simp only [ret_val, ret_time]; split_ifs <;> simp)

end time

theorem inst_pos (I : Instance) : 1 ≤ I.W ∧ 1 ≤ I.H := by
  have h := lt_of_lt_of_le I.k_pos I.k_le_cities
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h
  have := I.cities_inBounds c hc
  omega

theorem cells_length (I : Instance) : (cells I).length = I.W * I.H := by
  unfold cells
  rw [List.length_product, List.length_range, List.length_range]

/-- The raw sum of the bounds of all parts of `toKgen`. -/
def bRaw (n q : ℕ) : ℕ :=
  (2 * n + 2 + 4 * n * (4 * n * 1)) + 2 * (4 * n * 1) + 4 * (4 * n * q) +
    3 * (4 * n * bPort n q) + (n + 4 * n * (4 * n * (4 * n * 96))) +
    2 * (n * (n * (n * 1)) * (11 * n * q) + q) + 4 * n * 32 + (n * (11 * n * q) + q)

theorem bRaw_le (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) : bRaw n q ≤ 13000 * n ^ 4 * q := by
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  have hn4 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
  have p1 : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
  have p2 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by norm_num)
  have p3 : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by norm_num)
  have f0 : 1 ≤ n ^ 4 * q := Nat.mul_pos hn4 hq
  have f1 : n ≤ n ^ 4 * q := le_trans p1 (Nat.le_mul_of_pos_right _ hq)
  have f2 : n ^ 2 ≤ n ^ 4 * q := le_trans p2 (Nat.le_mul_of_pos_right _ hq)
  have f3 : n ^ 3 ≤ n ^ 4 * q := le_trans p3 (Nat.le_mul_of_pos_right _ hq)
  have g0 : q ≤ n ^ 4 * q := Nat.le_mul_of_pos_left _ hn4
  have g1 : n * q ≤ n ^ 4 * q := Nat.mul_le_mul_right _ p1
  have g2 : n ^ 2 * q ≤ n ^ 4 * q := Nat.mul_le_mul_right _ p2
  have g3 : n ^ 3 * q ≤ n ^ 4 * q := Nat.mul_le_mul_right _ p3
  unfold bRaw bPort bCard bCnt
  nlinarith [f0, f1, f2, f3, g0, g1, g2, g3]

theorem toKgen_time_raw (I : Instance) (X K : ℕ) :
    (toKgen I X K).time ≤
      bRaw (I.W * I.H + 1 + X + K)
        (Q ((I.W * I.H + 1 + X + K) * ((I.W * I.H + 1 + X + K) *
          ((I.W * I.H + 1 + X + K) * 1)) + 3)) := by
  generalize hn_def : I.W * I.H + 1 + X + K = n
  have hn : 1 ≤ n := by omega
  generalize hM_def : n * (n * (n * 1)) + 3 = M
  have hM : 3 ≤ M := by omega
  obtain ⟨hW1, hH1⟩ := inst_pos I
  have hWN : I.W ≤ I.W * I.H := Nat.le_mul_of_pos_right _ hH1
  have hHN : I.H ≤ I.W * I.H := Nat.le_mul_of_pos_left _ hW1
  have hn3 : n ≤ n * (n * (n * 1)) := by
    have h1 : n * 1 ≤ n * (n * 1) := Nat.le_mul_of_pos_left _ hn
    have h2 : n * (n * 1) ≤ n * (n * (n * 1)) := Nat.mul_le_mul_left _ h1
    omega
  have hnM : n ≤ M := by omega
  have hcl := cells_length I
  have hcsB : ∀ v ∈ cells I, v.1 + 1 ≤ M ∧ v.2 + 1 ≤ M := by
    intro v hv
    rw [mem_cells] at hv
    obtain ⟨h1, h2⟩ := hv
    omega
  have hcsB' : ∀ v ∈ cells I, CellB M v := fun v hv =>
    ⟨by have := hcsB v hv; omega, by have := hcsB v hv; omega⟩
  have hpl : (portL I).length ≤ I.W * I.H := by
    rw [← hcl]; exact List.length_filter_le _ _
  have hcil : (cityL I).length ≤ I.W * I.H := by
    rw [← hcl]; exact List.length_filter_le _ _
  have hplB : ∀ p ∈ portL I, CellB M p := fun p hp => hcsB' p (List.mem_of_mem_filter hp)
  have hclB : ∀ c ∈ cityL I, CellB M c := fun c hc => hcsB' c (List.mem_of_mem_filter hc)
  have hk : I.k + 1 ≤ n := by
    have := I.k_le_cities
    rw [← cityL_length] at this
    omega
  have hp : (filterM (cells I) I.ports).val = portL I := by rw [filterM_val]; rfl
  have hc : (filterM (cells I) I.cities).val = cityL I := by rw [filterM_val]; rfl
  have b1 := cellsM_time I hn (by omega : I.W ≤ n) (by omega : I.H ≤ n)
  have b2 := filterM_time hn (cells I) I.ports (by omega)
  have b3 := filterM_time hn (cells I) I.cities (by omega)
  have b4 := edgeM_time I hn hM (cells I) (by omega) hcsB
  have b5 := forL_time_le' (portL I) (portM I (cells I) (cityL I)) n (bPort n (Q M))
    (by omega) hn (one_le_bPort hn _ (Q_pos M))
    (fun p hp => portM_time I hn hM (cells I) (cityL I) p (by omega) hcsB (by omega) hclB
      (hplB p hp) hk hnM (by omega) (by omega))
    (fun p _ => hon_good (hon_portM I _ _ p))
  have b6 := excessItemsM_time I hn (portL I) (cityL I) (by omega) (by omega) (by omega)
  have l6 := excessItemsM_len I (n := n) (portL I) (cityL I) (by omega) (by omega) (by omega)
  have htag : ∀ g : ℕ, g ≤ 3 → Nat.size (Nat.pair g 0) ≤ 4 * M := fun g hg =>
    sz_pair' (m := 2 * M) (sz_atom (by omega)) (sz_atom (by omega)) (by omega)
  have b7 := counterM_time hn (M := M) (vCount (Nat.pair 2 0)) X (by omega)
    (excessItemsM I (portL I) (cityL I)).val 0
    (excessItemsM_items I hM _ _ hplB hclB (by omega))
    (fun i' j' hi hj => sz_vCount hM (htag 2 (by norm_num)) (by omega) (by omega))
  have b8 := tileItemsM_time hn (cells I) (by omega)
  have l8 := tileItemsM_len (cells I)
  have b9 := counterM_time hn (M := M) (vCount (Nat.pair 3 0)) K (by omega)
    (tileItemsM (cells I)).val 0 (tileItemsM_items hM _ hcsB')
    (fun i' j' hi hj => sz_vCount hM (htag 3 (by norm_num)) (by omega) (by omega))
  have g4 := hon_good (hon_edgeM I (cells I))
  have g5 := hon_good (hon_forL (portL I) (portM I (cells I) (cityL I))
    (fun p _ => hon_portM I _ _ p))
  have g7 := hon_good (hon_counterM (vCount (Nat.pair 2 0)) X
    (excessItemsM I (portL I) (cityL I)).val 0)
  have m7 : (excessItemsM I (portL I) (cityL I)).val.length * (11 * n * Q M) ≤
      n * (n * (n * 1)) * (11 * n * Q M) := Nat.mul_le_mul_right _ l6
  have m9 : (tileItemsM (cells I)).val.length * (11 * n * Q M) ≤ n * (11 * n * Q M) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [toKgen, bind_time, bind_val, pure_time, tickN_time, cellsM_val, hp, hc]
  unfold bRaw
  omega

end TrainNetwork.Answer
