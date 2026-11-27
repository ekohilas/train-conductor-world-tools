/-
One run of the certificate DP on an instance: choose the sweep direction so that a layer
has `min W H` cells, enumerate labels and layer states, compute the kinds of all cells,
and run the layered DP.

`dpRun_some` / `dpRun_none` state what the run returns in terms of labellings of the
grid (`GridOK`, `gridCost`), independently of the sweep direction.
-/
import TrainNetwork.GridDP

namespace TrainNetwork

open TimeM

/-- Cell `j` of layer `i`: layers are columns if `col`, rows otherwise. -/
def emb : Bool → ℕ → ℕ → Cell
  | true, i, j => (i, j)
  | false, i, j => (j, i)

/-- Layer and position of a cell. -/
def unemb : Bool → Cell → ℕ × ℕ
  | true, x => x
  | false, x => (x.2, x.1)

/-- Number of layers. -/
def nOf : Bool → ℕ → ℕ → ℕ
  | true, W, _ => W
  | false, _, H => H

/-- Cells per layer. -/
def mOf : Bool → ℕ → ℕ → ℕ
  | true, _, H => H
  | false, W, _ => W

/-- Direction inside a layer. -/
def dWOf : Bool → Dir
  | true => .D
  | false => .R

/-- Direction to the next layer. -/
def dAOf : Bool → Dir
  | true => .R
  | false => .D

theorem layOK_emb (col : Bool) {β W H : ℕ} {K : Cell → Kind} {L : Cell → Lab} :
    LayOK β (dWOf col) (dAOf col) (nOf col W H) (mOf col W H)
      (fun i j => K (emb col i j)) (fun i j => L (emb col i j)) ↔ GridOK β W H K L := by
  cases col
  · exact gridOK_iff_rows.symm
  · exact Iff.rfl

theorem sum_emb (col : Bool) (W H : ℕ) (f : Cell → ℕ) :
    ∑ i ∈ Finset.range (nOf col W H), ∑ j ∈ Finset.range (mOf col W H), f (emb col i j) =
      ∑ x ∈ Finset.range W, ∑ y ∈ Finset.range H, f (x, y) := by
  cases col
  · exact Finset.sum_comm
  · rfl

theorem emb_inBounds (I : Instance) {i j : ℕ}
    (hi : i < nOf (decide (I.H ≤ I.W)) I.W I.H) (hj : j < mOf (decide (I.H ≤ I.W)) I.W I.H) :
    I.InBounds (emb (decide (I.H ≤ I.W)) i j) := by
  cases h : decide (I.H ≤ I.W) <;> rw [h] at hi hj
  · exact ⟨hj, hi⟩
  · exact ⟨hi, hj⟩

/-- The label of a cell in the output of the DP. -/
def labOf (col : Bool) (w : List (List Lab)) (x : Cell) : Lab :=
  lab w (unemb col x).1 (unemb col x).2

theorem labOf_emb (col : Bool) (w : List (List Lab)) :
    (fun i j => labOf col w (emb col i j)) = lab w := by
  funext i j
  cases col <;> rfl

/-- One run of the certificate DP: ports and demands `pd`, degree cap `β`. Returns the
minimum certified cost and a labelling attaining it (as a list of layer states). -/
def dpRun (I : Instance) (pd : PD) (β : ℕ) : TimeM (Option (ℕ × List (List Lab))) := do
  -- one comparison, one multiplication, one addition, the length of `pd`, bookkeeping
  tickN (pd.length + 6)
  let labs ← labsT pd.length (I.W * I.H + 1)
  -- `List.replicate`
  tickN (mOf (decide (I.H ≤ I.W)) I.W I.H + 1)
  let cands ← tsections (List.replicate (mOf (decide (I.H ≤ I.W)) I.W I.H) labs)
  -- the two `List.range`s
  tickN (nOf (decide (I.H ≤ I.W)) I.W I.H + mOf (decide (I.H ≤ I.W)) I.W I.H + 2)
  let layers ← tmapM (fun i => tmapM (fun j => kindT I pd (emb (decide (I.H ≤ I.W)) i j))
      (List.range (mOf (decide (I.H ≤ I.W)) I.W I.H)))
    (List.range (nOf (decide (I.H ≤ I.W)) I.W I.H))
  LayerDP.run (gSelf β (I.W * I.H + 1) (dWOf (decide (I.H ≤ I.W))))
    (gLink (dAOf (decide (I.H ≤ I.W)))) cands layers

theorem dpRun_val (I : Instance) (pd : PD) (β : ℕ) :
    (dpRun I pd β).val =
      (LayerDP.run (gSelf β (I.W * I.H + 1) (dWOf (decide (I.H ≤ I.W))))
        (gLink (dAOf (decide (I.H ≤ I.W))))
        (List.replicate (mOf (decide (I.H ≤ I.W)) I.W I.H)
          (labsT pd.length (I.W * I.H + 1)).val).sections
        (layersOf (nOf (decide (I.H ≤ I.W)) I.W I.H) (mOf (decide (I.H ≤ I.W)) I.W I.H)
          (fun i j => kindOf I pd (emb (decide (I.H ≤ I.W)) i j)))).val := by
  simp only [dpRun, bind_val, tsections_val, tmapM_val]
  rfl

/-- The labels the DP ranges over: one entry per port, distances at most `W · H`. -/
def InRange (I : Instance) (pd : PD) (L : Cell → Lab) : Prop :=
  ∀ x, I.InBounds x → (L x).ds.length = pd.length ∧
    ∀ en ∈ (L x).ds, ∀ (d : ℕ) (δ : Dir), en = some (d, δ) → d < I.W * I.H + 1

theorem gridCost_emb (I : Instance) (pd : PD) (L : Cell → Lab) (M : ℕ) :
    gridCost M I pd L =
      ∑ i ∈ Finset.range (nOf (decide (I.H ≤ I.W)) I.W I.H),
        ∑ j ∈ Finset.range (mOf (decide (I.H ≤ I.W)) I.W I.H),
          (cellCostT M (kindOf I pd (emb (decide (I.H ≤ I.W)) i j))
            (L (emb (decide (I.H ≤ I.W)) i j))).val :=
  (sum_emb (decide (I.H ≤ I.W)) I.W I.H
    (fun c => (cellCostT M (kindOf I pd c) (L c)).val)).symm

/-- A labelling in range that passes all checks is a valid assignment of the DP. -/
theorem valid_of_gridOK {I : Instance} {pd : PD} {β : ℕ} {L : Cell → Lab}
    (hL : GridOK β I.W I.H (kindOf I pd) L) (hr : InRange I pd L) :
    LayerDP.Valid (gSelf β (I.W * I.H + 1) (dWOf (decide (I.H ≤ I.W))))
      (gLink (dAOf (decide (I.H ≤ I.W))))
      (List.replicate (mOf (decide (I.H ≤ I.W)) I.W I.H)
        (labsT pd.length (I.W * I.H + 1)).val).sections
      (layersOf (nOf (decide (I.H ≤ I.W)) I.W I.H) (mOf (decide (I.H ≤ I.W)) I.W I.H)
        (fun i j => kindOf I pd (emb (decide (I.H ≤ I.W)) i j)))
      (tab (nOf (decide (I.H ≤ I.W)) I.W I.H) (mOf (decide (I.H ≤ I.W)) I.W I.H)
        (fun i j => L (emb (decide (I.H ≤ I.W)) i j))) := by
  refine valid_tab ((layOK_emb _).mpr hL) (fun i j hi hj => ?_)
  obtain ⟨h1, h2⟩ := hr _ (emb_inBounds I hi hj)
  exact mem_labsT h1 h2

/-- If the run returns `(c, w)`, the labelling `w` passes all checks, has certified cost
`c`, and no labelling in range that passes all checks is cheaper. -/
theorem dpRun_some {I : Instance} {pd : PD} {β c : ℕ} {w : List (List Lab)}
    (h : (dpRun I pd β).val = some (c, w)) :
    GridOK β I.W I.H (kindOf I pd) (labOf (decide (I.H ≤ I.W)) w) ∧
    gridCost (I.W * I.H + 1) I pd (labOf (decide (I.H ≤ I.W)) w) = c ∧
    ∀ L : Cell → Lab, GridOK β I.W I.H (kindOf I pd) L → InRange I pd L →
      c ≤ gridCost (I.W * I.H + 1) I pd L := by
  rw [dpRun_val] at h
  obtain ⟨hv, hc, hmin⟩ := LayerDP.run_some h
  refine ⟨?_, ?_, ?_⟩
  · have hlay := valid_layOK hv
    rw [← labOf_emb (decide (I.H ≤ I.W)) w] at hlay
    exact (layOK_emb _).mp hlay
  · rw [gridCost_emb, ← hc, cost_of_valid hv]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← labOf_emb (decide (I.H ≤ I.W)) w]
  · intro L hL hr
    have hv' := valid_of_gridOK hL hr
    have := hmin _ hv'
    rw [cost_of_valid hv'] at this
    rw [gridCost_emb]
    refine le_trans this (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    rw [lab_tab _ _ _ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]

/-- If the run returns `none`, no labelling in range passes all checks. -/
theorem dpRun_none {I : Instance} {pd : PD} {β : ℕ} (h : (dpRun I pd β).val = none)
    (L : Cell → Lab) (hL : GridOK β I.W I.H (kindOf I pd) L) (hr : InRange I pd L) : False := by
  rw [dpRun_val] at h
  exact LayerDP.run_none h _ (valid_of_gridOK hL hr)

end TrainNetwork
