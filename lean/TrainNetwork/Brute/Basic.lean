/-
Executable basics for brute-force checking of Train Network instances:
computable `Decidable` instances for the predicates of `TrainNetwork.Problem`
and the list of all in-bounds cells.

`TrainNetwork.Problem` opens `Classical` (file-locally); this file deliberately does
not, so every instance below is a genuine decision procedure that `#eval` can run.
-/
import TrainNetwork.Problem

namespace TrainNetwork

/-! ### Computable decidability instances -/

instance Adjacent.instDecidableRel : DecidableRel Adjacent := fun a b => by
  unfold Adjacent; infer_instance

namespace Instance

variable (I : Instance)

instance InBounds.instDecidablePred : DecidablePred I.InBounds := fun c => by
  unfold InBounds; infer_instance

instance IsTerminal.instDecidablePred : DecidablePred I.IsTerminal := fun c => by
  unfold IsTerminal; infer_instance

instance IsFree.instDecidablePred : DecidablePred I.IsFree := fun c => by
  unfold IsFree; infer_instance

instance IsOpen.instDecidablePred : DecidablePred I.IsOpen := fun c => by
  unfold IsOpen; infer_instance

instance GridAdj.instDecidableRel : DecidableRel I.GridAdj := fun a b => by
  unfold GridAdj; infer_instance

end Instance

namespace Brute

/-! ### The list of all in-bounds cells -/

/-- All in-bounds cells, as a duplicate-free list. -/
def cells (I : Instance) : List Cell :=
  (List.range I.W).flatMap fun x => (List.range I.H).map fun y => (x, y)

theorem cells_eq_product (I : Instance) :
    cells I = List.range I.W ×ˢ List.range I.H := rfl

theorem mem_cells (I : Instance) (c : Cell) : c ∈ cells I ↔ I.InBounds c := by
  obtain ⟨x, y⟩ := c
  rw [cells_eq_product, List.mem_product, List.mem_range, List.mem_range]
  rfl

theorem cells_nodup (I : Instance) : (cells I).Nodup := by
  rw [cells_eq_product]
  exact List.Nodup.product List.nodup_range List.nodup_range

theorem cells_length (I : Instance) : (cells I).length = I.W * I.H := by
  rw [cells_eq_product, List.length_product, List.length_range, List.length_range]

end Brute

end TrainNetwork
