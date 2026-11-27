/-
Frozen cost model for running-time claims. Do NOT edit.

An algorithm is written in `TimeM`. Its running time is the `time` field, which only
`tick` increases. Auditing rule (checked by review, not by Lean):

* Every primitive operation on unbounded data (one arithmetic op, comparison, array/
  list/finset access or update, allocation of one element) and every loop iteration or
  recursive call must be charged at least one `tick`.
* Pure Lean code between ticks may only do O(1) work on values of bounded size. In
  particular `Finset`/`List` operations whose cost grows with the input (e.g. `filter`,
  `card`, `sort`, `sInf` over a search space) must be reimplemented in `TimeM`, or
  charged at an explicitly proven upper bound via `tickN`.
* Noncomputable definitions (`Classical.choice`, `sInf`, ...) may appear in *proofs*,
  never inside the algorithm being timed.

The input size of an instance is `Instance.size` below: `N = W * H + 1`, the size of
the dense grid encoding (one symbol per cell). Ports, cities and blocked cells all fit
in that grid, and `k ≤ |cities| ≤ N` for any instance with a feasible solution.
-/
import TrainNetwork.Problem

namespace TrainNetwork

/-- A computation returning a value together with the number of steps it took. -/
structure TimeM (α : Type) where
  val : α
  time : ℕ

namespace TimeM

instance : Monad TimeM where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.val; ⟨r.val, m.time + r.time⟩

/-- Charge one step. -/
def tick : TimeM Unit := ⟨(), 1⟩

/-- Charge `n` steps (for a sub-computation whose cost bound is proven separately). -/
def tickN (n : ℕ) : TimeM Unit := ⟨(), n⟩

@[simp] theorem pure_val {α} (a : α) : (pure a : TimeM α).val = a := rfl
@[simp] theorem pure_time {α} (a : α) : (pure a : TimeM α).time = 0 := rfl
@[simp] theorem bind_val {α β} (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).val = (f m.val).val := rfl
@[simp] theorem bind_time {α β} (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).time = m.time + (f m.val).time := rfl
@[simp] theorem tick_time : tick.time = 1 := rfl
@[simp] theorem tickN_time (n : ℕ) : (tickN n).time = n := rfl

end TimeM

/-- Input size `N` of an instance (docs/problem.md, "Decision version"). -/
def Instance.size (I : Instance) : ℕ := I.W * I.H + 1

end TrainNetwork
