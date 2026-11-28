/-
Answer file for `Goal.lean`. **PARTIAL RESULT — the goal is NOT reached.**

What is provided:

* `Answer.solve`    : an executable exact solver in `TimeM` (exhaustive search).
* `Answer.correct`  : it returns an optimal solution, or `none` exactly when no feasible
                      solution exists. This is the statement required by
                      `Goal.goal_correct`, fully proved.
* `Answer.exp_time` : an **exponential** bound `2 ^ (600 * N)` on its running time.

What is NOT provided:

* `Answer.quasipoly`. The solver is exhaustive search, and no quasi-polynomial algorithm
  was found. `Goal.lean` therefore does not compile, deliberately: `goal_quasipoly`
  refers to a theorem that does not exist, and nothing here pretends otherwise.
  See `docs/result.md`, and `Partial.lean` for the statements that are proved.
-/
import TrainNetwork.TimeBound

namespace TrainNetwork.Answer

/-- Exact solver (exhaustive search over edge subsets and city choices). -/
def solve (I : Instance) : TimeM (Option Solution) := solveT I

/-- `solve` returns an optimal solution, or `none` exactly when the instance has no
feasible solution. The bounds on the number of ports and cities are not needed. -/
theorem correct (I : Instance) (_hP : I.ports.card ≤ 10) (_hC : I.cities.card ≤ 40) :
    match (solve I).val with
    | some σ => IsOptimal I σ
    | none => ¬ ∃ σ : Solution, σ.Feasible I := by
  unfold solve
  rw [solveT_val]
  exact solvePure_correct I

/-- Exponential running time: `2 ^ (c * N)` steps. This is NOT quasi-polynomial. -/
theorem exp_time :
    ∃ c : ℕ, ∀ I : Instance, I.ports.card ≤ 10 → I.cities.card ≤ 40 →
      (solve I).time ≤ 2 ^ (c * I.size) :=
  ⟨600, fun I hP hC => solveT_time_le I hP hC⟩

end TrainNetwork.Answer
