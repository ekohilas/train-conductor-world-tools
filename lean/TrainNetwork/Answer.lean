/-
The answer to `Goal.lean`.

* `Answer.solve`   — the algorithm, in `TimeM` (`Solve.lean`);
* `Answer.correct` — it returns an optimal solution, or `none` exactly when the instance
                     has no feasible solution (`Correct.lean`);
* `Answer.subexp`  — its running time is `2^{o(N)}` for at most 10 ports and 40 cities
                     (`TimeBound.lean`, which also proves the explicit bound
                     `Answer.solve_time_le`).

See `docs/result.md` for the paper proof and for a map of the development.
-/
import TrainNetwork.Correct
import TrainNetwork.TimeBound
