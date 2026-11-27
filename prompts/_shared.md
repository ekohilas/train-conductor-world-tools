<!-- Shared body, inlined into each rung prompt by scripts/prepare_fable_branch.sh.
     Not shown to Fable on its own. -->
## The problem

The full, frozen definition is in `docs/problem.md`. Read it first. The Lean encoding of
it is in `lean/TrainNetwork/Problem.lean`, and the running-time cost model is in
`lean/TrainNetwork/Cost.lean`. In short:

- A grid of `W × H` cells has some blocked cells (clouds), a set of ports and a set of
  cities. Each port must be connected to its `k` nearest cities, measured by grid
  distance `d` around clouds and other terminals. Ties at the `k`-th place are chosen
  freely.
- You build an undirected network on free cells. A track cell has at most 3 network
  neighbours, and there are no crossings. Paths may not pass through other cities or
  ports.
- Minimise lexicographically: first the total excess `Σ (network distance − d)` over
  the chosen pairs, then the number of track cells used.

## Repository

- `docs/problem.md`: the definition. **Frozen.**
- `lean/TrainNetwork/Problem.lean` and `lean/TrainNetwork/Cost.lean`: the formal
  definition and cost model. **Frozen.** Do not edit them, and do not add axioms.
- `lean/TrainNetwork/Goal.lean`: the statement you must prove. **Frozen.** Do not edit
  it. Write your proofs in new files under `lean/TrainNetwork/` and import them from
  `lean/TrainNetwork.lean` so that `lake build` checks `Goal.lean`.
- `network_solver/`: Python reference code.
  - `python -m network_solver solve <instance.json>`: an exact CP-SAT solver, to use as
    an oracle.
  - `python -m network_solver verify <instance.json> <solution.json>`: an independent
    feasibility and cost checker.
  - `network_solver/generate.py`: random instances.
- `data/instances/europe.json`: the real map (49 × 55, 6 ports, 23 cities, `k = 9`).
- `tests/`: pytest suite. Keep it green.

## Environment

- Python ≥ 3.11 with `ortools` and `pytest` (`pip install ortools pytest`).
- Lean 4 with Mathlib, pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`.
  Run `cd lean && lake exe cache get && lake build`.
  If the toolchain can't download, fetch the release tarball for the pinned version
  from GitHub releases (`leanprover/lean4`) and place it under
  `~/.elan/toolchains/leanprover--lean4---<version>`.

## Acceptance criteria

Your result counts only if **all** of these hold:

1. `cd lean && lake build` succeeds with `Goal.lean` imported. Running
   `#print axioms` on each theorem in `Goal.lean` shows only `propext`,
   `Classical.choice` and `Quot.sound`. No `sorry`, no `admit`, no new `axiom`, no
   `@[implemented_by]`/`@[extern]` tricks, and no edits to the frozen files.
2. Every algorithm you claim is written in `TimeM`, and follows the auditing rule at
   the top of `Cost.lean`. A reviewer will check every `tick`.
3. `docs/result.md` contains a self-contained, human-readable proof of the same claim,
   at the level of a good conference paper. It must state the exact theorem, the
   algorithm or reduction, the correctness argument and the running-time analysis. It
   must also list every place where the Lean proof and the paper proof differ.
4. A Python implementation of your algorithm or reduction lives in `network_solver/`,
   with tests showing that it agrees with the CP-SAT oracle (`network_solver.cpsat`).
   Use at least 200 random instances from `network_solver.generate`, of varied sizes,
   including ones with blocked cells and ties. Report its runtime on
   `data/instances/europe.json` next to the CP-SAT runtime.

## Rules

- Do not weaken, reinterpret or re-encode the problem. If you believe the frozen
  definition has a bug, stop and report it. Do not work around it.
- If you can't reach the goal, say so plainly in `docs/result.md`. State what you
  proved, what blocked you, and the strongest partial result with its exact
  statement. A clear negative report is far more useful than a weakened or disguised
  claim. Never present a partial result as the goal.
- Work only on the branch that is checked out. Do not fetch, check out, diff against or
  read any other branch or tag, and push only to this branch.
- Commit your work in small steps with clear messages.
