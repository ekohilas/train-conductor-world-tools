# Task: a sub-exponential algorithm for the Train Network Problem with few terminals

You are working in this repository on a research problem in algorithms and complexity.

**Goal.** Assume there are at most 10 ports and at most 40 cities. Find an algorithm
that solves the Train Network Problem *optimally* in time `2^{o(N)}`, where
`N = W · H`. Exhaustive search over all networks takes `2^{Θ(N)}`. Prove it correct and
prove its running time, both in Lean 4 (machine-checked) and on paper.

The exact statement you must prove is `lean/TrainNetwork/Goal.lean`. Concretely, you
must define in `lean/TrainNetwork/Answer.lean`:

- `TrainNetwork.Answer.solve : Instance → TimeM (Option Solution)`, which is executable,
- `TrainNetwork.Answer.correct`: on instances within the bounds, it returns an optimal
  solution, or `none` exactly when no feasible solution exists,
- `TrainNetwork.Answer.subexp`: for every `ε > 0`, on all large enough instances within
  the bounds, its `TimeM` cost is at most `2^(ε·N)`.

State the best running time you achieve (for example `2^{O(√N log N)}`) in
`docs/result.md`, even though the Lean goal only asks for `2^{o(N)}`. Test your
algorithm against the CP-SAT oracle on many small instances before you formalise it.
Also report its actual runtime on `data/instances/europe.json`.
