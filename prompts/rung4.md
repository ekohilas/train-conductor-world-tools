# Task: a quasi-polynomial algorithm for the Train Network Problem with few terminals

You are working in this repository on a research problem in algorithms and complexity.

**Goal.** Assume there are at most 10 ports and at most 40 cities. Find an algorithm
that solves the Train Network Problem *optimally* in quasi-polynomial time
`2^{O(log^d N)}` (equivalently `N^{O(log^{d-1} N)}`), where `N = W · H`. The constants
may depend on the bounds 10 and 40, but not on the instance. Exhaustive search over all
networks takes `2^{Θ(N)}`. Prove the algorithm correct and prove its running time, both
in Lean 4 (machine-checked) and on paper.

The exact statement you must prove is `lean/TrainNetwork/Goal.lean`. Concretely, you
must define in `lean/TrainNetwork/Answer.lean`:

- `TrainNetwork.Answer.solve : Instance → TimeM (Option Solution)`, which is executable,
- `TrainNetwork.Answer.correct`: on instances within the bounds, it returns an optimal
  solution, or `none` exactly when no feasible solution exists,
- `TrainNetwork.Answer.quasipoly`: there are constants `c` and `d` such that, on
  instances within the bounds, its `TimeM` cost is at most
  `2^(c · (⌊log₂ N⌋ + 1)^d)`.

Think hard about the structure of the problem before committing to an approach. Test
your ideas against the CP-SAT oracle on many small instances before you try to
formalise them. An idea that fails on a random 6×6 instance will not survive Lean.
State the exact running time you achieve in `docs/result.md`, and report the actual
runtime of your Python implementation on `data/instances/europe.json`.
