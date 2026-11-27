# Task: a polynomial-time algorithm for the Train Network Problem

You are working in this repository on a research problem in algorithms and complexity.

**Goal.** Find an algorithm that solves the Train Network Problem *optimally* in time
polynomial in `N = W · H`, with no bound on the number of ports or cities. Prove it
correct and prove its running time, both in Lean 4 (machine-checked) and on paper.

The exact statement you must prove is `lean/TrainNetwork/Goal.lean`. Concretely, you
must define in `lean/TrainNetwork/Answer.lean`:

- `TrainNetwork.Answer.solve : Instance → TimeM (Option Solution)`, which is executable,
- `TrainNetwork.Answer.correct`: it returns an optimal solution, or `none` exactly when
  no feasible solution exists,
- `TrainNetwork.Answer.polytime`: its `TimeM` cost is bounded by a fixed polynomial in
  `Instance.size`.

Think hard about the structure of the problem before committing to an approach. The
grid geometry, the degree bound of 3, the lexicographic objective (excess first), the
fact that paths may not pass through terminals, and the `k`-nearest rule may all matter.
Test your ideas against the CP-SAT oracle on many small instances before you try to
formalise them. An idea that fails on a random 6×6 instance will not survive Lean.
