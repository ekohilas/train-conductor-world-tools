# Task: a polynomial-time algorithm for the Train Network Problem with few terminals

You are working in this repository on a research problem in algorithms and complexity.

**Goal.** Assume there are at most 10 ports and at most 40 cities. Find an algorithm
that solves the Train Network Problem *optimally* in time polynomial in `N = W · H`.
The degree of the polynomial may depend on the constants 10 and 40, but must be a fixed
number. Prove it correct and prove its running time, both in Lean 4 (machine-checked)
and on paper.

The exact statement you must prove is `lean/TrainNetwork/Goal.lean`. Concretely, you
must define in `lean/TrainNetwork/Answer.lean`:

- `TrainNetwork.Answer.solve : Instance → TimeM (Option Solution)`, which is executable,
- `TrainNetwork.Answer.correct`: on instances within the bounds, it returns an optimal
  solution, or `none` exactly when no feasible solution exists,
- `TrainNetwork.Answer.polytime`: on instances within the bounds, its `TimeM` cost is
  bounded by a fixed polynomial in `Instance.size`.

The bounded number of terminals is the lever. Work out exactly what it does and doesn't
buy you. Note that the networks themselves can still have `Θ(N)` cells and that paths
may need detours. Test your ideas against the CP-SAT oracle on many small instances
before you try to formalise them. Also report the actual runtime of your Python
implementation on `data/instances/europe.json`.
