# Task: pin down the exact complexity of the Train Network Problem

You are working in this repository on a research problem in algorithms and complexity.

**Goal.** Show that the decision version of the Train Network Problem is *equivalent*,
under polynomial-time many-one reductions in both directions, to an established problem
from the literature whose complexity is already known. Then the Train Network Problem
has exactly that complexity. Prove both reductions correct and polynomial, in Lean 4
(machine-checked) and on paper.

The exact statement you must prove is `lean/TrainNetwork/Goal.lean`. Concretely, you
must define in `lean/TrainNetwork/Answer.lean`:

- `TrainNetwork.Answer.KInstance : Type`, `KInstance.size : KInstance → ℕ` and
  `KYes : KInstance → Prop`: a faithful Lean encoding of the known problem, with its
  standard size measure,
- executable reductions `toK : Instance → ℕ → ℕ → TimeM KInstance` and
  `fromK : KInstance → TimeM (Instance × ℕ × ℕ)`,
- the lemmas `to_correct`, `from_correct`, `to_poly` and `from_poly` whose types are
  given in `Goal.lean`.

Choosing the right known problem is part of the task. In `docs/result.md`, cite the
publication that defines it and the one that establishes its complexity. Explain why
your Lean definition matches the published one, symbol by symbol. The known problem
must be a genuinely different, standard problem: a re-encoding of the Train Network
Problem itself does not count. Note that both directions are required, so one
reduction alone is not enough.

Test both reductions empirically before you formalise them. Round-trip random
instances from `network_solver.generate` through your Python implementation, and check
the yes/no answers against the CP-SAT oracle (and a solver for the known problem, if
one is practical).
