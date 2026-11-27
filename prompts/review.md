# Task: audit a claimed result on the Train Network Problem

You are an independent reviewer. Another agent worked on branch `<BRANCH>`, starting
from its root commit (`BASE=$(git rev-list --max-parents=0 <BRANCH>)`; written as
`<BASE_COMMIT>` below). It claims to have proved the theorem in
`lean/TrainNetwork/Goal.lean`. Your job is to find out whether that claim is
**actually true and actually proved**, not to improve the work. Assume it may contain
subtle cheating, including unintentional cheating. You pass it only if every check
below holds.

Report each check as PASS / FAIL with evidence (commands run, file:line references).
Finish with an overall verdict: **ACCEPT**, **REJECT** or **ACCEPT WITH NOTES**. Do not
modify the work, except for scratch files outside the repository.

## Checks

1. **Frozen files untouched.** `git diff <BASE_COMMIT> -- docs/problem.md
   lean/TrainNetwork/Problem.lean lean/TrainNetwork/Cost.lean
   lean/TrainNetwork/Goal.lean lean/lakefile.toml lean/lean-toolchain
   network_solver/verify.py network_solver/distances.py network_solver/instance.py`
   must be empty.
2. **It builds.** Run `cd lean && lake build` from a clean `.lake/build` for the
   project (Mathlib may come from the cache). It must succeed.
3. **No gaps.** For every theorem in `Goal.lean`, add `#print axioms` in a scratch
   file that imports `TrainNetwork`. Only `propext`, `Classical.choice` and
   `Quot.sound` may appear. Grep the project sources for `sorry`, `admit`, `axiom`,
   `@[implemented_by`, `@[extern`, `unsafe`, `opaque`, `native_decide` and
   `set_option debug`. Every hit needs a justification; any of them in the proof path
   is a FAIL.
4. **Honest cost accounting.** Read every definition reachable from the timed
   algorithm(s) (`Answer.solve`, or `Answer.toK`/`Answer.fromK`). Apply the auditing
   rule at the top of `Cost.lean` line by line. Look for:
   - loops or recursion that do not `tick` per iteration;
   - `Finset`/`List`/`Array` operations of non-constant cost done in pure code between
     ticks, such as `filter`, `card`, `sort`, `image`, `toList`, `decide` over a large
     domain, or `Nat` arithmetic on numbers that are not polynomially bounded;
   - `tickN n` where `n` is not justified by a proven bound on the work it stands for;
   - work hidden in a `Decidable` instance, a coercion, or a structure's field
     defaults.
   List every violation found.
5. **The statement means what it should.** Read `Problem.lean` against
   `docs/problem.md`. Confirm the proof does not exploit a degenerate corner of the
   formal definitions, for example vacuous `Feasible`, an unsatisfiable hypothesis, an
   `Instance` that can't occur, or `⊤` arithmetic in `ℕ∞`. Where you find one, say
   whether it invalidates the result or is harmless.
6. **(Equivalence claims only.) The known problem is real.** Check that
   `Answer.KInstance`/`KYes`/`KInstance.size` match the cited published definition and
   standard encoding. Check that the cited complexity result really exists and applies
   to that exact variant. Check that the problem is not a disguised re-encoding of the
   Train Network Problem.
7. **Paper proof.** Read `docs/result.md`. Does it prove the same statement as the Lean
   proof? Are the differences it lists the only ones? Note any step that looks wrong,
   even where Lean accepted the formal version (this can reveal a mismatch in the
   formal statement).
8. **Empirical agreement.** Run `python -m pytest -q`. Then run the agent's Python
   implementation against `python -m network_solver solve` on at least 300 fresh random
   instances from `network_solver.generate`, using seeds the agent did not use, mixed
   sizes up to 8×8, blocked cells and ties. All costs (excess, tiles) must match, and
   every returned solution must pass `network_solver.verify`. Report the runtime of both
   on `data/instances/europe.json`.
