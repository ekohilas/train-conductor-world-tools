# Fable prompt ladder

Four research prompts on the complexity of the Train Network Problem
(`docs/problem.md`), ordered from hardest to easiest:

| Rung | Goal | Sizes | Lean goal (`goals/RungN.lean`) |
|---|---|---|---|
| 1 | Polynomial-time exact algorithm | N, P, C unbounded | `goal_correct`, `goal_polytime` |
| 2 | Exact complexity via equivalence (reductions both ways) with a known problem | N, P, C unbounded | `goal_to_correct`, `goal_from_correct`, `goal_to_poly`, `goal_from_poly` |
| 3 | Exact algorithm, polynomial in N | P ≤ 10, C ≤ 40 | `goal_correct`, `goal_polytime` |
| 4 | Exact algorithm in time 2^{o(N)} | P ≤ 10, C ≤ 40 | `goal_correct`, `goal_subexp` |

## How to run the ladder

1. Run rung 1 first. Only if it fails, run rung 2, and so on. Stop at the first rung
   that passes review.
2. For each rung:
   ```bash
   scripts/prepare_fable_branch.sh 1 /tmp/rung1-prompt.md
   git push -u origin fable/rung-1 && git push origin fable-rung-1-base
   ```
   Start a **fresh** session on branch `fable/rung-1` and give it
   `/tmp/rung1-prompt.md` as the first message.
3. The branch is an orphan commit without `prompts/` or `scripts/`, and each prompt is
   standalone. The agent never sees the other rungs, the review checklist, or that an
   earlier rung failed. Keep failure reports out of later prompts.
4. When a run claims success, start another fresh session and give it `review.md`, with
   `<BRANCH>` and `<BASE_COMMIT>` filled in (the `fable-rung-N-base` tag). A rung counts
   as passed only on an ACCEPT verdict.

## Files

* `rungN.md`: the rung-specific part of each prompt.
* `_shared.md`: the shared problem summary, environment and acceptance criteria,
  appended to every rung.
* `goals/RungN.lean`: the frozen Lean statement for each rung. It is copied to
  `lean/TrainNetwork/Goal.lean` on the rung branch (with `_tiny.lean` inlined, which
  forces the answer to be executable code).
* `review.md`: the independent audit checklist.
