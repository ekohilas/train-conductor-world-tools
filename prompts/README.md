# Fable prompt ladder

Five research prompts on the complexity of the Train Network Problem
(`docs/problem.md`). Rungs are numbered from hardest (1) to easiest (5):

| Rung | Goal | Sizes | Lean goal (`goals/RungN.lean`) |
|---|---|---|---|
| 1 | Polynomial-time exact algorithm | N, P, C unbounded | `goal_correct`, `goal_polytime` |
| 2 | Exact complexity via equivalence (reductions both ways) with a known problem | N, P, C unbounded | `goal_to_correct`, `goal_from_correct`, `goal_to_poly`, `goal_from_poly` |
| 3 | Exact algorithm, polynomial in N | P ≤ 10, C ≤ 40 | `goal_correct`, `goal_polytime` |
| 4 | Exact algorithm in quasi-polynomial time 2^{O(log^d N)} | P ≤ 10, C ≤ 40 | `goal_correct`, `goal_quasipoly` |
| 5 | Exact algorithm in time 2^{o(N)} | P ≤ 10, C ≤ 40 | `goal_correct`, `goal_subexp` |

## How the results relate

* **1 ⇒ 3 ⇒ 4 ⇒ 5.** A polynomial algorithm for unbounded terminals is also polynomial
  with at most 10 ports and 40 cities. Polynomial time is also quasi-polynomial, and
  quasi-polynomial time is also `2^{o(N)}`.
* **Rung 2 is a separate track.** If it shows equivalence to an NP-hard problem, rung 1
  is hopeless unless P = NP. It says nothing about rungs 3 and 4, which can both still
  succeed.

## How to run the ladder

1. Run two tracks independently, in parallel:
   * **Algorithm track, easiest first: 5 → 4 → 3 → 1.** Climb only after the current rung
     passes review. Stop at the first rung that fails. A failed attempt doesn't prove
     a rung impossible. But a harder rung implies the easier one, so it's unlikely to
     succeed where the easier one didn't.
   * **Equivalence track: rung 2,** run on its own whenever convenient.
2. For each rung:
   ```bash
   scripts/prepare_fable_branch.sh 5 /tmp/rung5-prompt.md
   git push -u origin fable/run-<id>     # the branch name the script prints
   ```
   Start a **fresh** session on that branch and give it `/tmp/rung5-prompt.md` as the
   first message. The script records which rung each `fable/run-<id>` branch is in
   `.git/fable-runs` (local only).
3. The branch is an orphan commit without `prompts/` or `scripts/`, and each prompt is
   standalone. Branch names are opaque and no tags are pushed, so other branches on the
   remote don't announce which rung they are. The shared prompt tells the agent to
   work only on its own branch. That last part is a request, not a guarantee: other
   branches (including this one and earlier rungs' branches) stay readable if the
   agent deliberately fetches them. Keep earlier results, successes and failures alike, out of later
   prompts, so a harder rung isn't anchored on an easier rung's approach.
4. When a run claims success, start another fresh session and give it `review.md`, with
   `<BRANCH>` filled in. The base is the branch's root commit. A rung counts as passed
   only on an ACCEPT verdict.

## Files

* `rungN.md`: the rung-specific part of each prompt.
* `_shared.md`: the shared problem summary, environment and acceptance criteria,
  appended to every rung.
* `goals/RungN.lean`: the frozen Lean statement for each rung. It is copied to
  `lean/TrainNetwork/Goal.lean` on the rung branch (with `_tiny.lean` inlined, which
  forces the answer to be executable code).
* `review.md`: the independent audit checklist.
