# Train Network Problem: results

This file collects what is known about the problem defined in
[`docs/problem.md`](problem.md): the complexity results produced by the Fable prompt
ladder ([`prompts/`](../prompts/README.md)), their independent reviews, and the solved
real map. Last updated 2026-11-28.

## Summary

| Question | Answer | Strength |
|---|---|---|
| Can the problem be solved faster than exponential time? | **Yes**, for at most 10 ports and 40 cities: in `2^{O(√N log N)}`, where `N = W·H` | Proved in Lean, reviewed (rung 5) |
| Is it in NP? | **Yes** | Proved in Lean, reviewed (rung 2) |
| Is it NP-hard? | **Yes**, even with one port, no clouds and every city required | Paper proof, reviewed; the one cited fact was checked against the primary source (below) |
| Polynomial or quasi-polynomial with few terminals? | **Open** | Two independent runs (rungs 3 and 4) reduce it to an open disjoint-paths problem |
| Optimum of the real map | **Total excess 2, 210 track tiles** | Proved optimal by CP-SAT in about 5 minutes with 8 workers |

So the decision version is **NP-complete**. No polynomial algorithm exists for unbounded
numbers of terminals unless P = NP, which settles rung 1 in the negative (conditionally on
P ≠ NP). With few terminals the problem is sub-exponential, but whether it is polynomial
is tied to an open question in the algorithms literature.

## Results by rung

Each run worked on its own history-free branch, then an independent reviewer audited it
with [`prompts/review.md`](../prompts/review.md). Every run and review used Fable; runs
used extra-high effort, reviews high.

| Rung | Goal | Branch | Outcome | Review |
|---|---|---|---|---|
| 1 | Polynomial, unbounded terminals | — | Not run. Ruled out by NP-completeness unless P = NP | — |
| 2 | Polynomial-time equivalence with a known problem | `fable/run-1ce44c` | **Half reached.** Train ≤ₚ SAT in Lean; SAT ≤ₚ Train on paper via Rectilinear Steiner Tree | ACCEPT WITH NOTES |
| 3 | Polynomial, ≤ 10 ports, ≤ 40 cities | `fable/run-6eef41` | **Not reached.** Honest negative report with partial results | ACCEPT WITH NOTES |
| 4 | Quasi-polynomial, ≤ 10 ports, ≤ 40 cities | `fable/run-047e06` | **Not reached.** Honest negative report with partial results | ACCEPT WITH NOTES |
| 5 | `2^{o(N)}`, ≤ 10 ports, ≤ 40 cities | `fable/run-b7a3b8` | **Reached.** `Goal.lean` builds with standard axioms only | ACCEPT WITH NOTES |

Each branch's `docs/result.md` has the full statements and proofs.

### Rung 5: sub-exponential algorithm (goal reached)

- **Theorem (Lean):** with at most 10 ports and 40 cities, `Answer.solve` returns an
  optimal solution (or `none` exactly when none exists) in at most
  `2^420 · N^(60 + 90·min(W, H))` steps of the frozen cost model. Since
  `min(W, H) ≤ √N`, that is `2^{O(√N log N)}`.
- **Method:** a dynamic program over the grid one column (or row) at a time. Network
  distances have locally checkable certificates (distance labels with predecessor
  pointers), so only the current column needs to be remembered.
- **Review:** all 169 definitions reachable from `Answer.solve` were read; no
  undercounted work. The algorithm proved correct is the one whose time is bounded.
  483 fresh instances matched CP-SAT.
- **Caveats:**
  - Purely theoretical: the bound only drops below `2^N` around `N ≈ 4` million, and
    neither the verified version nor the faster "pruned" Python version finishes the
    real map.
  - The pruned Python solver is a different, unverified algorithm; its hardest cases
    (many pairs, large excess, infeasible instances) are lightly tested.
  - With the terminal counts bounded, the result is close to a textbook column DP.

### Rung 2: NP-completeness (half in Lean)

- **In NP (Lean):** a polynomial-time reduction from the Train Network decision problem
  to CNF-SAT (`toK`, `to_correct`, `to_poly`). Reviewed with 3,400 tiny instances
  against an independent brute force, 600 against CP-SAT using a different SAT solver,
  and a clause-by-clause comparison of the Lean and Python reductions.
- **NP-hard (paper):** a reduction from Rectilinear Steiner Tree. Points are scaled onto
  a grid, one becomes the single port and the rest are cities, and small repairs around
  each city keep every track cell at degree ≤ 3. The reviewer checked every step and
  found no error.
- **The cited fact, now confirmed.** The reduction needs Rectilinear Steiner Tree to be
  NP-complete with coordinates polynomially bounded in the number of points (NP-complete
  "in the strong sense"). This was checked against the primary source: Garey, Graham and
  Johnson, *Some NP-complete geometric problems*, Proc. 8th ACM STOC (1976), 10–22,
  Section 2. That section reduces from Exact Cover by 3-Sets, which has no numbers. Its
  coordinates scale with `K = 162n²t² + 96n²t + 60nt` (eq. 2.1), and its point set
  includes every integer point along each segment. So coordinates are polynomially
  bounded in the number of points, as required.
- **Not formalised:** SAT ≤ₚ Train in Lean. It would mean formalising
  SAT → planar vertex cover → Rectilinear Steiner Tree → Train. A direct reduction
  needs crossing gadgets, and crossing routes change the nearest-city sets.
- **Note:** the branch's own `README.md` says "NP-complete" without the condition, and
  `result.md` still marks the Steiner fact as unconfirmed. This file supersedes both.

### Rungs 3 and 4: polynomial and quasi-polynomial (not reached)

Both runs reached the same wall independently.

- **Structure found:** some optimal network has at most `m(m−1)` T-junctions for `m`
  chosen pairs (both runs). So the problem reduces to guessing junction positions and
  routing between them.
- **The wall:** the routing step is, or contains, **min-sum (shortest) disjoint paths**
  with a fixed number of pairs on a grid with holes. For 3 or more pairs no polynomial
  or quasi-polynomial algorithm is known, even on planar graphs (known for 2 pairs:
  Björklund and Husfeldt; solved on grids *without* holes: Mari, Mukherjee, Pilipczuk
  and Sankowski, SODA 2024, who list grids with holes as open).
- **The reduction only goes one way.** Routes may share track for free, so the train
  problem might be strictly easier; no hardness for bounded terminals was found either.
- **Partial results:**
  - Rung 3: a Lean-verified exhaustive solver; feasibility in polynomial time for
    bounded terminals via Robertson–Seymour (paper only, far too large to formalise);
    an exact branch-and-bound solver that proves the real map's optimal excess in 2.5 s.
  - Rung 4: a Lean-verified exhaustive solver with a proved `2^{600(N+1)}` bound; a
    Lean reduction of the goal to a "complete candidate generator" (meaningful only under
    the tick audit); a paper frontier DP in `2^{O(√N log N)}`.
- **Open core, in one sentence (rung 3):** in a grid with holes, delete one grid edge at
  every crossroads so that the sum of the `m` pair distances is as small as possible.

## The real map

- **Instance:** `data/instances/europe.json`, 49 × 55, 1149 clouds, 6 ports, 23 cities,
  `k = 9` (54 pairs).
- **Optimum:** total excess 2, **210 track tiles**:
  `data/instances/europe.solution.json`. The excess of 2 is forced: Stuttgart→Paris has
  one straight shortest path along row 27, all 4 shortest paths of Marseille→Mons cross
  it, and there is no crossing tile. See
  [`docs/crossing-conflict.html`](crossing-conflict.html).
- **In the map:** [`data/train-conductor-world.optimal.tmx`](../data/train-conductor-world.optimal.tmx)
  is a copy of the map whose `tracks` layer holds this network, built from the
  Transparent track tiles (T-junctions 101–104). Picture:
  [`docs/optimal-network.png`](optimal-network.png).
- **The manual network** in `data/train-conductor-world.tmx` (244 tiles) does not satisfy
  the current rules: Hamburg→Bastei is not connected, and the connected pairs have total
  excess 64 (choosing Lyon for Rotterdam's tie). It was built for the earlier rules (different city sets and
  Manhattan distances). Check any map with
  `python -m network_solver.tmx_tracks check [file.tmx]`.

### Solving it

| Solver | Real map | Notes |
|---|---|---|
| CP-SAT, 8 workers (default) | **Optimal proved in ~5 min** | `python -m network_solver solve data/instances/europe.json` |
| CP-SAT, 4 workers | Finds 210 tiles, cannot prove it (bound stuck at 104) in 30 min | Below 8 workers CP-SAT drops its LP-based strategies (`max_lp`, `reduced_costs`, `quick_restart`). `cpsat.solve` now warns |
| Rung 3's branch-and-bound | Optimal excess in 2.5 s; tiles not finished in an hour | On `fable/run-6eef41` |
| Rung 5's layered DP | Does not finish | Theoretical |
| SAT encoding (rung 2) | 432 million clauses | A proof device, not a solver |

Workers are threads, so 8 workers are fine on a 4-core machine.

## Known limits of this setup

- **Tick accounting is an honour system.** Wrapping a solver in `pure` costs 0 steps
  and still type-checks, so running-time claims rely on the review's line-by-line audit.
  No run cheated.
- **Run isolation is a request.** Each run's branch has no history and opaque naming,
  but other branches stay readable on the remote; the prompt asks the agent not to read
  them.
- **Long runs hit platform limits.** One run hit the 5-hour usage limit and one
  produced a single response over the 128k output-token cap. Both were resumed; the
  shared prompt now asks for small responses and frequent pushes.

## Cost

About $226 for four runs (rung 3 $43, rung 5 $73, rung 2 $60, rung 4 $50) and about $40
for four reviews.

## Possible next steps

- **Formalise NP-hardness in Lean** (SAT → planar vertex cover → Rectilinear Steiner
  Tree → Train). Very large.
- **The open core:** min-sum disjoint paths on grids with holes. An open research
  problem; low odds.
- **Simplified variants** that isolate the difficulty: allow 4-way junctions (removes
  the degree rule, leaving a Manhattan-network-style problem), or fix the total excess
  to a constant.
