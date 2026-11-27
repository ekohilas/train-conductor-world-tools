"""Larger randomised cross-check of `network_solver.exact` against the CP-SAT oracle.

    python scripts/stress_exact.py [COUNT]        # default 2500, about two minutes

Random sizes 3..9 x 3..9, 1-4 ports, 2-7 cities, k <= 4, blocked fraction 0..0.5.
Instances on which `exact` exceeds 20 s are counted as `exact_timeout` and skipped; a
disagreement is printed as MISMATCH and makes the script exit with status 1.
"""
from __future__ import annotations

import collections
import pathlib
import random
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from network_solver import cpsat, exact, verify  # noqa: E402
from network_solver.distances import requirements  # noqa: E402
from network_solver.generate import random_instance  # noqa: E402


def main(count: int) -> int:
    rng = random.Random(12345)
    stats: collections.Counter = collections.Counter()
    start = time.time()
    for _ in range(count):
        w, h = rng.randint(3, 9), rng.randint(3, 9)
        ports, cities = rng.randint(1, 4), rng.randint(2, 7)
        k = rng.randint(1, min(cities, 4))
        fraction = rng.choice([0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5])
        if ports + cities > w * h - 2:
            continue
        try:
            inst = random_instance(w, h, ports, cities, k, blocked_fraction=fraction,
                                   seed=rng.randrange(10 ** 9), max_tries=200)
        except RuntimeError:
            stats["generator_failed"] += 1
            continue
        sol, st = exact.solve(inst, time_limit=20)
        if not st["optimal"]:
            stats["exact_timeout"] += 1
            continue
        oracle, ost = cpsat.solve(inst, time_limit=120, workers=2)
        if oracle is not None and not ost.get("optimal"):
            stats["cpsat_not_optimal"] += 1
            continue
        got = verify.check(inst, sol).cost if sol else None
        want = verify.check(inst, oracle).cost if oracle else None
        stats["compared"] += 1
        if got is None:
            stats["infeasible"] += 1
        elif got[0] > 0:
            stats["positive_excess"] += 1
        if any(r.choose < len(r.tied) for r in requirements(inst).values()):
            stats["tie_choice"] += 1
        if got != want:
            stats["MISMATCH"] += 1
            print("MISMATCH", inst.to_json(), got, want, flush=True)
    print(dict(stats), f"{time.time() - start:.0f}s")
    return 1 if stats["MISMATCH"] else 0


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 2500))
