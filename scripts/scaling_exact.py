"""Shows the exponential behaviour of `network_solver.exact` on medium instances.

    python scripts/scaling_exact.py [TIME_LIMIT_SECONDS]      # default 30

15 fixed random instances (10x10 and 12x12, 4 ports, 8 cities, k = 4, i.e. 16 pairs).
Prints, per instance, the result and time of `exact` and of the CP-SAT oracle.
"""
from __future__ import annotations

import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from network_solver import cpsat, exact, verify  # noqa: E402
from network_solver.generate import random_instance  # noqa: E402

CONFIGS = [(10, 10, 4, 8, 4), (12, 12, 4, 8, 4), (12, 12, 4, 8, 4)]
FRACTIONS = [0.0, 0.1, 0.2, 0.3, 0.4]


def main(limit: float) -> None:
    finished, times = 0, []
    for ci, (w, h, p, c, k) in enumerate(CONFIGS):
        for seed in range(5):
            inst = random_instance(w, h, p, c, k, blocked_fraction=FRACTIONS[seed],
                                   seed=1000 + 10 * ci + seed)
            t0 = time.perf_counter()
            sol, stats = exact.solve(inst, time_limit=limit)
            t1 = time.perf_counter()
            oracle, ostats = cpsat.solve(inst, time_limit=300, workers=4)
            t2 = time.perf_counter()
            got = verify.check(inst, sol).cost if sol else None
            want = verify.check(inst, oracle).cost if oracle else None
            if stats["optimal"]:
                finished += 1
                times.append(t1 - t0)
                assert got == want, (got, want)
            print(f"{w}x{h} seed {1000 + 10 * ci + seed} blocked {FRACTIONS[seed]}: "
                  f"exact {stats['status']} {got} excess_proved={stats.get('excess_optimal', False)} "
                  f"{t1 - t0:.2f}s | cpsat {want} optimal={ostats.get('optimal')} {t2 - t1:.2f}s", flush=True)
    print(f"exact finished {finished} of 15 within {limit:.0f}s; "
          f"times of finished runs {min(times):.2f}s .. {max(times):.2f}s")


if __name__ == "__main__":
    main(float(sys.argv[1]) if len(sys.argv) > 1 else 30.0)
