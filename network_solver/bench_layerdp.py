"""Timing script for the layered DP (network_solver/layerdp.py).

  python -m network_solver.bench_layerdp europe [--instance PATH] [--time-limit S]
                                                [--max-states N] [--max-rss-mb MB]
  python -m network_solver.bench_layerdp scaling [--time-limit S] [--seeds N] [--workers N]

`europe` runs the pruned DP on one instance under a wall-clock limit and memory guards
and prints the stats (including how far it got if a guard fired). `scaling` runs it on
random instances of growing size and reports how many finish within the time limit.
"""
from __future__ import annotations

import argparse
import json
import multiprocessing
import pathlib
import statistics
import sys
import time

from network_solver import layerdp, verify
from network_solver.generate import random_instance
from network_solver.instance import Instance

ROOT = pathlib.Path(__file__).resolve().parent.parent

# (width, height) of the random instances of the scaling run.
SCALING_SHAPES = [(6, 6), (8, 8), (10, 10), (15, 15), (20, 15), (20, 20), (30, 20),
                  (30, 30), (40, 30), (40, 40), (50, 50)]
# (ports, cities, k, blocked_fraction) of the random instances of the scaling run.
SCALING_CONFIGS = [(2, 4, 2, 0.1), (3, 5, 3, 0.1), (4, 8, 4, 0.2)]


def _scaling_job(job: tuple) -> dict:
    width, height, ports, cities, k, blocked, seed, time_limit, max_states = job
    inst = random_instance(width, height, ports, cities, k, blocked, seed)
    start = time.perf_counter()
    sol, stats = layerdp.solve(inst, time_limit=time_limit, max_states=max_states)
    seconds = time.perf_counter() - start
    return {"shape": (width, height), "config": (ports, cities, k, blocked), "seed": seed,
            "status": stats["status"], "stopped": stats.get("stopped"),
            "seconds": seconds, "states": stats["states"],
            "excess": stats["excess"], "tiles": stats["tiles"]}


def run_scaling(time_limit: float, seeds: int, workers: int, max_states: int) -> None:
    jobs = [(w, h, *cfg, seed, time_limit, max_states)
            for cfg in SCALING_CONFIGS for (w, h) in SCALING_SHAPES for seed in range(seeds)]
    with multiprocessing.Pool(workers) as pool:
        results = pool.map(_scaling_job, jobs, chunksize=1)
    print(f"pruned DP, random instances, {seeds} seeds each, limit {time_limit}s and "
          f"{max_states} states per instance, {workers} worker(s)")
    for cfg in SCALING_CONFIGS:
        print(f"ports={cfg[0]} cities={cfg[1]} k={cfg[2]} blocked_fraction={cfg[3]}")
        for shape in SCALING_SHAPES:
            rows = [r for r in results if r["shape"] == shape and r["config"] == cfg]
            done = [r for r in rows if r["status"] != "TIMEOUT"]
            times = sorted(r["seconds"] for r in done)
            line = f"  {shape[0]:>3}x{shape[1]:<3} finished {len(done):>2}/{len(rows)}"
            if times:
                line += (f"  median {statistics.median(times):6.2f}s  max {times[-1]:6.2f}s"
                         f"  max states {max(r['states'] for r in done)}")
            print(line)


def run_europe(path: str, time_limit: float, max_states: int, max_rss_mb: float) -> int:
    inst = Instance.load(path)
    print(f"instance {path}: {inst.width}x{inst.height}, {len(inst.ports)} ports, "
          f"{len(inst.cities)} cities, k={inst.k}, {len(inst.blocked)} blocked", flush=True)
    start = time.perf_counter()
    sol, stats = layerdp.solve(inst, time_limit=time_limit, max_states=max_states,
                               max_rss_mb=max_rss_mb, verbose=True)
    stats["wall_seconds"] = round(time.perf_counter() - start, 2)
    print(json.dumps(stats))
    if sol is not None:
        report = verify.check(inst, sol)
        print("verify:", f"OK excess={report.excess} tiles={report.tiles}"
              if report.ok else report.errors)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="network_solver.bench_layerdp")
    sub = parser.add_subparsers(dest="cmd", required=True)
    eu = sub.add_parser("europe")
    eu.add_argument("--instance", default=str(ROOT / "data/instances/europe.json"))
    eu.add_argument("--time-limit", type=float, default=1800.0)
    eu.add_argument("--max-states", type=int, default=5_000_000)
    eu.add_argument("--max-rss-mb", type=float, default=8192.0)
    sc = sub.add_parser("scaling")
    sc.add_argument("--time-limit", type=float, default=10.0)
    sc.add_argument("--seeds", type=int, default=12)
    sc.add_argument("--workers", type=int, default=1)
    sc.add_argument("--max-states", type=int, default=3_000_000)
    args = parser.parse_args(argv)
    if args.cmd == "europe":
        return run_europe(args.instance, args.time_limit, args.max_states, args.max_rss_mb)
    run_scaling(args.time_limit, args.seeds, args.workers, args.max_states)
    return 0


if __name__ == "__main__":
    sys.exit(main())
