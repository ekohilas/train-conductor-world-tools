"""CLI.

  python -m network_solver extract            # rebuild data/instances/europe.json from the Tiled map
  python -m network_solver solve INSTANCE [--out SOLUTION] [--time-limit S] [--log]
  python -m network_solver verify INSTANCE SOLUTION
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys

from network_solver import cpsat, verify
from network_solver.instance import Instance, Solution, from_tiled_map

ROOT = pathlib.Path(__file__).resolve().parent.parent


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="network_solver")
    sub = parser.add_subparsers(dest="cmd", required=True)
    ex = sub.add_parser("extract")
    ex.add_argument("--out", default=ROOT / "data/instances/europe.json")
    so = sub.add_parser("solve")
    so.add_argument("instance")
    so.add_argument("--out")
    so.add_argument("--time-limit", type=float, default=600.0)
    so.add_argument("--workers", type=int, default=8)
    so.add_argument("--log", action="store_true")
    ve = sub.add_parser("verify")
    ve.add_argument("instance")
    ve.add_argument("solution")
    args = parser.parse_args(argv)

    if args.cmd == "extract":
        inst = from_tiled_map(ROOT / "data/train-conductor-world.tmx", ROOT / "data/tiles.json")
        inst.save(args.out)
        print(f"wrote {args.out}: {inst.width}x{inst.height}, {len(inst.ports)} ports, "
              f"{len(inst.cities)} cities, {len(inst.blocked)} blocked")
        return 0

    inst = Instance.load(args.instance)
    if args.cmd == "solve":
        sol, stats = cpsat.solve(inst, time_limit=args.time_limit, workers=args.workers, log=args.log)
        print(json.dumps(stats))
        if sol is None:
            return 1
        report = verify.check(inst, sol)
        print("verify:", f"OK excess={report.excess} tiles={report.tiles}" if report.ok else report.errors)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as f:
                json.dump(sol.to_json(inst), f, indent=1)
        return 0 if report.ok else 1

    with open(args.solution, encoding="utf-8") as f:
        sol = Solution.from_json(json.load(f))
    report = verify.check(inst, sol)
    print(f"excess={report.excess} tiles={report.tiles}", "OK" if report.ok else "\n".join(report.errors))
    return 0 if report.ok else 1


if __name__ == "__main__":
    sys.exit(main())
