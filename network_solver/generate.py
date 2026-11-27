"""Random instance generator, for cross-checking algorithms against the CP-SAT oracle."""
from __future__ import annotations

import random

from network_solver.distances import requirements
from network_solver.instance import Instance


def random_instance(width: int, height: int, ports: int, cities: int, k: int,
                    blocked_fraction: float = 0.1, seed: int = 0,
                    max_tries: int = 1000) -> Instance:
    """Returns a random instance in which every port reaches at least k cities."""
    rng = random.Random(seed)
    cells = [(x, y) for x in range(width) for y in range(height)]
    for _ in range(max_tries):
        rng.shuffle(cells)
        terms = cells[: ports + cities]
        rest = cells[ports + cities:]
        blocked = frozenset(c for c in rest if rng.random() < blocked_fraction)
        inst = Instance(
            width=width,
            height=height,
            k=k,
            blocked=blocked,
            ports={f"P{i}": terms[i] for i in range(ports)},
            cities={f"C{i}": terms[ports + i] for i in range(cities)},
        )
        try:
            requirements(inst)
            return inst
        except ValueError:
            continue
    raise RuntimeError("Could not generate a feasible instance; lower blocked_fraction.")
