"""Required distances and the candidate-city rule (docs/problem.md, "Required pairs")."""
from __future__ import annotations

import collections
import dataclasses

from network_solver.instance import Cell, Instance

INF = float("inf")


def bfs(instance: Instance, source: Cell) -> dict[Cell, int]:
    """Edge-count distances from `source` through free cells only.

    Terminals other than `source` are reached (they get a distance) but never expanded,
    because a path may not pass through a city or port.
    """
    dist = {source: 0}
    queue = collections.deque([source])
    while queue:
        cell = queue.popleft()
        if cell != source and not instance.is_free(cell):
            continue  # a terminal: endpoint only
        for nxt in instance.neighbours(cell):
            if nxt not in dist:
                dist[nxt] = dist[cell] + 1
                queue.append(nxt)
    return dist


@dataclasses.dataclass(frozen=True)
class PortRequirement:
    """For one port: cities that must be connected, and a tie group from which exactly
    `choose` further cities must be connected (the optimiser picks which)."""

    port: str
    required: tuple[str, ...]
    tied: tuple[str, ...]
    choose: int
    distance: dict[str, int]  # city -> d(port, city), in edges

    @property
    def candidates(self) -> tuple[str, ...]:
        return self.required + self.tied


def requirements(instance: Instance) -> dict[str, PortRequirement]:
    """Applies the k-closest rule with ties at the k-th place left open."""
    out = {}
    for port, pcell in instance.ports.items():
        dist = bfs(instance, pcell)
        d = {c: dist.get(cell, INF) for c, cell in instance.cities.items()}
        reachable = sorted((v, c) for c, v in d.items() if v < INF)
        if len(reachable) < instance.k:
            raise ValueError(
                f"Port {port} reaches only {len(reachable)} cities; k={instance.k}."
            )
        threshold = reachable[instance.k - 1][0]
        required = tuple(c for v, c in reachable if v < threshold)
        tied = tuple(c for v, c in reachable if v == threshold)
        out[port] = PortRequirement(
            port=port,
            required=required,
            tied=tied,
            choose=instance.k - len(required),
            distance={c: int(v) for v, c in reachable if v <= threshold},
        )
    return out
