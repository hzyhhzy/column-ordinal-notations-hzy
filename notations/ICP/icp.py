"""ICP candidate: Interpolating Copy Patterns.

Two earlier-column addresses per edge. Monotone copying, root-first control,
and prefix-dependent interpolation. This version is NOT well-ordered:
S3[1][1][0], followed by repeated [1], is an infinite standard descending
chain. See non-well-founded.zh-CN.md. The expansion rules are unchanged.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from time import monotonic
from typing import Iterable

Edge = tuple[int, int]
Column = tuple[Edge, ...]
Pattern = tuple[Column, ...]


def column(edges: Iterable[Edge]) -> Column:
    values: dict[int, int] = {}
    for parent, root in edges:
        values[parent] = max(root, values.get(parent, -1))
    return tuple(sorted(values.items(), reverse=True))


def control(current: Column) -> Edge:
    return max(current, key=lambda edge: (edge[1], edge[0]))


def lower(prefix: Pattern, current: Column) -> Column:
    parent, root = control(current)
    edges = [(p, q) for p, q in current if p != parent]
    edges.extend(prefix[parent])
    if root:
        edges.append((parent, root - 1))
    return column(edges)


@dataclass
class Budget:
    """Optional experimental guard, separate from the finite rules."""
    max_columns: int = 2000
    max_edges: int = 200000
    max_work: int = 2000000
    seconds: float = 2.0
    work: int = 0
    start: float = field(default_factory=monotonic)

    def tick(self, work: int = 1, *, columns: int = 0, edges: int = 0) -> None:
        self.work += work
        if (self.work > self.max_work or columns > self.max_columns
                or edges > self.max_edges or monotonic() - self.start > self.seconds):
            raise RuntimeError("ICP experimental resource budget exhausted.")


def reflect(pattern: Pattern, budget: Budget | None = None,
            trace: list[dict] | None = None) -> Pattern:
    if not pattern or not pattern[-1]:
        return pattern
    cut, _ = control(pattern[-1])
    output = list(pattern[:-1]) + [lower(pattern[:-1], pattern[-1])]
    image = list(range(cut)) + [len(output) - 1]
    live_edges = sum(map(len, output))

    def append(current: Column) -> None:
        nonlocal live_edges
        live_edges += len(current)
        if budget is not None:
            budget.tick(1 + len(current), columns=len(output) + 1, edges=live_edges)
        output.append(current)

    # Each original column is processed once; its image is the end of its block.
    for origin in range(cut + 1, len(pattern)):
        current = column((image[p], image[q]) for p, q in pattern[origin])
        ancestors: list[int] = []
        if current:
            parent, root = control(current)
            while output[root]:
                root, _ = control(output[root])
                if root <= parent:
                    break
                ancestors.append(root)
                if budget is not None:
                    budget.tick()
        start = len(output)
        append(current)
        for ancestor in reversed(ancestors):
            current = column((*current, (ancestor, len(output) - 1)))
            append(current)
        image.append(len(output) - 1)
        assert image[-2] < image[-1]
        if trace is not None:
            trace.append({"origin": origin, "start": start,
                          "end": image[-1], "ancestors": ancestors})
    return tuple(output)


def expand(pattern: Pattern, n: int, budget: Budget | None = None) -> Pattern:
    if type(n) is not int or n < 0:
        raise ValueError("The index must be a nonnegative integer.")
    if not n or not pattern or not pattern[-1]:
        return pattern[:-1]
    for _ in range(n):
        pattern = reflect(pattern, budget)
    return pattern[:-1]


def seed(height: int) -> Pattern:
    if type(height) is not int or height < 0:
        raise ValueError("The seed height must be a nonnegative integer.")
    return ((),) + tuple(column((p, j - 1) for p in range(j))
                         for j in range(1, height + 1))


def validate(pattern: Pattern) -> None:
    for j, current in enumerate(pattern):
        assert current == column(current)
        assert all(0 <= p < j and 0 <= q < j for p, q in current)


def count(prefix: Pattern, current: Column, budget: Budget | None = None) -> int:
    answer = 1
    while current:
        if budget is not None:
            budget.tick(1 + len(current))
        following = lower(prefix, current)
        assert following < current
        current = following
        answer += 1
    return answer


def counts(pattern: Pattern, budget: Budget | None = None) -> tuple[int, ...]:
    return tuple(count(pattern[:j], c, budget) for j, c in enumerate(pattern))


def display(pattern: Pattern) -> str:
    return "".join("[" + ",".join(f"{p}:{q}" for p, q in c) + "]"
                   for c in pattern) or "0"
