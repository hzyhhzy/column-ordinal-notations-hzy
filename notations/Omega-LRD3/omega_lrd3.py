"""Omega-LRD3, a standalone finite definition; Python 3.10+, standard library.

Each column stores (row_graph, parent, maximum_root). A maximum q represents
all roots 0,...,q. Nested rows are finite OmegaLRD3 objects, never TOP.
Construction checks finite graph structure, NOT reachability from TOP.
Comparison is by (parent, row, root); control selection is by (row, root, parent).
The row packet at seam b uses indices 0 THROUGH b. Seeds add ONE column.

There are no mathematical truncations, caches, width limits, or time limits.
Large inputs can exhaust memory or Python's recursion limit. CLI arguments
are a finite expansion path starting at TOP. Example: python omega_lrd3.py 3 2.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import total_ordering


def _nat(n: int) -> int:
    if type(n) is not int or n < 0:
        raise ValueError("expected a nonnegative integer")
    return n


@total_ordering
@dataclass(frozen=True)
class OmegaLRD3:
    columns: tuple[tuple[tuple[OmegaLRD3, int, int], ...], ...] | None = ()

    def __post_init__(self):
        if self.columns is None:
            return
        columns = []
        for j, column in enumerate(self.columns):
            groups = {}
            for row, p, q in column:
                if not isinstance(row, OmegaLRD3) or row.columns is None:
                    raise TypeError("a row must be a finite OmegaLRD3 expression, not TOP")
                p, q = _nat(p), _nat(q)
                if not q <= p < j:
                    raise ValueError("a relation must satisfy 0 <= root <= parent < child")
                groups[row, p] = max(q, groups.get((row, p), -1))
            columns.append(tuple(sorted(
                ((row, p, q) for (row, p), q in groups.items()),
                key=lambda e: (e[1], e[0], e[2]), reverse=True,
            )))
        object.__setattr__(self, "columns", tuple(columns))

    @classmethod
    def integer(cls, n: int) -> OmegaLRD3:
        return cls(((),) * _nat(n))

    @classmethod
    def seed(cls, n: int) -> OmegaLRD3:
        value = cls()
        for _ in range(_nat(n)):
            width = len(value.columns)
            column = ((value, width - 1, width - 1),) if width else ()
            value = cls(value.columns + (column,))
        return value

    @property
    def is_integer(self) -> bool:
        return self.columns is not None and not any(self.columns)

    @property
    def kind(self) -> str:
        if self.columns is None:
            return "limit"
        if not self.columns:
            return "zero"
        return "limit" if self.columns[-1] else "successor"

    def __lt__(self, other):
        if not isinstance(other, OmegaLRD3):
            return NotImplemented
        if self.columns is None:
            return False
        if other.columns is None:
            return True
        def key(graph):
            return tuple(tuple((p, row, q) for row, p, q in column)
                         for column in graph.columns)
        return key(self) < key(other)

    def fs(self, n: int) -> OmegaLRD3:
        n = _nat(n)
        if self.columns is None:
            return OmegaLRD3.seed(n)
        if not self.columns:
            return self
        base, templates = self.columns[:-1], self.columns[-1]
        if n == 0 or not templates:
            return OmegaLRD3(base)

        K, c, r = max(templates, key=lambda e: (e[0], e[2], e[1]))
        x = len(base)
        block = x - c
        columns = [[] for _ in range(x + n * block)]
        for b in range(n + 1):
            def move(i):
                return i if i < c else i + b * block

            for j, column in enumerate(base):
                columns[move(j)].extend((row, move(p), move(q))
                                        for row, p, q in column)
            if b == n:
                break
            seam = columns[x + b * block]
            for row, p, q in templates:
                allowed = move(q) if row < K else min(move(q), move(r) - 1)
                if row <= K and allowed >= 0:
                    seam.append((row, move(p), allowed))
            if not K.is_integer:
                packet = {OmegaLRD3()} | {K[t] for t in range(b + 1)}
                seam.extend((row, move(c), move(c)) for row in packet)
        return OmegaLRD3(columns)

    __getitem__ = fs

    def __str__(self):
        if self.columns is None:
            return "Limit"
        if not self.columns:
            return "∅"
        def row_text(row):
            return str(len(row.columns)) if row.is_integer else "{" + str(row) + "}"
        return "".join(
            "[" + ",".join(f"({row_text(row)},{p},{q})" for row, p, q in column) + "]"
            for column in self.columns
        )


ZERO = OmegaLRD3()
TOP = OmegaLRD3(None)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Omega-LRD3: expand TOP along a finite path")
    parser.add_argument("indices", nargs="*", type=int, help="successive fundamental-sequence indices")
    args = parser.parse_args()
    value = TOP
    for index in args.indices:
        value = value[index]
    print(value)
