"""Minimal LRD definition; Python 3.10+, standard library only.

Row((a0, ..., ad)) means w**d*ad + ... + a0; Row(None) means w**w.
LRD.columns is a tuple of columns, each containing (row, parent, max_root).
Such a triple represents ALL roots from 0 through max_root. Construction
merges equal (row, parent) groups, then sorts by (parent, row, root) descending.
Column numbers start at zero. Construction checks graph structure, not whether
the graph is reachable from T.

Example: T[2][1], or LRD(((), ((Row((0, 1)), 0, 0),)))[2].
There are no runtime limits: large expansions may use large amounts of memory.
"""

from dataclasses import dataclass
from functools import total_ordering


def _nat(n: int) -> int:
    if type(n) is not int or n < 0:
        raise ValueError("expected a nonnegative integer")
    return n


@total_ordering
@dataclass(frozen=True)
class Row:
    coeffs: tuple[int, ...] | None = (0,)

    def __post_init__(self):
        if self.coeffs is not None:
            coeffs = tuple(_nat(a) for a in self.coeffs) or (0,)
            while len(coeffs) > 1 and coeffs[-1] == 0:
                coeffs = coeffs[:-1]
            object.__setattr__(self, "coeffs", coeffs)

    def __lt__(self, other):
        if not isinstance(other, Row):
            return NotImplemented
        if self.coeffs is None:
            return False
        if other.coeffs is None:
            return True
        return (len(self.coeffs), self.coeffs[::-1]) < (
            len(other.coeffs), other.coeffs[::-1]
        )

    @property
    def finite(self) -> bool:
        return self.coeffs is not None and len(self.coeffs) == 1

    def fs(self, n: int):
        n = _nat(n)
        if self.coeffs is None:
            return Row((0,) * (n + 1) + (1,))
        if self.coeffs == (0,):
            return self
        coeffs = list(self.coeffs)
        d = next(i for i, a in enumerate(coeffs) if a)
        coeffs[d] -= 1
        if d:
            coeffs[d - 1] = n + 1
        return Row(tuple(coeffs))

    __getitem__ = fs

    def __str__(self):
        if self.coeffs is None:
            return "w^w"
        terms = []
        for d in range(len(self.coeffs) - 1, -1, -1):
            a = self.coeffs[d]
            if not a:
                continue
            term = str(a) if d == 0 else "w" if d == 1 else f"w^{d}"
            if d and a != 1:
                term += f"*{a}"
            terms.append(term)
        return "+".join(terms) or "0"


@total_ordering
@dataclass(frozen=True)
class LRD:
    columns: tuple[tuple[tuple[Row, int, int], ...], ...] = ()

    def __post_init__(self):
        columns = []
        for j, column in enumerate(self.columns):
            groups = {}
            for row, p, q in column:
                if not isinstance(row, Row):
                    raise TypeError("a relation's row must be a Row")
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
    def seed(cls):
        return cls(((), ((Row(None), 0, 0),)))

    def __lt__(self, other):
        if not isinstance(other, LRD):
            return NotImplemented
        def key(graph):
            return tuple(tuple((p, row, q) for row, p, q in column)
                         for column in graph.columns)
        return key(self) < key(other)

    def fs(self, n: int):
        n = _nat(n)
        if not self.columns:
            return self
        base, templates = self.columns[:-1], self.columns[-1]
        if n == 0 or not templates:
            return LRD(base)

        # Control priority is (row, root, parent), NOT the comparison key.
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
            # LRD uses indices THROUGH b; Omega-LRD instead goes through b+1.
            if not K.finite:
                packet = {Row()} | {K[t] for t in range(b + 1)}
                seam.extend((row, move(c), move(c)) for row in packet)
        return LRD(columns)

    __getitem__ = fs

    def __str__(self):
        if not self.columns:
            return "∅"
        return "".join("[" + ",".join(f"({row},{p},{q})" for row, p, q in column)
                       + "]" for column in self.columns)


ZERO = LRD()
T = LRD.seed()
TOP = T


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="LRD: expand the seed T along a finite path")
    parser.add_argument("indices", nargs="*", type=int, help="successive fundamental-sequence indices")
    args = parser.parse_args()
    value = T
    for index in args.indices:
        value = value[index]
    print(value)
