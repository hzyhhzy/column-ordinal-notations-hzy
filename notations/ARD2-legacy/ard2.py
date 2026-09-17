"""ARD2: full-context anchored row diagrams; Python 3.10+, standard library only.

A column consists of (row, parent, maximum_root) triples. At child j,
0 <= row, maximum_root <= j and 0 <= parent < j. Maximum root q denotes
all roots 0,...,q. Row and root SELF references move with their child.

ARD2() is zero; TOP is the external limit; a[n] means a.fs(n).
The standard domain consists of finite descendants of the seeds, plus TOP.
The constructor checks structural legality, not membership in that domain.
Ordinary Lean proves well-founded expansion on all legal graphs and a well-order
on the standard domain: ../../lean/ARD2-legacy/src/ARD2Final.lean. The weak-theory paper is
../../proofs/paper/ard2-legacy-well-ordering.md; its KP derivation is not encoded inside
Lean. No order-type comparison or optimal axiom bound is established.

No parser, graphics, caching or resource guards are part of this definition.
Python integers are exact. Large expansion indices can allocate huge graphs;
use caller-controlled time, width and memory bounds for experiments.
"""

from dataclasses import dataclass
from functools import total_ordering


Edge = tuple[int, int, int]
Column = tuple[Edge, ...]


def _natural(value: int) -> None:
    if type(value) is not int or value < 0:
        raise ValueError("A nonnegative integer is required; bool is not accepted")


def _edge_key(edge: Edge) -> tuple[int, int, int]:
    row, parent, root = edge
    return parent, row, root


@total_ordering
@dataclass(frozen=True)
class ARD2:
    columns: tuple[Column, ...] | None = ()

    def __post_init__(self) -> None:
        if self.columns is None:
            return
        columns = []
        for child, column in enumerate(self.columns):
            groups = {}
            for row, parent, root in column:
                for value in (row, parent, root):
                    _natural(value)
                if not (row <= child and root <= child and parent < child):
                    raise ValueError("Require row, root <= child and parent < child")
                groups[row, parent] = max(root, groups.get((row, parent), -1))
            edges = ((k, p, q) for (k, p), q in groups.items())
            columns.append(tuple(sorted(edges, key=_edge_key, reverse=True)))
        object.__setattr__(self, "columns", tuple(columns))

    @classmethod
    def finite(cls, n: int) -> "ARD2":
        """The natural number n: exactly n empty columns."""
        _natural(n)
        return cls(tuple(() for _ in range(n)))

    @classmethod
    def seed(cls, n: int) -> "ARD2":
        """S_n has n columns: C_0 is empty and C_j={(j,j-1,j)} for j>0."""
        _natural(n)
        return cls(tuple(() if j == 0 else ((j, j - 1, j),) for j in range(n)))

    @property
    def kind(self) -> str:
        if self.columns is None:
            return "limit"
        if not self.columns:
            return "zero"
        return "limit" if self.columns[-1] else "successor"

    def _order_key(self) -> tuple:
        if self.columns is None:
            return (1, ())
        return (0, tuple(tuple(_edge_key(e) for e in c) for c in self.columns))

    def __lt__(self, other: "ARD2") -> bool:
        if not isinstance(other, ARD2):
            return NotImplemented
        return self._order_key() < other._order_key()

    def fs(self, n: int) -> "ARD2":
        """The nth fundamental-sequence term; finite nonzero a[0] deletes a column."""
        _natural(n)
        if self.columns is None:
            return self.seed(n)
        if not self.columns:
            return self
        if n == 0 or not self.columns[-1]:
            return ARD2(self.columns[:-1])

        last = len(self.columns) - 1
        # Control order differs from column order: row, root, then parent.
        row, cut, root = max(self.columns[-1], key=lambda e: (e[0], e[2], e[1]))
        width = last - cut
        result = [[] for _ in range(last + n * width)]
        for j in range(cut):
            result[j].extend(self.columns[j])

        for block in range(n + 1):
            def move(i: int) -> int:
                return i if i < cut else i + block * width

            # Move every coordinate, including row SELF and root SELF.
            for j in range(cut, last):
                result[move(j)].extend((move(k), move(p), move(q))
                                       for k, p, q in self.columns[j])
            if block == n:
                break
            child = last + block * width
            seam = result[child]
            for k, p, q in self.columns[-1]:
                lowered = move(q) if k < row else min(move(q), move(root) - 1)
                if k <= row and lowered >= 0:
                    seam.append((move(k), move(p), lowered))
            # The whole root context includes the new seam, not just its parent.
            seam.extend((k, move(cut), child) for k in range(move(row)))
        return ARD2(tuple(tuple(c) for c in result))

    __getitem__ = fs

    def local_step(self) -> "ARD2":
        """Retain only the old-width prefix of a positive expansion.

        A nonempty last column is replaced, not deleted. An empty one is
        deleted. Repeating this with a fixed prefix defines its local count;
        it is not the same as iterating the full fundamental sequence.
        """
        if self.columns is None:
            raise ValueError("TOP has no frozen-prefix local step")
        if not self.columns or not self.columns[-1]:
            return ARD2(self.columns[:-1])
        last = len(self.columns) - 1
        row, cut, root = max(self.columns[-1], key=lambda e: (e[0], e[2], e[1]))
        # Source C_cut shares the seam: both kinds of SELF must be rebound.
        column = [(last if k == cut else k, p, last if q == cut else q)
                  for k, p, q in self.columns[cut]]
        for k, p, q in self.columns[-1]:
            lowered = q if k < row else min(q, root - 1)
            if k <= row and lowered >= 0:
                column.append((k, p, lowered))
        column.extend((k, cut, last) for k in range(row))
        return ARD2((*self.columns[:-1], tuple(column)))

    def __str__(self) -> str:
        if self.columns is None:
            return "Limit of ARD2-legacy"
        return "".join("[" + ",".join(f"({k},{p},{q})" for k, p, q in c) + "]"
                       for c in self.columns) or "∅"


ZERO = ARD2()
TOP = ARD2(None)
