"""ARD2: skyline full-context anchored row diagrams; Python 3.10+, stdlib.

A column consists of (row, parent, maximum_root) triples. At child j,
0 <= row, maximum_root <= j and 0 <= parent < j. Maximum root q denotes
all roots 0,...,q. Row and root SELF references move with their child.
Parents decrease and (row, root) pairs strictly increase within each skyline.

ARD2() is zero; TOP is the external limit; a[n] means a.fs(n).
The standard domain consists of finite descendants of the seeds, plus TOP.
The constructor checks structural legality, not membership in that domain.
Ordinary Lean proves well-founded expansion on all legal graphs and a well-order
on the standard domain: ../../lean/ARD2/src/ARD2SkylineFinal.lean. The weak-theory paper is
../../proofs/paper/ard2-well-ordering.md; its KP derivation is not encoded inside
Lean. The paper proves exact skyline equivalence with ARD2-legacy; this
equivalence is not yet formalized in Lean. No optimal axiom bound is claimed.

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


def skyline(column) -> Column:
    """One maximum pair per parent, followed by the strict record highs."""
    by_parent = {}
    for row, parent, root in column:
        by_parent[parent] = max((row, root), by_parent.get(parent, (-1, -1)))
    result, highest = [], (-1, -1)
    for parent in sorted(by_parent, reverse=True):
        pair = by_parent[parent]
        if pair > highest:
            result.append((pair[0], parent, pair[1]))
            highest = pair
    return tuple(result)


def predecessor(edge: Edge, child: int) -> Column:
    """Lower a MOVED controller; borrow the seam child, never its parent."""
    row, parent, root = edge
    if root:
        return ((row, parent, root - 1),)
    if row:
        return ((row - 1, parent, child),)
    return ()


@total_ordering
@dataclass(frozen=True)
class ARD2:
    columns: tuple[Column, ...] | None = ()

    def __post_init__(self) -> None:
        if self.columns is None:
            return
        columns = []
        for child, column in enumerate(self.columns):
            edges = []
            for row, parent, root in column:
                for value in (row, parent, root):
                    _natural(value)
                if not (row <= child and root <= child and parent < child):
                    raise ValueError("Require row, root <= child and parent < child")
                edges.append((row, parent, root))
            columns.append(skyline(edges))
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
        column = self.columns[-1]
        control = column[-1]
        cut = control[1]
        width = last - cut
        result = list(self.columns[:-1])

        def move(edge: Edge, block: int) -> Edge:
            return tuple(i if i < cut else i + block * width for i in edge)

        for block in range(n):
            child = last + block * width
            seam = tuple(move(e, block) for e in column[:-1])
            seam += predecessor(move(control, block), child)
            # The next block's first column shares this seam. Moving by block+1
            # rebinds BOTH SELF coordinates in C_cut to the new child.
            seam += tuple(move(e, block + 1) for e in self.columns[cut])
            result.append(skyline(seam))
            result.extend(tuple(move(e, block + 1) for e in source)
                          for source in self.columns[cut + 1:last])
        return ARD2(tuple(result))

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
        control = self.columns[-1][-1]
        cut = control[1]
        # Source C_cut shares the seam: both kinds of SELF must be rebound.
        column = [(last if k == cut else k, p, last if q == cut else q)
                  for k, p, q in self.columns[cut]]
        column.extend(self.columns[-1][:-1])
        column.extend(predecessor(control, last))
        return ARD2((*self.columns[:-1], tuple(column)))

    def __str__(self) -> str:
        if self.columns is None:
            return "Limit of ARD2"
        return "".join("[" + ",".join(f"({k},{p},{q})" for k, p, q in c) + "]"
                       for c in self.columns) or "∅"


ZERO = ARD2()
TOP = ARD2(None)
