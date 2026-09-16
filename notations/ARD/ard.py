"""ARD (Anchored Row Diagrams), skyline edition; Python 3.10+, standard library.

A column stores triples (anchor, parent, maximum_root), with anchor and root
at most parent, and parent earlier than the column. Dominated records are
discarded: parents decrease while the pairs (anchor, root) strictly increase.

Only the last column is replaced, followed by copies of the source suffix.
This readable definition omits parsing, counting, diagrams and resource limits.
Integers have arbitrary precision. Large indices can require enormous outputs.
Constructors check raw validity, not membership in the seed-generated domain.
"""

from dataclasses import dataclass
from functools import total_ordering

Edge = tuple[int, int, int]
Column = tuple[Edge, ...]


def _natural(value: int) -> None:
    if type(value) is not int or value < 0:
        raise ValueError("Expected a nonnegative integer (not bool)")


def _column_key(edge: Edge) -> tuple[int, int, int]:
    anchor, parent, root = edge
    return parent, anchor, root


def skyline(column) -> Column:
    """Keep the greatest (anchor, root) at each parent, then the record highs."""
    by_parent = {}
    for anchor, parent, root in column:
        by_parent[parent] = max((anchor, root), by_parent.get(parent, (-1, -1)))
    result = []
    highest = (-1, -1)
    for parent in sorted(by_parent, reverse=True):
        pair = by_parent[parent]
        if pair > highest:
            result.append((pair[0], parent, pair[1]))
            highest = pair
    return tuple(result)


def predecessor(edge: Edge) -> Column:
    """Predecessor of a MOVED controller; do not move after decrementing."""
    anchor, parent, root = edge
    if root:
        return ((anchor, parent, root - 1),)
    if anchor:
        return ((anchor - 1, parent, parent),)
    return ()


@total_ordering
@dataclass(frozen=True)
class AnchoredRows:
    # None is the external top; () is zero; ((),) is one.
    columns: tuple[Column, ...] | None = ()

    def __post_init__(self) -> None:
        if self.columns is None:
            return
        normalized = []
        for child, column in enumerate(self.columns):
            edges = []
            for anchor, parent, root in column:
                for value in (anchor, parent, root):
                    _natural(value)
                if not (anchor <= parent < child and root <= parent):
                    raise ValueError(f"Column {child}: require 0 <= anchor, root <= parent < child")
                edges.append((anchor, parent, root))
            normalized.append(skyline(edges))
        object.__setattr__(self, "columns", tuple(normalized))

    @classmethod
    def finite(cls, n: int) -> "AnchoredRows":
        _natural(n)
        return cls(tuple(() for _ in range(n)))

    @classmethod
    def seed(cls, n: int) -> "AnchoredRows":
        _natural(n)
        return cls(tuple(() if j == 0 else ((j - 1, j - 1, j - 1),) for j in range(n)))

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
        return (0, tuple(tuple(_column_key(e) for e in col) for col in self.columns))

    def __lt__(self, other: "AnchoredRows") -> bool:
        if not isinstance(other, AnchoredRows):
            return NotImplemented
        return self._order_key() < other._order_key()

    def fs(self, n: int) -> "AnchoredRows":
        _natural(n)
        if self.columns is None:
            return self.seed(n)
        if not self.columns:
            return self
        front = list(self.columns[:-1])
        if n == 0 or not self.columns[-1]:
            return AnchoredRows(tuple(front))

        column = self.columns[-1]
        control = column[-1]
        cut = control[1]
        width = len(self.columns) - 1 - cut

        def move(edge: Edge, block: int) -> Edge:
            return tuple(i if i < cut else i + block * width for i in edge)

        for block in range(n):
            seam = tuple(move(e, block) for e in column[:-1])
            seam += predecessor(move(control, block)) + self.columns[cut]
            front.append(skyline(seam))
            for source in self.columns[cut + 1:-1]:
                front.append(tuple(move(e, block + 1) for e in source))
        return AnchoredRows(tuple(front))

    __getitem__ = fs

    def __str__(self) -> str:
        if self.columns is None:
            return "Limit of ARD"
        if not self.columns:
            return "∅"
        return "".join("[" + ",".join(f"({k},{p},{q})" for k, p, q in col) + "]"
                       for col in self.columns)


ZERO = AnchoredRows()
TOP = AnchoredRows(None)
