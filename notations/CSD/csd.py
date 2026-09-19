"""CSD: Contextual Stack Diagrams, a research candidate, Python 3.10+.

A record is (parent, word), where word = (head, *nonempty_address_tail).
Parents in each column strictly decrease. There is no sorting, skyline,
deduplication, dominance test, or normalization. Invalid inputs are rejected.

Every coordinate is an address, including possible SELF. Head borrowing
reads an already constructed earlier column. Full well-ordering and ordinal
comparisons with ARD2 / wY have NOT been proved. See definition.zh-CN.md.
The mathematical kernel has no resource guards; bound experiments externally.
"""

from dataclasses import dataclass
from functools import total_ordering

Word = tuple[int, ...]
Record = tuple[int, Word]
Column = tuple[Record, ...]


def natural(value):
    if type(value) is not int or value < 0:
        raise ValueError("Expected a nonnegative integer, not bool")


def word_key(word):
    return word[0], len(word) - 1, word[1:]


def context_tail(column, child):
    """SELF followed by each record's parent and full word, in stack order.

    The result is an address list, not a reversible column serialization.
    """
    tail = [child]
    for parent, word in column:
        tail.append(parent)
        tail.extend(word)
    return tuple(tail)


def lower_word(word, prefix):
    """Lower an already moved word at child=len(prefix); never recurse on FS."""
    head, tail = word[0], word[1:]
    child = len(prefix)
    for position in range(len(tail) - 1, -1, -1):
        if tail[position]:
            return (head, *tail[:position], tail[position] - 1,
                    *((child,) * (len(tail) - position - 1)))
    if len(tail) > 1:
        return (head, *((child,) * (len(tail) - 1)))
    if head:
        return (head - 1, *context_tail(prefix[head - 1], child))
    return None


@total_ordering
@dataclass(frozen=True)
class CSD:
    columns: tuple[Column, ...] = ()

    def __post_init__(self):
        if not isinstance(self.columns, tuple):
            raise ValueError("Use an immutable tuple of columns")
        for child, column in enumerate(self.columns):
            if not isinstance(column, tuple):
                raise ValueError("Use an immutable tuple of records")
            previous = child
            for parent, word in column:
                natural(parent)
                if not parent < previous:
                    raise ValueError("Parents must strictly decrease, below child")
                previous = parent
                if not isinstance(word, tuple) or len(word) < 2:
                    raise ValueError("A word needs a head and a nonempty tail")
                for address in word:
                    natural(address)
                    if address > child:
                        raise ValueError("Address must not exceed child")

    @classmethod
    def seed(cls, n):
        natural(n)
        return cls(tuple(() if j == 0 else ((j - 1, (j, j)),)
                         for j in range(n)))

    def order_key(self):
        return tuple(tuple((p, word_key(w)) for p, w in col)
                     for col in self.columns)

    def __lt__(self, other):
        if not isinstance(other, CSD):
            return NotImplemented
        return self.order_key() < other.order_key()

    def fs(self, n):
        natural(n)
        if not self.columns or n == 0 or not self.columns[-1]:
            return CSD(self.columns[:-1])
        source = self.columns
        last = len(source) - 1
        cut, control = source[-1][-1]
        width = last - cut
        result = list(source[:-1])

        def move_column(column, block):
            def move(address):
                return address if address < cut else address + block * width
            return tuple((move(p), tuple(move(a) for a in word))
                         for p, word in column)

        for block in range(n):
            seam = list(move_column(source[-1][:-1], block))
            parent, moved = move_column(((cut, control),), block)[0]
            lowered = lower_word(moved, result)
            if lowered is not None:
                seam.append((parent, lowered))
            # Source SELF binds to this seam. Its parents all precede cut.
            seam.extend(move_column(source[cut], block + 1))
            result.append(tuple(seam))
            for column in source[cut + 1:last]:
                result.append(move_column(column, block + 1))
        return CSD(tuple(result))

    __getitem__ = fs

    def local_step(self):
        """One frozen-prefix step, not an iterated whole [1] descent."""
        return CSD(self.fs(1).columns[:len(self.columns)])

    def __str__(self):
        return "".join("[" + ";".join(
            f"{p}:({w[0]};{','.join(map(str, w[1:]))})" for p, w in c
        ) + "]" for c in self.columns) or "0"


ZERO = CSD()
# Optional external Top: Top[n] = CSD.seed(n). Top cannot be an address.
