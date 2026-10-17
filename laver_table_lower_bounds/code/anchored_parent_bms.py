"""BMS in parent coordinates, with an IBLP-style index convention.

This is a presentation of ordinary BMS, not a claimed stronger system.
Columns are lists of earlier parent-column indices, one per nonzero row.
On standard terms [2] is ordinary BM4 [1]; [1] retains only its first new
column.  Every basic-sequence computation has explicitly bounded loops.

No M-normalization or descent-to-zero computation occurs inside fs().
The optional BLP encoding is an initial finite pattern, not a proof that
the pattern is realizable below a specified small-period endpoint.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class ParentBMS:
    columns: tuple[tuple[int, ...], ...] = ()

    def __post_init__(self):
        # This is structural validation only, not a standardness decision.
        for j, column in enumerate(self.columns):
            if any(type(p) is not int or not 0 <= p < j for p in column):
                raise ValueError("a parent must be an earlier column")

    @classmethod
    def seed(cls, n):
        """A[n] has the BMS value (0^(n+1))(1^(n+1))(2^(n+1))."""
        if type(n) is not int or n < 0:
            raise ValueError("the index must be a nonnegative integer")
        height = n + 1
        return cls(((), (0,) * height, (1,) * height))

    def fs(self, n):
        if type(n) is not int or n < 0:
            raise ValueError("the index must be a nonnegative integer")
        if not self.columns:
            return self
        if n == 0 or not self.columns[-1]:
            return ParentBMS(self.columns[:-1])

        last = self.columns[-1]
        level = len(last) - 1
        root = last[level]
        end = len(self.columns) - 1
        width = end - root
        result = list(self.columns[:-1])
        copies = max(1, n - 1)
        for block in range(1, copies + 1):
            for j in range(root, end):
                if j == root:
                    lower = tuple(p + (block - 1) * width if p >= root else p
                                  for p in last[:level])
                    column = lower + self.columns[j][level:]
                else:
                    column = tuple(p + block * width if p >= root else p
                                   for p in self.columns[j])
                result.append(column)
                if n == 1:
                    return ParentBMS(tuple(result))
        return ParentBMS(tuple(result))

    __getitem__ = fs

    def order_key(self):
        """Column-lexicographic key, omitting insignificant trailing zeroes."""
        result = []
        for column in self.columns:
            result.append(tuple(
                1 + (result[parent][row] if row < len(result[parent]) else 0)
                for row, parent in enumerate(column)))
        return tuple(result)

    def __lt__(self, other):
        if not isinstance(other, ParentBMS):
            return NotImplemented
        return self.order_key() < other.order_key()

    def matrix(self):
        """Recover standard BM4 entries by bounded parent-depth recursion."""
        values = self.order_key()
        height = max(1, max(map(len, values), default=0))
        return tuple(c + (0,) * (height - len(c)) for c in values)

    def blp(self, height=None):
        """Return rows and steps of the balanced BLP realization problem."""
        actual_height = max((len(c) for c in self.columns), default=0)
        if height is None:
            height = actual_height
        if type(height) is not int or height < actual_height:
            raise ValueError("height is too small")
        width = height + 1
        rows = [(0, 1, 2), (0, 1, 2, 3)]
        steps = [1, 1]
        for j, column in enumerate(self.columns):
            base = 3 + j * width
            for k in range(width):
                address = base + k
                if k == 0 or k > len(column):
                    rows.append((0, address, address + 1))
                    steps.append(1)
                else:
                    source = 3 + column[k - 1] * width
                    rows.append(tuple(range(source, source + k + 1))
                                + tuple(range(base, address + 2)))
                    steps.append(k + 1)
        return tuple(rows), tuple(steps)

    def __str__(self):
        return "".join("[" + ",".join(map(str, c)) + "]" for c in self.columns) or "0"


if __name__ == "__main__":
    # Only construct a small exact seed; never descend it to zero here.
    seed = ParentBMS.seed(10)
    rows, steps = seed.blp()
    print(seed)
    print("height=11, columns=3, BLP_rows=", len(rows))
