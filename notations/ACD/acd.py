"""ACD candidate: Ancestral-Context Diagrams, 2026-09-18.

A column is a finite parent -> head-source map. Both references point left.
The profile of a referenced column is its canonically renumbered ancestor
diagram, compared by the SAME recursive column order. No tree parameters,
ordinal labels, levels, or operation histories are stored in expressions.

This is a conjectural design, not a proved well-order or a proved extension
of BTBMS, e0MN, or IPD. Only descendants of compatible seeds are standard.
"""


class ACD:
    def __init__(self, columns=()):
        self.columns = []
        self.ancestors = []
        self.views = []
        self.comparisons = {}
        for column in columns:
            self.append(column)

    def head_compare(self, left, right):
        """Compare canonically renumbered closed ancestor diagrams.

        A view stores (local_parent, original_head, local_head). The original
        head address is only a memoized link into an earlier, smaller view.
        This is native diagram lexicographic order, NOT a tree path order.
        """
        if left == right:
            return 0
        pair = left, right
        if pair in self.comparisons:
            return self.comparisons[pair]
        a, b = self.views[left], self.views[right]
        result = 0
        for x, y in zip(a, b):
            for (p, h, local_h), (q, k, local_k) in zip(x, y):
                result = ((p > q) - (p < q) or self.head_compare(h, k)
                          or (local_h > local_k) - (local_h < local_k))
                if result:
                    break
            if not result:
                result = (len(x) > len(y)) - (len(x) < len(y))
            if result:
                break
        if not result:
            result = (len(a) > len(b)) - (len(a) < len(b))
        self.comparisons[pair] = result
        return result

    def source_compare(self, left, right):
        """Canonical representative of a tied semantic head: later address."""
        return self.head_compare(left, right) or (left > right) - (left < right)

    def normalize(self, column, child):
        parents = {}
        for parent, head in column:
            if (type(parent) is not int or type(head) is not int
                    or not 0 <= parent < child or not 0 <= head < child):
                raise ValueError("Both references must point to earlier columns")
            if parent not in parents or self.source_compare(head, parents[parent]) > 0:
                parents[parent] = head
        return tuple(sorted(parents.items(), reverse=True))

    def append(self, column):
        child = len(self.columns)
        column = self.normalize(column, child)
        self.columns.append(column)
        ancestors = {child}
        for parent, head in column:
            ancestors.update(self.ancestors[parent])
            ancestors.update(self.ancestors[head])
        ancestors = tuple(sorted(ancestors))
        address = {old: new for new, old in enumerate(ancestors)}
        view = tuple(tuple((address[p], h, address[h]) for p, h in self.columns[j])
                     for j in ancestors)
        self.ancestors.append(ancestors)
        self.views.append(view)

    def ancestor_view(self, child):
        """An actual diagram, without the temporary original-address links."""
        return tuple(tuple((p, local_h) for p, _, local_h in c) for c in self.views[child])

    def control(self, column):
        result = column[0]
        for parent, head in column[1:]:
            relation = self.head_compare(head, result[1])
            if relation > 0 or relation == 0 and parent > result[0]:
                result = parent, head
        return result

    def lower_column(self, column, child):
        """The left context is fixed; no copied suffix is constructed."""
        cut, head = self.control(column)
        smaller = [i for i in range(child) if self.head_compare(i, head) < 0]
        predecessor = None
        for i in smaller:
            if predecessor is None or self.source_compare(i, predecessor) > 0:
                predecessor = i
        result = [(p, h) for p, h in column if p != cut]
        if predecessor is not None:
            result.append((cut, predecessor))
        result.extend(self.columns[cut])
        return cut, self.normalize(result, child)

    def reflect(self):
        """Lower the last column, then copy the tail INCLUDING its template."""
        last = len(self.columns) - 1
        cut, seam = self.lower_column(self.columns[last], last)
        span = last - cut
        move = lambda i: i if i < cut else i + span
        result = ACD(self.columns[:last])
        result.append(seam)
        for column in self.columns[cut + 1:]:
            result.append((move(p), move(h)) for p, h in column)
        return result

    def fs(self, index):
        if type(index) is not int or index < 0:
            raise ValueError("A natural index is required")
        if not self.columns:
            return ACD()
        result = self
        if self.columns[-1]:
            for _ in range(index):
                result = result.reflect()
        return ACD(result.columns[:-1])

    def counts(self, tick=lambda: None):
        """Exact local countdowns, including the final deletion of an empty column.

        An experimental caller should pass a bounded tick callback. Python
        integers are unbounded. This does NOT run a global descent to zero.
        """
        answer = []
        for child, column in enumerate(self.columns):
            count = 1
            while column:
                tick()
                _, column = self.lower_column(column, child)
                count += 1
            answer.append(count)
        return tuple(answer)

    def compare(self, other):
        for a, b in zip(self.columns, other.columns):
            if a == b:
                continue
            # Earlier columns agree. Head references in this first differing
            # column therefore have the same meaning in both expressions.
            for (p, h), (q, k) in zip(a, b):
                result = (p > q) - (p < q) or self.source_compare(h, k)
                if result:
                    return result
            return (len(a) > len(b)) - (len(a) < len(b))
        return (len(self.columns) > len(other.columns)) - (len(self.columns) < len(other.columns))

    @classmethod
    def seed(cls, index):
        if type(index) is not int or index < 0:
            raise ValueError("A natural index is required")
        return cls([()] + [((j - 1, j - 1),) for j in range(1, index + 1)])

    def __str__(self):
        return ''.join('[' + ';'.join(f'{p}:{h}' for p, h in column) + ']'
                       for column in self.columns) or '0'


# The external top is an entrance, not another column kind:
#   Top[index] = ACD.seed(index).
# In particular seed(0) is one empty column, while ACD() is zero.
