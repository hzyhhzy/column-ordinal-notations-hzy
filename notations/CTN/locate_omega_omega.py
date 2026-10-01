"""Symbolic leftmost unbounded-height search in the low-formula CTN fragment.

This does not expand fundamental sequences or materialize tens of millions
of table entries. Correctness for the finite fragment is proved separately.
It deliberately rejects formulas outside the audited one-quantifier range.
"""

from dataclasses import dataclass
from math import isqrt

import ctn_table as t
from ctn_sparse import SparseTable, metadata


@dataclass(frozen=True)
class Shape:
    """A finite or cofinite set: default bit, with finitely many exceptions."""
    default: bool
    exceptions: frozenset = frozenset()

    def contains(self, n):
        return self.default != (n in self.exceptions)

    def subset(self, other):
        if self.default and not other.default:
            return False
        return all(not self.contains(n) or other.contains(n)
                   for n in self.exceptions | other.exceptions)

    def complement(self):
        return Shape(not self.default, self.exceptions)

    def intersection(self, other):
        default = self.default and other.default
        exceptions = frozenset(n for n in self.exceptions | other.exceptions
                               if (self.contains(n) and other.contains(n)) != default)
        return Shape(default, exceptions)

    def union(self, other):
        return self.complement().intersection(other.complement()).complement()


EMPTY, ALL = Shape(False), Shape(True)


def roots(polynomial):
    """Nonnegative integer zeros of c + b*x + a*x*x."""
    c, b, a = polynomial
    if a == 0:
        if b == 0:
            return ALL if c == 0 else EMPTY
        return Shape(False, frozenset([-c // b])) if -c % b == 0 and -c // b >= 0 else EMPTY
    discriminant = b * b - 4 * a * c
    if discriminant < 0:
        return EMPTY
    square = isqrt(discriminant)
    if square * square != discriminant:
        return EMPTY
    found = set()
    for numerator in (-b + square, -b - square):
        if numerator % (2 * a) == 0 and numerator // (2 * a) >= 0:
            found.add(numerator // (2 * a))
    return Shape(False, frozenset(found))


class Rows:
    """Row equality, exact shapes, lower shapes, and known membership bits."""
    def __init__(self):
        self.parent, self.exact, self.lower, self.bits = {}, {}, {}, {}

    def find(self, row):
        if row not in self.parent:
            self.parent[row] = row
            self.lower[row], self.bits[row] = EMPTY, {}
        while row != self.parent[row]:
            row = self.parent[row]
        return row

    def accepts(self, row, shape, lower=False):
        row = self.find(row)
        if row in self.exact:
            return shape.subset(self.exact[row]) if lower else shape == self.exact[row]
        if lower:
            return all(bit or not shape.contains(n) for n, bit in self.bits[row].items())
        return (self.lower[row].subset(shape)
                and all(shape.contains(n) == bool(bit) for n, bit in self.bits[row].items()))

    def assign(self, row, shape, lower=False):
        row = self.find(row)
        assert self.accepts(row, shape, lower)
        if lower:
            self.lower[row] = self.lower[row].union(shape)
        else:
            self.exact[row] = shape

    def compatible(self, left, right):
        left, right = self.find(left), self.find(right)
        if left == right:
            return True
        if left in self.exact and not self.accepts(right, self.exact[left]):
            return False
        if right in self.exact and not self.accepts(left, self.exact[right]):
            return False
        for a, b in ((left, right), (right, left)):
            if any((n in self.bits[b] and self.bits[b][n] != bit)
                   or (not bit and self.lower[b].contains(n))
                   for n, bit in self.bits[a].items()):
                return False
        return True

    def merge(self, left, right):
        assert self.compatible(left, right)
        left, right = self.find(left), self.find(right)
        if left == right:
            return
        self.parent[right] = left
        self.bits[left].update(self.bits[right])
        self.lower[left] = self.lower[left].union(self.lower[right])
        if right in self.exact:
            self.exact[left] = self.exact[right]

    def bit(self, row, number):
        row = self.find(row)
        if row in self.exact:
            bit = int(self.exact[row].contains(number))
        else:
            bit = self.bits[row].get(number, int(self.lower[row].contains(number)))
        assert self.bits[row].get(number, bit) == bit
        self.bits[row][number] = bit
        return bit


def comprehension_shape(code, numbers, sets, rows):
    """Return Shape or ('row', r); the new number variable is x."""
    op, body = t.unpair(code)
    if op == t.EXISTS_S:
        if body > 5:
            raise ValueError('Outside the audited existential-set fragment')
        return comprehension_shape(body, numbers, sets, rows)
    if op == t.EXISTS_N:
        if body in (0, 1, 4, 6):
            return ALL
        if body == 3:
            return EMPTY
        if body == 2:
            return Shape(False, frozenset([0]))
        if body == 5:
            return ALL if numbers[0] == 0 else EMPTY
        raise ValueError('Outside the audited existential-number fragment')
    if op == t.NOT:
        return comprehension_shape(body, numbers, sets, rows).complement()
    if op == t.AND:
        left, right = t.unpair(body)
        return comprehension_shape(left, numbers, sets, rows).intersection(
            comprehension_shape(right, numbers, sets, rows))

    def variable(index):
        return (0, 1, 0) if index == 0 else (numbers[index - 1], 0, 0)

    if op == t.ZERO:
        return roots(variable(body))
    i, rest = t.unpair(body)
    if op == t.MEMBER:
        return ('row', sets[rest]) if i == 0 else (ALL if rows.bit(sets[rest], numbers[i - 1]) else EMPTY)
    if op in (t.EQUAL, t.SUCC):
        left, right = variable(i), variable(rest)
        difference = [left[k] - right[k] for k in range(3)]
        difference[0] += int(op == t.SUCC)
        return roots(difference)
    j, k = t.unpair(rest)
    left, right, target = variable(i), variable(j), variable(k)
    if op == t.ADD:
        polynomial = [left[p] + right[p] - target[p] for p in range(3)]
    elif op == t.MUL:
        polynomial = [left[0] * right[0] - target[0],
                      left[0] * right[1] + left[1] * right[0] - target[1],
                      left[1] * right[1] - target[2]]
    else:
        raise ValueError((code, op))
    return roots(polynomial)


def actual_truth(code, numbers, sets, rows):
    # For a nonempty context, evaluate the exact comprehension shape at its
    # head coordinate. This is ordinary semantic truth, not the deferred bit.
    op, body = t.unpair(code)
    if numbers:
        shape = comprehension_shape(code, numbers[1:], sets, rows)
        return rows.bit(shape[1], numbers[0]) if isinstance(shape, tuple) else int(shape.contains(numbers[0]))
    if op == t.EXISTS_N and body in (0, 1, 4, 6):
        return 1
    if op == t.EXISTS_N and body == 3:
        return 0
    raise ValueError(('Unexpected scoped empty number context', code))


def locate(max_address=30_000_000):
    fields = metadata(max_address)
    rows, entries = Rows(), {}
    caps, truth_constraints = {}, {}
    relaxed_comprehensions = []
    stop = None
    for address in sorted(fields):
        field = fields[address]
        kind = field[0]
        if kind == t.MEMBERSHIP:
            row, number = t.unpair(field[1])
            entries[address] = rows.bit(row, number)
            continue
        _, payload, _, code, nc, sc, numbers, sets = field
        op, body = t.unpair(code)
        if kind == t.COMPREHENSION:
            shape = comprehension_shape(code, numbers, sets, rows)
            lower = op in (t.EXISTS_N, t.EXISTS_S)
            row = 0
            while not (rows.compatible(row, shape[1]) if isinstance(shape, tuple)
                       else rows.accepts(row, shape, lower)):
                row += 1
                if row > 10_000:
                    raise RuntimeError('Bounded experiment: too many row trials')
            if isinstance(shape, tuple):
                rows.merge(row, shape[1])
            else:
                rows.assign(row, shape, lower)
                representative = rows.find(row)
                if lower and representative in rows.exact and shape != rows.exact[representative]:
                    relaxed_comprehensions.append((address, code, numbers, sets, row))
            entries[address], caps[payload] = row, row
        elif kind == t.TRUTH:
            actual = actual_truth(code, numbers, sets, rows)
            chosen = actual
            if numbers:
                cp = t.context(code, numbers[1:], sets)
                if cp in caps:
                    chosen = rows.bit(caps[cp], numbers[0])
            if op not in (t.EXISTS_N, t.EXISTS_S):
                assert chosen == actual, (address, code, numbers, chosen, actual)
            else:
                assert chosen >= actual, (address, code, numbers)
                truth_constraints[payload] = (chosen, actual)
            entries[address] = chosen
        elif kind == t.WITNESS and op in (t.EXISTS_N, t.EXISTS_S):
            chosen, actual = truth_constraints[payload]
            if chosen and not actual:
                stop = dict(address=address, code=code, numbers=numbers, sets=sets)
                break
            witness = numbers[0] if chosen and op == t.EXISTS_N and body == 4 else 0
            entries[address] = witness

    if stop is None:
        raise RuntimeError('No stopping field within the bounded fragment')
    length = stop['address']
    entries = {i: v for i, v in entries.items() if i < length}
    table = SparseTable(length, entries)
    for address in fields:
        if address >= length:
            continue
        try:
            if not t.check_entry(table, address):
                raise AssertionError(('Reference checker rejected generated prefix', address))
        except t.Pending:
            pass
    stop['raw_columns'] = 3 * length + sum(entries.values()) + 1
    stop['nonzero_fields'] = sum(bool(v) for v in entries.values())
    stop['max_scoped_formula'] = max(field[3] for address, field in fields.items()
                                     if address < length and len(field) > 3)
    stop['first_relaxed_comprehensions'] = relaxed_comprehensions[:10]
    stop['first_nonzero'] = [(i, v) for i, v in sorted(entries.items()) if v and i < 100]
    return stop, table


if __name__ == '__main__':
    import argparse
    import json
    import time
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sparse', action='store_true', help='Print the exact actual-value table as sparse JSON')
    args = parser.parse_args()
    started = time.perf_counter()
    result, table = locate()
    if args.sparse:
        artifact = {'format': 'CTN actual table values; omitted addresses are zero',
                    'ordinal': 'omega^omega', 'table_length': len(table),
                    'cap': True, 'raw_columns': result['raw_columns'],
                    'nonzero_values': [[i, v] for i, v in sorted(table.entries.items()) if v]}
        print(json.dumps(artifact, ensure_ascii=False, indent=2))
    else:
        result['seconds'] = round(time.perf_counter() - started, 3)
        print(json.dumps(result, ensure_ascii=False))
