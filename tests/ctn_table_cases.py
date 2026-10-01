"""Bounded, reproducible checks; these do not numerically test CK strength."""

from itertools import product
from time import perf_counter
import json
import unittest

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'CTN'))

import ctn_table as c


class SparseTable:
    """Test a clause without allocating its large Godel addresses."""

    def __init__(self, entries):
        self.entries = entries

    def __len__(self):
        return (1 << 63) - 1

    def __getitem__(self, index):
        if index not in self.entries:
            raise AssertionError(f"Unexpected clause dependency: {index}")
        return self.entries[index]


def checked(entries, address):
    return c.check_entry(SparseTable(entries), address)


def shallow_table(size):
    """A legal finite table, not a claimed prefix of an infinite model.

    Visible truth formulas are quantifier-free at these small address bounds.
    Comprehension rows are placed beyond the written membership region.
    """
    def evaluate(code, numbers, sets):
        op, data = c.unpair(code)
        if op == c.ZERO:
            return int(numbers[data] == 0)
        if op in (c.EQUAL, c.SUCC, c.MEMBER):
            i, j = c.unpair(data)
            if op == c.MEMBER:
                return 0
            return int(numbers[i] + int(op == c.SUCC) == numbers[j])
        if op in (c.ADD, c.MUL):
            i, rest = c.unpair(data)
            j, k = c.unpair(rest)
            result = numbers[i] + numbers[j] if op == c.ADD else numbers[i] * numbers[j]
            return int(result == numbers[k])
        if op == c.NOT:
            return 1 - evaluate(data, numbers, sets)
        if op == c.AND:
            left, right = c.unpair(data)
            return evaluate(left, numbers, sets) & evaluate(right, numbers, sets)
        raise AssertionError("Benchmark address bound is no longer quantifier-free")

    values = [0] * size
    for index in range(size):
        kind, payload = c.unpair(index)
        if kind not in (c.TRUTH, c.COMPREHENSION):
            continue
        code, env = c.unpair(payload)
        ns, ss = c.unpair(env)
        numbers, sets = c.decode_list(ns), c.decode_list(ss)
        extra = int(kind == c.COMPREHENSION)
        if c.scoped(code, len(numbers) + extra, len(sets)):
            values[index] = size if extra else evaluate(code, numbers, sets)
    return values


class TableTests(unittest.TestCase):
    def test_pairing_and_lists(self):
        for a in range(100):
            for b in range(100):
                self.assertEqual(c.unpair(c.pair(a, b)), (a, b))
        for values in [(), (0,), (1, 2, 3), (0, 0, 0, 0), (200, 1)]:
            self.assertEqual(c.decode_list(c.encode_list(values)), values)

    def test_atomic_arithmetic_and_scope(self):
        examples = [
            (c.formula(c.ZERO, 0), (0,), (), 1),
            (c.formula(c.ZERO, 0), (3,), (), 0),
            (c.formula(c.EQUAL, 0, 1), (7, 7), (), 1),
            (c.formula(c.SUCC, 0, 1), (7, 8), (), 1),
            (c.formula(c.ADD, 0, 1, 2), (2, 3, 5), (), 1),
            (c.formula(c.MUL, 0, 1, 2), (2, 3, 7), (), 0),
        ]
        for code, numbers, sets, value in examples:
            address = c.pair(c.TRUTH, c.context(code, numbers, sets))
            self.assertTrue(checked({address: value}, address))
            self.assertFalse(checked({address: 1 - value}, address))
        self.assertFalse(c.scoped(c.formula(c.MEMBER, 0, 0), 1, 0))
        self.assertTrue(c.scoped(c.formula(c.MEMBER, 0, 0), 1, 1))

    def test_boolean_rules(self):
        zero = c.formula(c.ZERO, 0)
        ns = c.encode_list((0,))
        child = c.truth_address(zero, ns, 0)
        neg = c.truth_address(c.formula(c.NOT, zero), ns, 0)
        conjunction = c.truth_address(c.formula(c.AND, zero, zero), ns, 0)
        self.assertTrue(checked({child: 1, neg: 0}, neg))
        self.assertFalse(checked({child: 1, neg: 1}, neg))
        self.assertTrue(checked({child: 1, conjunction: 1}, conjunction))

    def test_existential_witness_and_negative_instances(self):
        zero = c.formula(c.ZERO, 0)
        ex = c.formula(c.EXISTS_N, zero)
        payload = c.context(ex)
        truth = c.pair(c.TRUTH, payload)
        witness = c.pair(c.WITNESS, payload)
        zero_instance = c.pair(c.TRUTH, c.context(zero, (0,)))
        self.assertTrue(checked({truth: 1, witness: 0, zero_instance: 1}, truth))
        self.assertFalse(checked({truth: 1, witness: 0, zero_instance: 0}, truth))
        negative = c.pair(c.FORALL_TEST, c.pair(payload, 0))
        self.assertFalse(checked({negative: 0, truth: 0, zero_instance: 1}, negative))
        self.assertTrue(checked({negative: 0, truth: 0, zero_instance: 0}, negative))

    def test_set_quantifier_and_membership(self):
        body = c.formula(c.MEMBER, 0, 0)
        ex = c.formula(c.EXISTS_S, body)
        payload = c.context(ex, (4,))
        truth = c.pair(c.TRUTH, payload)
        witness = c.pair(c.WITNESS, payload)
        instance = c.pair(c.TRUTH, c.context(body, (4,), (2,)))
        self.assertTrue(checked({truth: 1, witness: 2, instance: 1}, truth))
        member = c.membership_address(2, 4)
        self.assertTrue(checked({instance: 1, member: 1}, instance))
        self.assertFalse(checked({instance: 1, member: 0}, instance))

    def test_comprehension(self):
        zero = c.formula(c.ZERO, 0)
        payload = c.context(zero)
        test = c.pair(c.COMP_TEST, c.pair(payload, 0))
        choice = c.pair(c.COMPREHENSION, payload)
        member = c.membership_address(3, 0)
        truth = c.pair(c.TRUTH, c.context(zero, (0,)))
        entries = {test: 0, choice: 3, member: 1, truth: 1}
        self.assertTrue(checked(entries, test))
        entries[member] = 0
        self.assertFalse(checked(entries, test))

    def test_finite_table_tree_is_prefix_closed(self):
        for length in range(9):
            for values in product(range(2), repeat=length):
                if c.table_ok(values):
                    for k in range(length + 1):
                        self.assertTrue(c.table_ok(values[:k]))
        self.assertFalse(c.table_ok([0] * 9))  # T(x=0, x:=0) must be 1.
        self.assertFalse(c.table_ok([2]))      # Membership entries are bits.



if __name__ == "__main__":
    unittest.main(verbosity=2)
