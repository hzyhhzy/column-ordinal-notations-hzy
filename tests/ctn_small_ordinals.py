"""Bounded implementation checks for the explicit omega^2 and omega^3 proofs.

These checks do not infer ordinal equalities from sampled fundamental sequences.
The all-natural-number arguments are in notations/CTN/small-ordinals.zh-CN.md.
"""

import unittest

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'CTN'))

import ctn_table as table
import ctn


OMEGA2_TABLE = [0] * 8 + [1, 0]
OMEGA3_TABLE = [0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
OMEGA2 = "12112112112112112112112112211212"
OMEGA3 = "12112112112112112112221121122112211211211211211211211212"


def block_counts(word):
    """Number of following 2s plus one, splitting at each 1."""
    assert not word or word.startswith("1")
    return [len(run) + 1 for run in word.split("1")[1:]]


class SmallOrdinalChecks(unittest.TestCase):
    def test_encodings_and_legality(self):
        for values, expected, length in [
            (OMEGA2_TABLE, OMEGA2, 32),
            (OMEGA3_TABLE, OMEGA3, 56),
        ]:
            self.assertEqual(ctn.encode_table(values, cap=True), expected)
            self.assertEqual(len(expected), length)
            self.assertTrue(table.table_ok(values))
            self.assertTrue(ctn.is_standard(expected))

    def test_omega2_display_and_fundamental_sequences(self):
        self.assertEqual(block_counts(OMEGA2), [2, 1] * 8 + [3, 1, 2, 2])
        entry = OMEGA2[:-1]
        self.assertEqual(ctn.fundamental(OMEGA2, 0), entry)
        for n in range(1, 33):
            self.assertEqual(ctn.fundamental(OMEGA2, n), entry + "1" + "2" * (n - 1))

    def test_omega2_conflicting_addresses(self):
        zero = table.formula(table.ZERO, 0)
        context = table.context(zero)
        self.assertEqual(table.membership_address(0, 0), 0)
        self.assertEqual(table.pair(table.COMPREHENSION, context), 6)
        self.assertEqual(table.pair(table.TRUTH, table.context(zero, (0,))), 8)
        self.assertEqual(table.pair(table.COMP_TEST, table.pair(context, 0)), 10)
        for next_value in [0, 1, 2, 100, 10**50]:
            self.assertFalse(table.table_ok(OMEGA2_TABLE + [next_value]))

    def test_omega3_conflicting_addresses(self):
        equal = table.formula(table.EQUAL, 0, 0)
        context = table.context(equal)
        self.assertEqual(table.pair(table.COMPREHENSION, context), 11)
        self.assertEqual(table.pair(table.COMP_TEST, table.pair(context, 0)), 16)
        self.assertEqual(table.pair(table.TRUTH, table.context(equal, (0,))), 19)
        for choice in [0, 1, 2, 100, 10**50]:
            self.assertTrue(table.table_ok(OMEGA3_TABLE + [choice]))
            self.assertTrue(table.table_ok(OMEGA3_TABLE + [choice, 0]))
            self.assertFalse(table.table_ok(OMEGA3_TABLE + [choice, 1]))
            for last in [0, 1, 2, 100]:
                self.assertFalse(table.table_ok(OMEGA3_TABLE + [choice, 0, last]))

    def test_omega3_earlier_positive_children_have_bounded_failure(self):
        prefix = OMEGA3_TABLE[:6]
        for choice in (0, 1):
            for bit in (0, 1):
                leaf = prefix + [choice, 0, 1, bit]
                self.assertTrue(table.table_ok(leaf))
                for next_value in (0, 1, 2):
                    self.assertFalse(table.table_ok(leaf + [next_value]))
        leaf = OMEGA3_TABLE[:9] + [0]
        self.assertTrue(table.table_ok(leaf))
        for next_value in (0, 1, 2):
            self.assertFalse(table.table_ok(leaf + [next_value]))


if __name__ == "__main__":
    unittest.main()
