"""Finite cross-checks for the paper proof; never materialize the giant word."""

import json
from pathlib import Path
import unittest

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'CTN'))

import ctn_table as t
from ctn_sparse import SparseTable, metadata
from locate_omega_omega import (
    ALL, EMPTY, Rows, Shape, comprehension_shape, locate, roots,
)


def direct_truth(code, numbers, sets, interpretations):
    """Independent bounded semantic evaluator for the audited formula range."""
    op, body = t.unpair(code)
    if op == t.ZERO:
        return numbers[body] == 0
    if op in (t.EQUAL, t.SUCC, t.MEMBER):
        i, j = t.unpair(body)
        if op == t.MEMBER:
            return interpretations[sets[j]].contains(numbers[i])
        return numbers[i] + int(op == t.SUCC) == numbers[j]
    if op in (t.ADD, t.MUL):
        i, rest = t.unpair(body)
        j, k = t.unpair(rest)
        result = numbers[i] + numbers[j] if op == t.ADD else numbers[i] * numbers[j]
        return result == numbers[k]
    if op == t.NOT:
        return not direct_truth(body, numbers, sets, interpretations)
    if op == t.AND:
        a, b = t.unpair(body)
        return direct_truth(a, numbers, sets, interpretations) and direct_truth(b, numbers, sets, interpretations)
    if op == t.EXISTS_N:
        # In this test fragment true witnesses are 0 or one of the supplied
        # parameters (all <= 8). This is not a general existential evaluator.
        return any(direct_truth(body, (w,) + numbers, sets, interpretations) for w in range(10))
    if op == t.EXISTS_S:
        # All audited set-quantifier bodies ignore their bound set variable.
        return direct_truth(body, numbers, (0,) + sets, interpretations)
    raise AssertionError(code)


class OmegaOmegaChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result, cls.table = locate()
        cls.fields = metadata(len(cls.table) + 1)

    def test_exact_sparse_artifact_and_lengths(self):
        artifact = json.loads((Path(__file__).resolve().parents[1] / 'notations/CTN/fixtures/omega-omega.sparse.json').read_text(encoding='utf-8'))
        nonzero = [[i, v] for i, v in sorted(self.table.entries.items()) if v]
        self.assertEqual(artifact['nonzero_values'], nonzero)
        self.assertEqual(artifact['table_length'], 23_191_452)
        self.assertEqual(artifact['raw_columns'], 69_593_927)
        self.assertEqual(len(nonzero), 4352)
        self.assertEqual(3 * len(self.table) + sum(self.table.entries.values()) + 1, artifact['raw_columns'])

    def test_exact_formula_fragment(self):
        formulas = {f[3] for i, f in self.fields.items() if i < len(self.table) and len(f) > 3}
        self.assertEqual(max(formulas), 113)
        self.assertEqual(sorted(c for c in formulas if t.unpair(c)[0] == t.EXISTS_N), [36, 46, 57, 69, 82, 96, 111])
        self.assertEqual(sorted(c for c in formulas if t.unpair(c)[0] == t.EXISTS_S), [45, 56, 68, 81, 95, 110])

    def test_three_decisive_addresses(self):
        body = t.formula(t.EQUAL, 1, 0)
        formula = t.formula(t.EXISTS_S, body)
        ca = t.pair(t.COMPREHENSION, t.context(formula, (1,)))
        va = t.pair(t.TRUTH, t.context(formula, (0, 1)))
        wa = t.pair(t.WITNESS, t.context(formula, (0, 1)))
        self.assertEqual((body, formula), (4, 95))
        self.assertEqual((ca, va, wa), (11_802_507, 23_184_643, 23_191_452))
        self.assertEqual((self.table[ca], self.table[va]), (3, 1))
        self.assertEqual(wa, len(self.table))

    def test_failure_addresses_and_first_legal_children(self):
        expected = [175526, 445094, 2158001, 14329979, 103140701, 709608626, 4414099859]
        va = 23_184_643
        for witness, expected_address in enumerate(expected):
            address = t.truth_address(4, t.encode_list((0, 1)), t.cons(witness, 0))
            self.assertEqual(address, expected_address)
            values = dict(self.table.entries)
            values[len(self.table)] = witness
            child = SparseTable(len(self.table) + 1, values)
            if witness < 4:
                self.assertFalse(t.check_entry(child, va))
            else:
                with self.assertRaises(t.Pending):
                    t.check_entry(child, va)
                for index in self.fields:
                    try:
                        self.assertTrue(t.check_entry(child, index), index)
                    except t.Pending:
                        pass

    def test_original_checker_on_all_relevant_fields(self):
        for index in self.fields:
            if index >= len(self.table):
                continue
            try:
                self.assertTrue(t.check_entry(self.table, index), index)
            except t.Pending:
                pass
        for length in (0, 10, 32, 100, 1000, 10000):
            self.assertTrue(t.table_ok([self.table[i] for i in range(length)]))

    def test_shape_arithmetic_against_independent_formula_evaluation(self):
        interpretations = {0: Shape(False, frozenset([0, 3])),
                           1: Shape(True, frozenset([1, 2]))}
        rows = Rows()
        for row, shape in interpretations.items():
            rows.assign(row, shape)
        for parameters in ((0, 1, 2, 3), (2, 0, 1, 3), (3, 3, 3, 3)):
            for code in range(114):
                if not t.scoped(code, len(parameters) + 1, 2):
                    continue
                shape = comprehension_shape(code, parameters, (0, 1), rows)
                for x in range(9):
                    actual = rows.bit(shape[1], x) if isinstance(shape, tuple) else shape.contains(x)
                    self.assertEqual(bool(actual), direct_truth(code, (x,) + parameters, (0, 1), interpretations),
                                     (code, parameters, x))

    def test_polynomial_roots_and_row_lower_bounds(self):
        for a in range(-2, 3):
            for b in range(-3, 4):
                for c in range(-3, 4):
                    shape = roots((c, b, a))
                    for x in range(12):
                        self.assertEqual(shape.contains(x), a * x * x + b * x + c == 0)
        rows = Rows()
        rows.assign(0, EMPTY)
        rows.assign(1, ALL)
        singleton = Shape(False, frozenset([1]))
        self.assertFalse(rows.accepts(0, singleton, lower=True))
        self.assertTrue(rows.accepts(1, singleton, lower=True))
        rows.assign(2, singleton, lower=True)
        self.assertEqual(rows.bit(2, 1), 1)
        self.assertFalse(rows.compatible(0, 2))
        self.assertTrue(rows.compatible(1, 2))


if __name__ == '__main__':
    unittest.main()
