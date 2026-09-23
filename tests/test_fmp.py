"""Fast, dependency-free tests for the delivered kernel and count helpers.

Run from the repository root: python -B tests/test_fmp.py
Finite regression tests, not a well-foundedness proof.
"""
import random
import time
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations/FMP'))

from fmp import Column, Pattern, copy_tail, seed, trace
from fmp_tools import compare, counts, display, parse, validate


class ScaleLimit(Exception):
    pass


class FMPTests(unittest.TestCase):
    def test_zero_successors_and_omega(self):
        self.assertEqual(Pattern()[3], Pattern())
        omega = parse('[][1]')
        for n in range(15):
            finite = omega[n]
            self.assertEqual(finite, Pattern((Column(),) * (n + 1)))
            self.assertEqual(finite[0], finite[7])
            self.assertEqual(counts(finite), (1,) * (n + 1))

    def test_seed_formula(self):
        for n in range(21):
            a, b = seed(n), seed(n + 1)
            self.assertEqual(a.columns, b.columns[:len(a.columns)])
            self.assertEqual(counts(a), tuple((r + 1) ** 2 // 4
                                             for r in range(1, len(a.columns) + 1)))
            validate(a)

    def test_binary_blocks(self):
        carrier = seed(1)[0][1]
        self.assertEqual(display(carrier), '[][1][2]')
        previous = Pattern()
        for n in range(9):
            a = carrier[n]
            self.assertEqual(len(a.columns), 2 ** (n + 1))
            self.assertEqual(a.columns[:len(previous.columns)], previous.columns)
            self.assertEqual(counts(a), tuple(1 << i.bit_count() for i in range(len(a.columns))))
            self.assertEqual(parse(display(a)), a)
            self.assertEqual(parse(display(a, full=True)), a)
            validate(a)
            previous = a

    def test_stars_have_real_effect(self):
        a = seed(1)[1][0][2][0][0][0]
        self.assertEqual(display(a), '[][1][1:2;2][1:2;2][1:2,2:4*;3][1:2;2]')
        self.assertEqual(counts(a), (1, 2, 4, 4, 3, 4))
        stripped = Pattern(tuple(Column(c.edges) for c in a.columns))
        with_stars, without_stars = a[1], stripped[1]
        self.assertEqual(len(with_stars.columns), 21)
        self.assertEqual(len(without_stars.columns), 21)
        self.assertEqual(counts(with_stars)[17:], (3, 3, 3, 3))
        self.assertEqual(counts(without_stars)[17:], (2, 2, 2, 2))
        self.assertNotEqual(with_stars.columns[17].edges, without_stars.columns[17].edges)

    def test_projection_forgets_only_a_map(self):
        a = seed(1)[1][0][1][1][0]
        self.assertEqual(display(a), '[][1][1:2;2][1:2;2][2:4;4]')
        raw = copy_tail(a)
        self.assertEqual(raw.columns[4], Column())
        self.assertTrue(raw.columns[-1].edges, 'the actual self-copy is retained until cut')
        validate(a[2])

    def test_mixed_star_really_splices_an_old_trace(self):
        carrier = seed(1)[0][1]
        a = carrier[2][0][1]
        self.assertEqual(len(a.columns), 10)
        self.assertEqual(trace(a.columns, 5, 1), (5,))
        self.assertIn(9, a.columns[-1].stars)
        self.assertEqual(trace(a.columns, 9, 5), (9,))
        raw = copy_tail(a)
        # The first copied source is old column 6.  Its star 1->5 is
        # transported to 1->9 by splicing the controller's 9->5 trace.
        self.assertIn(9, raw.columns[9].stars)
        self.assertIn((1, 9), raw.columns[9].edges)
        self.assertEqual(trace(raw.columns, 9, 1), (9, 5))

    def test_context_specific_counts(self):
        self.assertEqual(counts(parse('[][1][2]'))[-1], 3)
        self.assertEqual(counts(parse('[][][2]'))[-1], 2)

    def test_eight_column_examples_are_standard(self):
        # Reach the eight-column example by actual FS and cut steps, not
        # by treating a syntactically valid handwritten table as standard.
        a = seed(1)[0][1][2]
        self.assertEqual(counts(a), (1, 2, 2, 4, 2, 4, 4, 8))
        snapshots = {8: a}
        for value in (7, 6, 5, 4):
            a = a[1]
            self.assertLess(len(a.columns), 200)
            while len(a.columns) > 8:
                a = a[0]
            self.assertEqual(counts(a)[-1], value)
            snapshots[value] = a
        h = parse('[][1][1][1:3*;2][1][1:5*;2][1:5*,2:6*;3][1:5*,2:6*;3]')
        self.assertEqual(a, h)
        self.assertEqual(snapshots[5][1], h)
        self.assertEqual(counts(h[0]), (1, 2, 2, 4, 2, 4, 4))

    def test_complete_port_band_formula(self):
        h = parse('[][1][1][1:3*;2][1][1:5*;2][1:5*,2:6*;3][1:5*,2:6*;3]')
        expected = list(h.columns[:-1])

        def port(q, source, head):
            return Column(tuple((source + i, head + i) for i in range(q + 2)),
                          frozenset(range(head, head + q)))

        self.assertEqual(h[0], Pattern(tuple(expected)))
        for m in range(1, 13):
            g, u = m + 2, m * m + 3 * m + 1
            expected.extend(port(q, u, u + g) for q in range(g))
            expected.extend(port(q, u, u + 2 * g) for q in range(g + 1))
            actual = h[m]
            self.assertEqual(len(actual.columns), m * m + 6 * m + 7)
            self.assertEqual(actual, Pattern(tuple(expected)))
            validate(actual)

    def test_rehanging_a_column(self):
        a = seed(7)[1][0]
        values = counts(a)
        head = len(a.columns) + 1
        for i, c in enumerate(a.columns):
            if not c.edges:
                continue
            rehung = Column(c.edges[:-2] + ((c.pivot, head), (c.pivot + 1, head + 1)), c.stars)
            extended = Pattern(a.columns + (rehung,))
            validate(extended)
            self.assertEqual(counts(extended)[-1], values[i])

    def test_bounded_standard_paths(self):
        start = time.monotonic()
        rng = random.Random(2026092211)
        a = seed(2)
        completed = 0

        def guard(size=0):
            if size > 180:
                raise ScaleLimit()
            if time.monotonic() - start > 5:
                raise TimeoutError()

        for _ in range(500):
            if not a.columns:
                a = seed(rng.randrange(6))
            n = rng.randrange(4)
            try:
                b = a.expand(n, guard)
                self.assertEqual(b.columns[:max(0, len(a.columns) - 1)], a.columns[:-1])
                if n:
                    c = a.expand(n - 1, guard)
                    self.assertEqual(c.columns, b.columns[:len(c.columns)])
                validate(b)
                self.assertEqual(compare(b, a), -1)
                self.assertLess(counts(b), counts(a))
                a = b
                completed += 1
            except ScaleLimit:
                a = seed(rng.randrange(6))
            except TimeoutError:
                break
        self.assertGreater(completed, 25)


if __name__ == '__main__':
    unittest.main(verbosity=2)
