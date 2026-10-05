"""Bounded public-domain checks; not an ordinal or normalization proof."""
import unittest

import standard as d


class StandardFrontendTests(unittest.TestCase):
    def test_small_paths(self):
        self.assertEqual(d.counts(d.from_path("TOP[1]")), (1, 2))
        omega = d.from_path("TOP[1][1]")
        self.assertEqual(d.counts(omega), (1,) * 17 + (2,))
        self.assertTrue(d.is_limit(omega))
        self.assertFalse(d.is_limit(d.from_path("TOP[1][0]")))
        self.assertFalse(d.is_limit(()))

    def test_prefixes_and_decrease(self):
        for path in ("TOP", "TOP[1]", "TOP[2]", "TOP[1][1]"):
            parent = d.from_path(path)
            previous = ()
            for index in range(6):
                child = d.expand(parent, index)
                self.assertEqual(child[:len(previous)], previous)
                self.assertEqual(d.compare(child, parent), -1)
                previous = child
            self.assertEqual(d.expand(parent, 0), parent[:-1])

    def test_raw_loop_rejected(self):
        loop = (("v", 0), ("a", 0, 0), ("l", 1), ("a", 2, 2), ("run", 3))
        for operation in (lambda: d.counts(loop), lambda: d.expand(loop, 1),
                          lambda: d.compare(loop, d.TOP), lambda: d.is_limit(loop)):
            with self.assertRaises(ValueError):
                operation()

    def test_input_and_budget_failures(self):
        for bad in ("TOP[-1]", "TOP[1.0]", "1,2", "TOP[1];print(1)"):
            with self.assertRaises(ValueError):
                d.from_path(bad)
        with self.assertRaises(d.ResourceLimit):
            d.from_path("TOP[1][54]", d.Budget(operations=2))
        with self.assertRaises(ValueError):
            d.expand(d.TOP, -1)
