import time
import unittest

import lcdn


class LCDNTests(unittest.TestCase):
    def test_beta_capture_avoidance(self):
        t = lcdn.Terms(lcdn.Budget())
        x, y = t.make("v", 0), t.make("v", 1)
        # (lambda. lambda. 1) 0 -> lambda. 1, not lambda. 0.
        root = t.make("a", t.make("l", t.make("l", y)), x)
        self.assertEqual(t.context_step(root, 0, 0), t.make("l", y))

    def test_under_lambda_and_shared_choice(self):
        t = lcdn.Terms(lcdn.Budget())
        q = t.make("q")
        root = t.make("l", t.make("a", q, q))
        # Under lambda, then right argument: heap address 4.
        expected = t.make("l", t.make("a", q, t.numeral(3)))
        self.assertEqual(t.context_step(root, 4, 3), expected)
        self.assertEqual(t.data[q], ("q",))
        self.assertIsNone(t.context_step(root, 2, 0))

    def test_two_column_omega(self):
        for n in range(41):
            self.assertEqual(lcdn.counts(lcdn.expand(lcdn.OMEGA, n)),
                             (1,) * (2 * n + 1))

    def test_occurrence_selection_does_not_unfold_sharing(self):
        t = lcdn.Terms(lcdn.Budget())
        q = t.make("q")
        root = q
        for _ in range(100):
            root = t.make("a", root, root)
        self.assertEqual(t.redex_count(root), 2 ** 100)
        # Select a large occurrence through the diagonal pair enumeration.
        # An odd (right-child) occurrence avoids creating an extra beta redex
        # in its parent when Q is replaced by the lambda numeral zero.
        occurrence = 2 ** 90 + 1
        index = occurrence * (occurrence + 1) // 2
        result = t.computation_child(root, index)
        self.assertEqual(t.redex_count(result), 2 ** 100 - 1)
        self.assertLess(len(t.data), 250)

    def test_twelve_column_compatible_seed(self):
        t = lcdn.Terms(lcdn.Budget())
        source = lcdn.tower_seed(t)
        seed = lcdn.append_program(lcdn.OMEGA, t, source)
        self.assertEqual(len(seed), 12)
        self.assertEqual(seed[:2], lcdn.OMEGA)
        previous = ()
        for n in range(31):
            child = lcdn.expand(seed, n)
            self.assertEqual(child[:len(previous)], previous)
            self.assertGreaterEqual(len(child), len(seed) - 1 + 2 * n)
            self.assertLess(lcdn.counts(child), lcdn.counts(seed))
            previous = child

    def test_bounded_standard_domain(self):
        t = lcdn.Terms(lcdn.Budget())
        root = lcdn.tower_seed(t)
        seed = lcdn.append_program(lcdn.OMEGA, t, root)
        seen = {}
        frontier = {seed}
        started = time.monotonic()
        for _ in range(7):
            following = set()
            for state in sorted(frontier, key=repr):
                self.assertLess(time.monotonic() - started, 8.0)
                word = lcdn.counts(state)
                self.assertEqual(seen.setdefault(word, state), state)
                outputs = [lcdn.expand(state, n) for n in range(5)]
                self.assertEqual(outputs[0], state[:-1])
                for a, b in zip(outputs, outputs[1:]):
                    self.assertEqual(a, b[:len(a)])
                if state:
                    self.assertTrue(all(lcdn.counts(x) < word for x in outputs))
                following.update(x for x in outputs if len(x) < 100)
            frontier = set(sorted(following, key=repr)[:300])
        self.assertGreater(len(seen), 50)

    def test_budget_and_bad_activity(self):
        with self.assertRaises(lcdn.ResourceLimit):
            lcdn.expand(lcdn.OMEGA, 100, lcdn.Budget(columns=10))
        with self.assertRaises(ValueError):
            lcdn.expand((("v", 0), ("run", 0)), 1)


if __name__ == "__main__":
    unittest.main()
