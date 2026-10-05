"""Bounded tests for the native-number kernel, not ordinal proof search."""

import unittest

import lqdn


class NativeTests(unittest.TestCase):
    def terms(self):
        return lqdn.Terms(lqdn.Budget(seconds=2.0))

    def test_numbers_are_not_pointers(self):
        t = self.terms()
        huge = t.numeral(2 ** 100)
        self.assertEqual(t.shift(huge, 20), huge)
        self.assertEqual(t.substitute(huge, t.numeral(1)), huge)
        self.assertEqual(t.redex_count(huge), 0)
        roots = lqdn.decode((("n", 2 ** 100),), t)
        self.assertEqual(roots, [huge])

    def test_primitive_recursor(self):
        t = self.terms()
        zero = t.numeral(0)
        v0 = t.make("v", 0)
        step = t.make("l", t.make("l", t.make("s", v0)))
        root = t.make("r", zero, step, t.numeral(10))
        for _ in range(100):
            if not t.reducible(root):
                break
            root = t.computation_child(root, 0)
        self.assertEqual(t.data[root], ("n", 10))

    def test_capture_avoidance_in_recursor(self):
        t = self.terms()
        v0, v1 = t.make("v", 0), t.make("v", 1)
        argument = t.numeral(123)
        body = t.make("l", t.make("r", v1, v0, v1))
        expected = t.make("l", t.make("r", argument, v0, argument))
        self.assertEqual(t.substitute(body, argument), expected)

    def test_q_and_prefix(self):
        for n in range(20):
            child = lqdn.expand(lqdn.OMEGA, n)
            self.assertEqual(lqdn.counts(child), (1,) * (2 * n + 1))
        t = self.terms()
        root = lqdn.tower_seed(t)
        columns = lqdn.append_program(lqdn.OMEGA, t, root)
        previous = ()
        for n in range(21):
            child = lqdn.expand(columns, n)
            self.assertEqual(child[:len(previous)], previous)
            self.assertLess(lqdn.counts(child), lqdn.counts(columns))
            previous = child

    def test_native_church_macro(self):
        t = self.terms()
        q = lqdn.church_choice(t)
        # Choose primitive Q=3 under the closed Church-iterator macro first.
        chosen = t.computation_child(q, 9)  # unpair(9)=(0,3).
        v0 = t.make("v", 0)
        successor = t.make("l", t.make("s", v0))
        root = t.make("a", t.make("a", chosen, successor), t.numeral(0))
        for _ in range(100):
            if not t.reducible(root):
                break
            root = t.computation_child(root, 0)
        self.assertEqual(t.data[root], ("n", 3))

    def test_three_child_occurrence_selection(self):
        t = self.terms()
        q = t.make("q")
        root = t.make("r", q, q, q)
        self.assertEqual(t.redex_count(root), 3)
        selected = t.computation_child(root, 3)  # unpair(3)=(2,0).
        self.assertEqual(t.data[selected], ("r", q, q, t.numeral(0)))


if __name__ == "__main__":
    unittest.main()
