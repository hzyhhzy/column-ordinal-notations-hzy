import unittest

import dqdn


class DemandTests(unittest.TestCase):
    def terms(self):
        return dqdn.Terms(dqdn.Budget(seconds=2.0))

    def test_does_not_reduce_unused_argument_or_lambda_body(self):
        t = self.terms()
        zero = t.numeral(0)
        query = t.make("q", zero)
        constant = t.make("l", zero)
        root = t.make("a", constant, query)
        self.assertEqual(t.computation_child(root, 100), zero)
        self.assertFalse(t.reducible(t.make("l", query)))

    def test_query_index_is_evaluated(self):
        t = self.terms()
        query = t.make("q", t.make("s", t.numeral(3)))
        first = t.computation_child(query, 2)
        self.assertEqual(t.data[first], ("q", t.numeral(4)))
        second = t.computation_child(first, 2)
        self.assertEqual(t.data[second], ("n", 1))

    def test_recursor_evaluates_only_index_first(self):
        t = self.terms()
        q = t.make("q", t.numeral(0))
        root = t.make("r", q, q, t.make("s", t.numeral(0)))
        next_root = t.computation_child(root, 0)
        self.assertEqual(t.data[next_root], ("r", q, q, t.numeral(1)))

    def test_first_query_and_fixed_answers(self):
        t = self.terms()
        root = dqdn.epsilon_seed(t)
        selected, _ = t.demand(root)
        self.assertEqual(t.data[selected][0], "q")
        for answer in range(6):
            # last item in triangular row answer has fair_index = answer.
            current = t.computation_child(root, answer * (answer + 3) // 2)
            for _ in range(200):
                d = t.demand(current)
                if d is None or t.data[d[0]][0] == "q":
                    break
                current = t.computation_child(current, 0)
            else:
                self.fail("administrative prefix exceeded bounded test allowance")
            if answer == 0:
                self.assertEqual(t.data[current], ("n", 0))
            else:
                self.assertEqual(t.data[t.demand(current)[0]][0], "q")

    def test_omega_and_prefix(self):
        for n in range(20):
            self.assertEqual(dqdn.counts(dqdn.expand(dqdn.OMEGA, n)),
                             (1,) * (2 * n + 2))
        t = self.terms()
        root = dqdn.epsilon_seed(t)
        columns = dqdn.append_program(dqdn.OMEGA, t, root)
        previous = ()
        for n in range(31):
            child = dqdn.expand(columns, n)
            self.assertEqual(child[:len(previous)], previous)
            self.assertLess(dqdn.counts(child), dqdn.counts(columns))
            previous = child


if __name__ == "__main__":
    unittest.main()
