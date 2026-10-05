"""Finite implementation checks only; no ordinal rank is inferred from tests."""

import unittest

import check_dqdn_seeds as check
import dqdn
import ordinal_tree_macros as m
import typed_builder as tb


def query_trace(source, answers, max_steps=10000, max_queries=64):
    terms = tb.Terms(dqdn.Budget(seconds=3, nodes=40000, operations=1500000))
    assert check.infer(source) == check.N
    current = check.erase(source, terms)
    consumed = 0
    for step in range(max_steps):
        selected = terms.demand(current)
        if selected is None:
            return consumed, terms.data[current], step
        if terms.data[selected[0]][0] == "q":
            if consumed >= max_queries:
                raise AssertionError("query bound exceeded")
            answer = answers[consumed] if consumed < len(answers) else 0
            current = terms.computation_child(current, 0 if answer == 0 else 2 * answer + 1)
            consumed += 1
        else:
            current = terms.computation_child(current, 0)
    raise AssertionError("step bound exceeded")


class OrdinalMacroTests(unittest.TestCase):
    def test_finite_successors(self):
        ordinal = m.var("zero")
        for n in range(8):
            source = m.program_for(ordinal)
            for answer in (0, 3):
                count, normal, _ = query_trace(source, [answer] * 8)
                self.assertEqual(count, n)
                self.assertEqual(normal, ("n", 0))
            ordinal = m.app(m.var("succO"), ordinal)

    def test_limit_reader_shares_one_numeric_answer(self):
        natural = m.iterate(m.var("succO"), m.var("zero"), m.var("n"), m.O)
        # n occurs twice: with a naive by-name f(Q0), two separate oracle
        # answers would be consumed. The strict reader must consume only one.
        ordinal = m.app(m.var("limO"), m.lam("n", m.N,
            m.app(m.var("addO"), natural, natural)))
        source = m.program_for(ordinal)
        for answer in range(6):
            count, normal, _ = query_trace(source, [answer])
            self.assertEqual(count, 1 + 2 * answer)
            self.assertEqual(normal, ("n", 0))

    def test_zero_branch_of_derivative_closure(self):
        for level in range(1, 5):
            count, normal, _ = query_trace(m.program(level), [0])
            self.assertEqual(count, 1)
            self.assertEqual(normal, ("n", 0))

    def test_first_nonzero_zeta_branch_reaches_epsilon_closure(self):
        # The outer zeta closure chooses one epsilon iteration. Its epsilon0
        # closure chooses zero iterations and returns ordinal zero.
        count, normal, _ = query_trace(m.program(2), [1, 0])
        self.assertEqual(count, 2)
        self.assertEqual(normal, ("n", 0))

    def test_gamma_first_two_branches(self):
        count, normal, _ = query_trace(m.gamma_program(), [0])
        self.assertEqual((count, normal), (1, ("n", 0)))
        # phi_0(0)=1, so one diagonal iteration adds a successor query.
        count, normal, _ = query_trace(m.gamma_program(), [1, 0])
        self.assertEqual((count, normal), (2, ("n", 0)))

    def test_typed_generator_replay(self):
        zeta = m.inspect(2, record=True)
        self.assertEqual(zeta["fuel"], 871)
        self.assertEqual(zeta["generator_fs_bound"], 1744)
        self.assertTrue(zeta["fields_replayed"])
        gamma = m.inspect("Gamma0", record=True, source=m.gamma_program())
        self.assertEqual(gamma["fuel"], 1093)
        self.assertEqual(gamma["generator_fs_bound"], 2188)
        self.assertTrue(gamma["fields_replayed"])


if __name__ == "__main__":
    unittest.main()
