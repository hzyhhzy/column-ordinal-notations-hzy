"""Bounded independent checks of the tree-collapse translation.

The reference is the finite syntax in Proofs as Programs, section 2. A successful
test is not a proof of an ordinal calibration or of a TOP-prefix upper bound.
"""

import unittest

import buchholz_tree_macros as b
import dqdn
import ordinal_tree_macros as m
from test_ordinal_tree_macros import query_trace


ZERO, ONE = (), ("one",)


def D(level, term=ZERO):
    return ((level, term),)


class Reference:
    def __init__(self, calls=10000, convention="schwichtenberg"):
        self.calls = calls
        self.convention = convention

    def tick(self):
        self.calls -= 1
        if self.calls < 0:
            raise AssertionError("reference recursion bound exceeded")

    def typ(self, term):
        self.tick()
        if not term:
            return -2  # zero
        final = term[-1]
        if final == "one":
            return -1  # successor
        sigma, child = final
        if not child:
            if self.convention in ("arai", "buchholz") and sigma == 0:
                return -1
            return sigma  # regular Omega_sigma
        child_type = self.typ(child)
        return max(0, child_type) if child_type <= sigma else 0

    def child(self, term, index):
        self.tick()
        if not term:
            raise ValueError("zero has no child")
        prefix, final = term[:-1], term[-1]
        if final == "one":
            return prefix
        sigma, argument = final
        if not argument:
            if self.convention in ("arai", "buchholz") and sigma == 0:
                result = ZERO
            else:
                result = ONE * index if sigma == 0 else index
        else:
            typ = self.typ(argument)
            if typ == -1:
                result = D(sigma, self.child(argument, 0)) * (index + 1)
            elif typ <= sigma:
                result = D(sigma, self.child(argument, index))
            else:
                if not isinstance(index, int) or not 0 <= index <= 5:
                    raise AssertionError("reference answer bound exceeded")
                previous = (ONE if self.convention in ("arai", "buchholz")
                            else D(typ - 1))
                iterations = 1 if self.convention == "buchholz" else index
                for _ in range(iterations):
                    previous = D(typ - 1, self.child(argument, previous))
                result = D(sigma, self.child(argument, previous))
        if len(prefix) + len(result) > 1000:
            raise AssertionError("reference width bound exceeded")
        return prefix + result

    def trace(self, term, answers, max_queries=32):
        count = 0
        while term:
            if count >= max_queries:
                raise AssertionError("reference query bound exceeded")
            answer = answers[count] if count < len(answers) else 0
            # A successor is interpreted by a query with identical children.
            term = self.child(term, answer if self.typ(term) == 0 else 0)
            count += 1
        return count


def macro_reference_pair(height, convention="schwichtenberg"):
    source = m.var(b.name("zero", 2))
    reference = ZERO
    for _ in range(height):
        source = m.app(m.var(b.name("D", 2, 1)), source)
        reference = D(1, reference)
    return b.program(m.app(m.var(b.name("D", 2, 0)), source), 2, convention), D(0, reference)


class BuchholzMacroTests(unittest.TestCase):
    def test_base_class_is_existing_church_type(self):
        self.assertEqual(b.tree_type(1), m.O)

    def test_collapsed_regular_and_towers_match_reference(self):
        answers_list = ([], [1], [2], [0, 1], [1, 1], [2, 0, 1])
        for height in range(4):
            source, reference = macro_reference_pair(height)
            for answers in answers_list:
                with self.subTest(height=height, answers=answers):
                    expected = Reference().trace(reference, answers)
                    actual, normal, _ = query_trace(source, answers)
                    self.assertEqual(actual, expected)
                    self.assertEqual(normal, ("n", 0))

    def test_successor_uses_n_plus_one_copies(self):
        source = b.program(m.app(m.var(b.name("D", 2, 0)),
            m.app(m.var(b.name("succ", 2)), m.var(b.name("zero", 2)))), 2)
        for answer in range(5):
            count, normal, _ = query_trace(source, [answer])
            self.assertEqual(count, answer + 2)
            self.assertEqual(normal, ("n", 0))

    def test_cofinal_candidate_outer_branch(self):
        source = b.program(b.cofinal_candidate(2), 2)
        for height in range(4):
            _, reference = macro_reference_pair(height)
            count, normal, _ = query_trace(source, [height])
            self.assertEqual(count, 1 + Reference().trace(reference, []))
            self.assertEqual(normal, ("n", 0))

    def test_actual_generator_fields(self):
        result = m.inspect("T2 cofinal candidate", record=True,
                           source=b.program(b.cofinal_candidate(2), 2))
        self.assertTrue(result["fields_replayed"])
        self.assertEqual(result["fuel"], 2197)
        self.assertFalse(result["standard_position_claimed"])

    def test_arai_convention_against_independent_syntax(self):
        for height in range(4):
            source, reference = macro_reference_pair(height, "arai")
            answers_list = ([], [1], [2], [0, 1], [1, 1])
            if height < 3:
                answers_list += ([2, 0, 1],)
            for answers in answers_list:
                with self.subTest(height=height, answers=answers):
                    expected = Reference(convention="arai").trace(reference, answers)
                    actual, normal, _ = query_trace(source, answers)
                    self.assertEqual(actual, expected)
                    self.assertEqual(normal, ("n", 0))

    def test_expensive_branch_hits_resource_guard(self):
        # This case exceeded the 40,000-node guard during the initial audit.
        # Retain that fact instead of quietly raising all evaluation limits.
        source, _ = macro_reference_pair(3, "arai")
        with self.assertRaises(dqdn.ResourceLimit):
            query_trace(source, [2, 0, 1])

    def test_original_buchholz_against_independent_syntax(self):
        # Height 3 already hits our bounded audit limits, even on the zero
        # branch. Check that fact separately; do not mistake it for a mismatch.
        for height in range(3):
            source, reference = macro_reference_pair(height, "buchholz")
            for answers in ([], [1], [2], [0, 1], [1, 1]):
                with self.subTest(height=height, answers=answers):
                    expected = Reference(convention="buchholz").trace(reference, answers)
                    actual, normal, _ = query_trace(source, answers)
                    self.assertEqual(actual, expected)
                    self.assertEqual(normal, ("n", 0))

    def test_original_high_arity_clause_is_constant(self):
        reference = D(0, D(1))
        children = [Reference(convention="buchholz").child(reference, n)
                    for n in range(6)]
        self.assertTrue(all(child == children[0] for child in children))
        self.assertEqual(children[0], D(0, D(0, ONE)))

    def test_original_height_three_resource_guards(self):
        source, reference = macro_reference_pair(3, "buchholz")
        with self.assertRaises(dqdn.ResourceLimit):
            query_trace(source, [])
        with self.assertRaisesRegex(AssertionError, "reference query bound"):
            Reference(convention="buchholz").trace(reference, [0, 1])

    def test_original_cofinal_source_fields(self):
        result = m.inspect("original Buchholz ID1 source", record=True,
            source=b.program(b.cofinal_candidate(2), 2, "buchholz"))
        self.assertTrue(result["fields_replayed"])
        self.assertEqual(result["fuel"], 2182)
        self.assertEqual(result["independent_columns"], 173)
        self.assertFalse(result["standard_position_claimed"])

    def test_compact_two_level_collapse(self):
        for height in range(3):
            term = m.var(b.name("zero", 2))
            reference = ZERO
            for _ in range(height):
                term = m.app(m.var(b.name("D", 2, 1)), term)
                reference = D(1, reference)
            source = b.compact_bho_program(m.app(m.var(b.name("D", 2, 0)), term))
            for answers in ([], [1], [2], [1, 1]):
                with self.subTest(height=height, answers=answers):
                    count, normal, _ = query_trace(source, answers)
                    self.assertEqual(count, Reference(convention="buchholz").trace(
                        D(0, reference), answers))
                    self.assertEqual(normal, ("n", 0))

    def test_compact_cofinal_fields(self):
        result = m.inspect("compact original BHO source", record=True,
                           source=b.compact_bho_program())
        self.assertTrue(result["fields_replayed"])
        self.assertEqual(result["fuel"], 1526)
        self.assertEqual(result["independent_columns"], 139)

    def test_single_use_inlining_preserves_query_tree_samples(self):
        for height in range(3):
            ordinal = m.var(b.name("zero", 2))
            for _ in range(height):
                ordinal = m.app(m.var(b.name("D", 2, 1)), ordinal)
            ordinal = m.app(m.var(b.name("D", 2, 0)), ordinal)
            original = b.compact_bho_program(ordinal)
            optimized = b.compact_bho_program(ordinal, inline_once=True)
            for answers in ([], [1], [2], [1, 1]):
                self.assertEqual(query_trace(original, answers)[:2],
                                 query_trace(optimized, answers)[:2])

    def test_inlined_bho_actual_fields(self):
        result = m.inspect("single-use-inlined BHO source", record=True,
                           source=b.compact_bho_program(inline_once=True))
        self.assertTrue(result["fields_replayed"])
        self.assertEqual(result["fuel"], 1344)
        self.assertEqual(result["warm_steps"], 12)
        self.assertEqual(result["independent_columns"], 139)


if __name__ == "__main__":
    unittest.main()
