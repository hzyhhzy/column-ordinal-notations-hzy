"""Small, ordinary System F iterator sources for the existing DQDN kernel.

These are authoring macros, not new notation rules. Type/field checks do not
prove ordinal ranks. See section 13 of the small-ordinal research document.
"""

import json
import unittest

import check_dqdn_seeds as s
import ordinal_tree_macros as m
from test_ordinal_tree_macros import query_trace


IDENTITY = s.LAM(s.N, s.V(0))

# C : CN becomes Lambda A. C[A -> A](C[A]). All type applications erase.
SELF_POWER_BODY = ("poly", s.APP(
    ("inst", s.V(0), s.arr(s.A, s.A)), ("inst", s.V(0), s.A)))
SELF_POWER = s.LAM(s.CN, SELF_POWER_BODY)
POWER_STEP = s.LAM(s.N, SELF_POWER)

# U(C) chooses a finite number of self-power iterations of C.
EPSILON_CLOSE = s.LAM(s.CN, ("rec", s.V(0), POWER_STEP, s.Q0))

# E(C) uses C itself as an iterator, with carrier CN.
# Its zeta lower bound requires the admissible-relation lifting argument;
# a calculation at the ground Nat type alone does not justify that bound.
EPSILON_INDEX = s.LAM(s.CN,
    s.APP(s.APP(("inst", s.V(0), s.CN), EPSILON_CLOSE), s.F))


def observe(iterator, observer=IDENTITY):
    return s.APP(s.APP(("inst", iterator, s.N), observer), ("num", 0))


EPSILON_SOURCE = observe(("rec", s.F, POWER_STEP, s.Q0))
EPSILON_OMEGA_SOURCE = observe(("rec", s.F, s.LAM(s.N, EPSILON_CLOSE), s.Q0))
ZETA_SOURCE = observe(("rec", s.F, s.LAM(s.N, EPSILON_INDEX), s.Q0))

# D(f)(c) = c[CN] (lambda d. Rec(U(d), lambda k. f, Q0)) F.
# Its proof uses the GLOBAL universal-realizer relation as an admissible
# relation on CN. A property only relative to one fixed ground relation would
# not suffice: EPSILON_INDEX itself changes the ground relation.
TRANSFORMER = s.arr(s.CN, s.CN)
DERIVATIVE_INDEX = s.LAM(TRANSFORMER, s.LAM(s.CN,
    s.APP(s.APP(("inst", s.V(0), s.CN), s.LAM(s.CN,
        ("rec", s.APP(EPSILON_CLOSE, s.V(0)), s.LAM(s.N, s.V(3)), s.Q0))), s.F)))
ZETA_INDEX = s.APP(DERIVATIVE_INDEX, EPSILON_INDEX)
ETA_SOURCE = observe(("rec", s.F, s.LAM(s.N, ZETA_INDEX), s.Q0))
FINITE_VEBLEN_SOURCE = observe(s.APP(
    ("rec", EPSILON_INDEX, s.LAM(s.N, DERIVATIVE_INDEX), s.Q0), s.F))

# P(c) implements the lower bound omega^alpha by one shift of function level.
OMEGA_POWER = s.LAM(s.CN, ("poly", s.APP(
    ("inst", s.V(0), s.arr(s.A, s.A)), ("inst", s.F, s.A))))
# K(c) = (c[CN -> CN] D P)(c). A direct 'exact Veblen index' relation
# is not closed at limit indices. Its proof instead uses strict lower indices:
# f covers xi when it bounds every phi_beta for beta < xi.
VEBLEN_DIAGONAL = s.LAM(s.CN, s.APP(s.APP(s.APP(
    ("inst", s.V(0), TRANSFORMER), DERIVATIVE_INDEX), OMEGA_POWER), s.V(0)))
GAMMA_SOURCE = observe(("rec", s.F, s.LAM(s.N, VEBLEN_DIAGONAL), s.Q0))


def finite_self_power(height):
    if not 0 <= height <= 4:
        raise ValueError("bounded test height exceeded")
    result = s.F
    for _ in range(height):
        result = s.APP(SELF_POWER, result)
    return result


class CompactIterationTests(unittest.TestCase):
    def test_types(self):
        self.assertEqual(s.infer(SELF_POWER), s.arr(s.CN, s.CN))
        self.assertEqual(s.infer(EPSILON_CLOSE), s.arr(s.CN, s.CN))
        self.assertEqual(s.infer(EPSILON_INDEX), s.arr(s.CN, s.CN))
        self.assertEqual(s.infer(DERIVATIVE_INDEX), s.arr(TRANSFORMER, TRANSFORMER))
        self.assertEqual(s.infer(ZETA_INDEX), TRANSFORMER)
        self.assertEqual(s.infer(OMEGA_POWER), TRANSFORMER)
        self.assertEqual(s.infer(VEBLEN_DIAGONAL), TRANSFORMER)
        for source in (EPSILON_SOURCE, EPSILON_OMEGA_SOURCE, ZETA_SOURCE,
                       ETA_SOURCE, FINITE_VEBLEN_SOURCE, GAMMA_SOURCE):
            self.assertEqual(s.infer(source), s.N)

    def test_fixed_outer_choices_match_unrolled_sources(self):
        for height in range(4):
            fixed = observe(finite_self_power(height))
            for later in ([], [1], [2, 0], [1, 1]):
                actual = query_trace(EPSILON_SOURCE, [height] + later)
                expected = query_trace(fixed, later)
                self.assertEqual(actual[:2], (expected[0] + 1, expected[1]))

    def test_zero_choices_of_higher_sources(self):
        for source in (EPSILON_OMEGA_SOURCE, ZETA_SOURCE):
            count, normal, _ = query_trace(source, [0, 0])
            self.assertEqual((count, normal), (2, ("n", 0)))

    def test_bounded_derivative_query_traces(self):
        for source in (ETA_SOURCE, FINITE_VEBLEN_SOURCE, GAMMA_SOURCE):
            for answers in ([0], [1, 0], [2, 0], [1, 1, 0], [1, 1, 1, 0]):
                _, normal, _ = query_trace(source, answers, max_steps=5000, max_queries=32)
                self.assertEqual(normal, ("n", 0))

    def test_literal_generator_fields(self):
        for name, source, fuel, columns in (
                ("epsilon", EPSILON_SOURCE, 145, 18),
                ("epsilon-omega lower source", EPSILON_OMEGA_SOURCE, 175, 21),
                ("zeta lower source", ZETA_SOURCE, 261, 24),
                ("eta lower source", ETA_SOURCE, 460, 33),
                ("finite Veblen lower source", FINITE_VEBLEN_SOURCE, 464, 33),
                ("Gamma lower source", GAMMA_SOURCE, 441, 35)):
            result = m.inspect(name, record=True, source=source)
            self.assertTrue(result["fields_replayed"])
            self.assertEqual(result["fuel"], fuel)
            self.assertEqual(result["independent_columns"], columns)
            self.assertEqual(result["warm_steps"], 0)


if __name__ == "__main__":
    print(json.dumps([m.inspect(name, record=True, source=source)
        for name, source in (("epsilon", EPSILON_SOURCE),
            ("epsilon-omega lower source", EPSILON_OMEGA_SOURCE),
            ("zeta lower source", ZETA_SOURCE),
            ("eta lower source", ETA_SOURCE),
            ("phi_omega(0) lower source", FINITE_VEBLEN_SOURCE),
            ("Gamma0 lower source", GAMMA_SOURCE))], indent=2))
