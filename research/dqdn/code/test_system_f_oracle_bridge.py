"""Bounded checks of the level-one interface, not proof extraction itself.

At most 16 numerals, 19 query tests, and 4 field replays; each run has a
3-second/30,000-node/300,000-operation budget and at most 4,000 steps.
No ordinal ranks or infinite trees are inferred from these finite tests.
"""

import unittest

import check_dqdn_seeds as s
import dqdn
import ordinal_tree_macros as m
import typed_builder as tb


N, X = m.N, m.X
CPLUS = ("all", "X", m.arr(X, m.arr(m.arr(X, X), m.arr(X, X))))

# This is the inhabited translation of the usual Church numeral type.
ENCODE_NAMED = m.lam("n", N, ("poly", "X",
    m.lam("default", X, m.lam("f", m.arr(X, X), m.lam("x", X,
        ("rec", m.var("x"),
         m.lam("k", N, m.lam("y", X, m.app(m.var("f"), m.var("y")))),
         m.var("n")))))))
DECODE_NAMED = m.lam("c", CPLUS,
    m.app(("inst", m.var("c"), N), m.num(0),
          m.lam("n", N, ("succ", m.var("n"))), m.num(0)))
ORACLE_NAMED = m.lam("c", CPLUS,
    m.app(ENCODE_NAMED, ("query", m.app(DECODE_NAMED, m.var("c")))))

# Main paper route: induction with native numbers and an unchanged function
# parameter. The default argument is merely typing evidence, not an extra query.
ITERATE_NAMED = m.lam("f", m.arr(N, N), m.lam("n", N,
    ("rec", m.num(0),
     m.lam("k", N, m.lam("value", N, m.app(m.var("f"), m.var("value")))),
     m.var("n"))))
DEFAULT_ID_NAMED = ("poly", "X",
    m.lam("default", X, m.lam("value", X, m.var("value"))))


def native_source(n):
    query = m.lam("x", N, ("query", m.var("x")))
    value = m.app(ITERATE_NAMED, query, m.num(n))
    return compile_named(m.app(("inst", DEFAULT_ID_NAMED, N),
                              ("query", m.num(999)), value))


def compile_named(term):
    return m.compile_term(term, budget=dqdn.Budget(
        seconds=3, nodes=30000, operations=300000))


def source(n, depth=1):
    term = m.app(ENCODE_NAMED, m.num(n))
    for _ in range(depth):
        term = m.app(ORACLE_NAMED, term)
    return compile_named(m.app(DECODE_NAMED, term))


def evaluate(source_term, oracle):
    assert s.infer(source_term) == N
    terms = tb.Terms(dqdn.Budget(seconds=3, nodes=30000, operations=300000))
    root = s.erase(source_term, terms)
    calls = []
    for _ in range(4000):
        selected = terms.demand(root)
        if selected is None:
            assert terms.data[root][0] == "n"
            return terms.data[root][1], calls
        redex, _ = selected
        answer = 0
        if terms.data[redex][0] == "q":
            arg = terms.data[redex][1]
            assert terms.data[arg][0] == "n", "oracle index was not forced"
            index = terms.data[arg][1]
            calls.append(index)
            answer = oracle(index)
        root = terms.computation_child(root, 2 * answer + 1)
    raise AssertionError("bounded bridge test exceeded 4000 steps")


class OracleBridgeTests(unittest.TestCase):
    def test_types_use_only_system_f(self):
        cplus = m.compile_type(CPLUS)
        self.assertEqual(s.infer(compile_named(ENCODE_NAMED)), s.arr(N, cplus))
        self.assertEqual(s.infer(compile_named(DECODE_NAMED)), s.arr(cplus, N))
        self.assertEqual(s.infer(compile_named(ORACLE_NAMED)), s.arr(cplus, cplus))

    def test_native_church_roundtrip(self):
        for n in range(16):
            term = compile_named(m.app(DECODE_NAMED,
                                      m.app(ENCODE_NAMED, m.num(n))))
            value, calls = evaluate(term, lambda _: self.fail("unexpected query"))
            self.assertEqual((value, calls), (n, []))

    def test_query_indices_are_forced(self):
        for n in range(6):
            value, calls = evaluate(source(n), lambda x: x + 2)
            self.assertEqual((value, calls), (n + 2, [n]))
            value, calls = evaluate(source(n, 2), lambda x: x + 2)
            self.assertEqual((value, calls), (n + 4, [n, n + 2]))

    def test_native_induction_and_unused_default(self):
        for n in range(7):
            value, calls = evaluate(native_source(n), lambda x: x + 2)
            self.assertEqual((value, calls), (2 * n, list(range(0, 2 * n, 2))))

    def test_real_level_one_generator_replay(self):
        samples = [source(n, depth) for n, depth in ((0, 1), (3, 1), (2, 2))]
        samples.append(native_source(3))
        for term in samples:
            terms = tb.Terms(dqdn.Budget(
                seconds=3, nodes=30000, operations=300000))
            author = m.RecordingAuthor(terms, level=1)
            context = terms.available(author.library, "ctx")[0]
            proof = author.term(term, context)
            erased = terms.parts(proof, "ep")[2]
            self.assertEqual(erased, s.erase(term, terms))
            self.assertFalse(any(row[0] in ("kk", "tl", "tt") for row in terms.data))
            terms.budget = dqdn.Budget(
                seconds=3, nodes=30000, operations=300000)
            root = terms.builder(1, len(author.choices), terms.initial_library())
            for answer in author.choices:
                root = terms.builder_child(root, answer)
            self.assertEqual(terms.builder_child(root, 0), erased)


if __name__ == "__main__":
    unittest.main()
