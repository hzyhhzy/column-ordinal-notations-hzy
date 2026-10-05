"""Bounded adversarial checks; these do not prove strong normalization.

The production notation is not modified. In particular, an untyped loop is
only a negative control and is not admitted into the TOP-generated domain.
"""

import random
import unittest

import check_dqdn_seeds as seeds
import dqdn
import typed_builder as tb


def ref_shift(term, amount, variable, binders, depth=0):
    tag, *args = term
    if tag == variable:
        index = args[0]
        return (tag, index + amount if index >= depth else index)
    if tag in ("n", "tn", "ks"):
        return term
    if tag in ("tf", "tl"):
        return (tag, args[0], ref_shift(args[1], amount, variable, binders, depth + 1))
    return (tag, *(ref_shift(x, amount, variable, binders, depth + (tag in binders))
                   for x in args))


def ref_replace(term, argument, variable, binders, depth=0):
    """Replace index zero without deleting the binder (different algorithm)."""
    tag, *args = term
    if tag == variable:
        return (ref_shift(argument, depth, variable, binders)
                if args[0] == depth else term)
    if tag in ("n", "tn", "ks"):
        return term
    if tag in ("tf", "tl"):
        return (tag, args[0], ref_replace(args[1], argument, variable, binders, depth + 1))
    return (tag, *(ref_replace(x, argument, variable, binders, depth + (tag in binders))
                   for x in args))


def ref_top_substitution(body, argument, variable, binders):
    raised = ref_shift(argument, 1, variable, binders)
    replaced = ref_replace(body, raised, variable, binders)
    return ref_shift(replaced, -1, variable, binders)


def import_tree(t, tree):
    tag, *args = tree
    if tag in t.atom_arities:
        return t.make(tag, *args)
    return t.make(tag, *(import_tree(t, x) for x in args))


def export_tree(t, root):
    tag, *args = t.data[root]
    if tag in t.atom_arities:
        return (tag, *args)
    return (tag, *(export_tree(t, x) for x in args))


def random_tree(rng, depth, free, types=False):
    variable = "tx" if types else "v"
    if depth == 0:
        return ((variable, rng.randrange(free)) if rng.randrange(2) else
                ("tn",) if types else ("n", rng.randrange(4)))
    tag = rng.choice(("ta", "tt", "tf", "tl", "atom") if types else
                     ("a", "l", "s", "q", "r", "atom"))
    if tag == "atom":
        return random_tree(rng, 0, free, types)
    if tag in ("tf", "tl"):
        return (tag, ("ks",), random_tree(rng, depth - 1, free + 1, True))
    arity = {"a": 2, "l": 1, "s": 1, "q": 1, "r": 3, "ta": 2, "tt": 2}[tag]
    return (tag, *(random_tree(rng, depth - 1, free + (tag == "l"), types)
                   for _ in range(arity)))


def tree_demand_step(term, answer):
    """Independent, unshared occurrence-tree step; None means stopped."""
    tag, *args = term
    if tag == "a":
        if args[0][0] == "l":
            return ref_top_substitution(args[0][1], args[1], "v", {"l"})
        position = 0
    elif tag in ("s", "q", "r"):
        position = 2 if tag == "r" else 0
        if args[position][0] == "n":
            number = args[position][1]
            if tag == "s":
                return ("n", number + 1)
            if tag == "q":
                return ("n", answer)
            z, step, _ = args
            if number == 0:
                return z
            previous = ("n", number - 1)
            return ("a", ("a", step, previous), ("r", z, step, previous))
    else:
        return None
    child = tree_demand_step(args[position], answer)
    if child is None:
        return None
    args[position] = child
    return (tag, *args)


def bounded_export(t, root, maximum=20_000):
    """Test trees may unshare a DAG; enforce a separate small expansion cap."""
    remaining = maximum

    def visit(node):
        nonlocal remaining
        remaining -= 1
        if remaining < 0:
            raise RuntimeError("test-only unshared tree budget exceeded")
        tag, *args = t.data[node]
        if tag in t.atom_arities:
            return (tag, *args)
        return (tag, *(visit(x) for x in args))

    return visit(root)


class BoundaryAudit(unittest.TestCase):
    def test_2000_substitutions_against_separate_three_pass_definition(self):
        rng = random.Random(20261005)
        for types in (False, True):
            t = tb.Terms(dqdn.Budget(seconds=8, nodes=100_000, operations=2_000_000))
            for _ in range(1000):
                body = random_tree(rng, 4, 4, types)
                argument = random_tree(rng, 3, 3, types)
                b, a = import_tree(t, body), import_tree(t, argument)
                actual = t.type_walk(b, a, True) if types else t.substitute(b, a)
                expected = ref_top_substitution(body, argument,
                                                "tx" if types else "v", {"l"})
                self.assertEqual(export_tree(t, actual), expected)

    def test_eta_rejects_a_free_occurrence_of_removed_variable(self):
        t = tb.Terms(dqdn.Budget(seconds=2))
        star = t.make("ks")
        # lambda X. ((lambda Y. X) X) must not eta-reduce: X occurs in F.
        dependent_function = t.make("tl", star, t.make("tx", 1))
        bad_eta = t.make("tl", star,
                         t.make("tt", dependent_function, t.make("tx", 0)))
        with self.assertRaises(tb.BadConstruction):
            t.type_step(bad_eta, 0, eta=True)

    def test_untyped_loop_is_real_but_nonstandard(self):
        t = tb.Terms(dqdn.Budget(seconds=2))
        variable = t.make("v", 0)
        delta = t.make("l", t.make("a", variable, variable))
        omega = t.make("a", delta, delta)
        self.assertEqual(t.computation_child(omega, 0), omega)
        columns = dqdn.append_program((), t, omega)
        self.assertEqual(len(columns), 5)
        self.assertFalse(tb.is_standard(columns))
        for _ in range(20):
            child = tb.expand(columns, 1)
            self.assertLess(tb.compare(child, columns), 0)
            self.assertEqual(len(child), len(columns) + 1)
            self.assertFalse(tb.is_standard(child))
            columns = child

    def test_more_reachable_count_words_have_no_collisions(self):
        seen, frontier, words = set(), {tb.root(1)}, {}
        for _ in range(8):
            later = set()
            for columns in frontier:
                if columns in seen:
                    continue
                seen.add(columns)
                word = tb.counts(columns)
                if word in words:
                    self.assertEqual(words[word], columns)
                words[word] = columns
                for n in range(5):
                    child = tb.expand(columns, n)
                    self.assertLess(tb.compare(child, columns), 0)
                    self.assertTrue(tb.is_standard(child))
                    if child:
                        later.add(child)
            frontier = later
            self.assertLess(len(seen) + len(frontier), 6000)
        self.assertGreater(len(seen), 100)

    def test_erased_graph_steps_match_unshared_typed_programs(self):
        # Check only short prefixes, not brute-force termination runs. The
        # source annotations pass the separate System F checker first.
        identity = ("poly", seeds.LAM(seeds.A, seeds.V(0)))
        identity_type = ("all", seeds.arr(seeds.A, seeds.A))
        self_application = seeds.APP(
            ("inst", seeds.APP(("inst", identity, identity_type), identity), seeds.N),
            ("num", 0))
        sources = [self_application, seeds.EPSILON]
        sources.extend(seeds.tower(height) for height in range(4))
        checked = 0
        for source in sources:
            self.assertEqual(seeds.infer(source), seeds.N)
            for offset in range(4):
                t = tb.Terms(dqdn.Budget(seconds=2, nodes=20_000, operations=500_000))
                current = seeds.erase(source, t)
                for turn in range(48):
                    tree = bounded_export(t, current)
                    answer = (0, 1, 3, 2)[(turn + offset) % 4]
                    expected = tree_demand_step(tree, answer)
                    if expected is None:
                        self.assertIsNone(t.demand(current))
                        break
                    current = t.computation_child(current, 2 * answer + 1)
                    self.assertEqual(bounded_export(t, current), expected)
                    checked += 1
        self.assertGreater(checked, 300)

    def test_a_shared_query_is_not_a_memoized_oracle_answer(self):
        t = tb.Terms(dqdn.Budget(seconds=2))
        query = t.make("q", t.numeral(0))
        step = t.make("l", t.make("l", t.make("v", 0)))
        current = t.make("r", query, step, query)
        # The same q(0) graph occurs as both base and index. Only the index
        # occurrence changes when the first answer is 1.
        current = t.computation_child(current, 3)
        self.assertEqual(t.data[current], ("r", query, step, t.numeral(1)))
        for _ in range(12):
            selected, _ = t.demand(current)
            if t.data[selected][0] == "q":
                break
            current = t.computation_child(current, 0)
        else:
            self.fail("did not reach the second occurrence of q(0)")
        self.assertEqual(selected, query)
        current = t.computation_child(current, 5)
        self.assertEqual(t.data[current], ("n", 2))


if __name__ == "__main__":
    unittest.main()
