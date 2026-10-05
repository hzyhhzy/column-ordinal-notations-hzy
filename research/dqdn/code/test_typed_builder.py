import random
import unittest

import check_dqdn_seeds as seeds
import dqdn
import typed_builder as tb


class Author:
    """Test-only annotation reader; each action is a public local builder rule."""

    def __init__(self, terms, level):
        self.t, self.level = terms, level

    def do(self, rule, *args):
        return self.t.construct(rule, args, self.level)

    def typ(self, a, delta):
        if a[0] == "nat":
            return self.do("nat_type", delta)
        if a[0] == "tv":
            return self.do("type_variable", delta, self.t.numeral(a[1]))
        if a[0] == "arr":
            return self.do("type_arrow", self.typ(a[1], delta), self.typ(a[2], delta))
        if a[0] == "all":
            child = self.do("kind_context", delta, self.t.make("ks"))
            return self.do("type_forall", self.typ(a[1], child))
        raise ValueError("test annotation outside System F")

    def term(self, source, context):
        delta = self.t.parts(context, "ct")[0]
        tag, *args = source
        if tag in ("var", "num"):
            return self.do("variable" if tag == "var" else "number",
                           context, self.t.numeral(args[0]))
        if tag == "lam":
            child = self.do("extend_context", context, self.typ(args[0], delta))
            return self.do("lambda", self.term(args[1], child))
        if tag == "poly":
            child = self.do("lift_context", context, self.t.make("ks"))
            return self.do("polymorphic", self.term(args[0], child))
        if tag == "inst":
            return self.do("instantiate", self.term(args[0], context), self.typ(args[1], delta))
        rule = {"app": "application", "query": "query", "succ": "successor",
                "rec": "recursor"}[tag]
        return self.do(rule, *(self.term(x, context) for x in args))


class BuilderTests(unittest.TestCase):
    def setup_terms(self, level=2):
        t = tb.Terms(dqdn.Budget(seconds=3.0))
        context = t.make("ct", t.make("ke"), t.make("nil"))
        return t, Author(t, level), context

    def test_fair_first_occurrences_and_repetitions(self):
        for n in range(100):
            index = 2 * n + 1
            for _ in range(15):
                self.assertEqual(tb.fair_choice(index), n)
                index = 2 * index + 2
        self.assertEqual(tb.fair_choice((203 << 100000) - 2), 100)

    def test_epsilon_annotation_builds_without_type_normalizing(self):
        t, author, context = self.setup_terms(1)
        result = author.term(seeds.EPSILON, context)
        actual_context, actual_type, erased = t.parts(result, "ep")
        self.assertEqual(actual_context, context)
        self.assertEqual(t.data[actual_type], ("tn",))
        self.assertEqual(erased, dqdn.epsilon_seed(t))
        selected, _ = t.demand(erased)
        self.assertEqual(t.data[selected][0], "q")

    def test_simple_towers_at_level_zero(self):
        t, author, context = self.setup_terms(0)
        for height in range(7):
            result = author.term(seeds.tower(height), context)
            self.assertEqual(t.parts(result, "ep")[2], dqdn.finite_tower(t, height))
        with self.assertRaises(tb.BadConstruction):
            author.term(seeds.EPSILON, context)

    def test_epsilon_reachable_by_actual_generation_fields(self):
        t, _, context = self.setup_terms(1)

        class RecordingAuthor(Author):
            def __init__(self):
                super().__init__(t, 1)
                self.library = t.initial_library()
                self.choices = []

            def do(self, rule, *args):
                rule_index = [name for name, _ in tb.RULES].index(rule)
                sorts = tb.RULES[rule_index][1]
                self.choices.append(rule_index)
                for sort, argument in zip(sorts, args):
                    choice = (t.parts(argument, "n")[0] if sort == "number" else
                              t.available(self.library, sort).index(argument))
                    self.choices.append(choice)
                self.choices.append(0)  # deterministic local construction
                entry = super().do(rule, *args)
                self.library = t.make("li", entry, self.library)
                return entry

        author = RecordingAuthor()
        proof = author.term(seeds.EPSILON, context)
        source = t.builder(1, len(author.choices), t.initial_library())
        for choice in author.choices:
            self.assertEqual(t.data[source][0], "b")
            source = t.builder_child(source, choice)
        actual = t.builder_child(source, 0)
        self.assertEqual(actual, t.parts(proof, "ep")[2])
        self.assertEqual(actual, dqdn.epsilon_seed(t))

    def test_type_beta_conversion_and_kind_ceiling(self):
        t, author, context = self.setup_terms(2)
        delta = t.parts(context, "ct")[0]
        star = t.make("ks")
        body_context = author.do("kind_context", delta, star)
        variable = author.do("type_variable", body_context, t.numeral(0))
        identity_type_operator = author.do("type_lambda", variable)
        nat = author.do("nat_type", delta)
        applied = author.do("type_application", identity_type_operator, nat)
        equality = author.do("type_beta", applied, t.numeral(0))
        left, right = t.parts(equality, "eq")
        self.assertEqual(right, nat)
        zero = author.do("number", context, t.numeral(0))
        reverse = author.do("equality_sym", equality)
        converted = author.do("convert", zero, reverse)
        self.assertEqual(t.parts(converted, "ep")[1], t.parts(applied, "tp")[2])
        self.assertEqual(author.do("convert", converted, equality), zero)
        with self.assertRaises(tb.BadConstruction):
            t.construct("type_lambda", [variable], 1)

    def test_type_substitution_capture_and_eta(self):
        t, author, context = self.setup_terms(2)
        star, delta = t.make("ks"), t.parts(context, "ct")[0]
        # Under a second binder, substituting free X0 must become X1.
        body = t.make("tf", star, t.make("tx", 1))
        actual = t.type_walk(body, t.make("tx", 0), True)
        self.assertEqual(actual, body)
        function_kind = author.do("kind_arrow", star, star)
        d1 = author.do("kind_context", delta, function_kind)
        d2 = author.do("kind_context", d1, star)
        f = author.do("type_variable", d2, t.numeral(1))
        x = author.do("type_variable", d2, t.numeral(0))
        applied = author.do("type_application", f, x)
        abstraction = author.do("type_lambda", applied)
        equality = author.do("type_eta", abstraction, t.numeral(0))
        _, right = t.parts(equality, "eq")
        self.assertEqual(t.parts(right, "tp")[2], t.make("tx", 0))

    def test_reject_polymorphism_when_context_mentions_new_variable(self):
        t, author, context = self.setup_terms(1)
        delta = t.parts(context, "ct")[0]
        d1 = author.do("kind_context", delta, t.make("ks"))
        a = author.do("type_variable", d1, t.numeral(0))
        c1 = author.do("term_context", d1)
        c2 = author.do("extend_context", c1, a)
        variable = author.do("variable", c2, t.numeral(0))
        with self.assertRaises(tb.BadConstruction):
            author.do("polymorphic", variable)

    def test_generate_query_then_execute_it(self):
        t, _, _ = self.setup_terms()
        state = t.builder(0, 3, t.initial_library())
        query_rule = [name for name, _ in tb.RULES].index("query")
        for choice in (query_rule, 0, 0):
            state = t.builder_child(state, choice)
        self.assertEqual(t.data[state][0], "b")
        program = t.builder_child(state, 0)
        self.assertEqual(t.data[program], ("q", t.numeral(0)))
        self.assertEqual(t.data[t.computation_child(program, 11)], ("n", 5))

    def test_generation_fuel_bounds_with_bounded_random_choices(self):
        t, _, _ = self.setup_terms()
        rng = random.Random(20261005)
        for fuel in range(20):
            for _ in range(5):
                state = t.builder(2, fuel, t.initial_library())
                for _ in range(fuel + 1):
                    if t.data[state][0] != "b":
                        break
                    state = t.builder_child(state, rng.randrange(30))
                self.assertNotEqual(t.data[state][0], "b")

    def test_global_roots_and_prefix_expansion(self):
        for level in range(3):
            root = tb.root(level)
            self.assertEqual(dqdn.counts(root), (1, 2) * (level + 1))
            previous = ()
            for n in range(15):
                child = tb.expand(root, n, dqdn.Budget(seconds=2.0))
                self.assertEqual(child[:len(previous)], previous)
                self.assertLess(dqdn.counts(child), dqdn.counts(root))
                self.assertGreaterEqual(len(child), len(root) - 1 + 2 * n)
                previous = child

    def test_single_top_and_its_linear_prefix_sequence(self):
        previous = ()
        self.assertEqual(tb.counts(tb.TOP), (2,))
        self.assertTrue(tb.is_standard(tb.TOP))
        for n in range(12):
            child = tb.expand(tb.TOP, n)
            self.assertEqual(len(child), 2 * n)
            self.assertEqual(child[:len(previous)], previous)
            self.assertLess(tb.compare(child, tb.TOP), 0)
            previous = child
        with self.assertRaises(ValueError):
            tb.expand(tb.TOP, -1)
        with self.assertRaises(dqdn.ResourceLimit):
            tb.expand(tb.TOP, 1000, dqdn.Budget(columns=8))

    def test_common_standard_domain_and_count_injectivity(self):
        frontier, seen, words = {tb.root(1)}, set(), {}
        for _ in range(4):
            later = set()
            for parent in frontier:
                if parent in seen:
                    continue
                seen.add(parent)
                self.assertTrue(tb.is_standard(parent, dqdn.Budget(seconds=2.0)))
                word = dqdn.counts(parent)
                if word in words:
                    self.assertEqual(parent, words[word])
                words[word] = parent
                later.update(tb.expand(parent, n, dqdn.Budget(seconds=2.0)) for n in range(4))
            frontier = later
        self.assertFalse(tb.is_standard(dqdn.OMEGA))
        self.assertFalse(tb.is_standard((("g", 1),)))
        self.assertFalse(tb.is_standard((("g", 0), ("run", 9))))

    def test_bounded_random_constructions_have_independently_valid_kinds(self):
        t = tb.Terms(dqdn.Budget(seconds=4.0, operations=3_000_000))
        library = t.initial_library()
        star = t.make("ks")
        rng = random.Random(11052026)
        cache = {}

        def infer_kind(node, environment):
            key = (node, environment)
            if key in cache:
                return cache[key]
            t.budget.tick()
            tag, *args = t.data[node]
            if tag == "tn":
                result = star
            elif tag == "tx":
                self.assertLess(args[0], len(environment))
                result = environment[args[0]]
            elif tag == "ta":
                self.assertEqual(infer_kind(args[0], environment), star)
                self.assertEqual(infer_kind(args[1], environment), star)
                result = star
            elif tag in ("tf", "tl"):
                body_kind = infer_kind(args[1], (args[0],) + environment)
                if tag == "tf":
                    self.assertEqual(body_kind, star)
                    result = star
                else:
                    result = t.make("kk", args[0], body_kind)
            elif tag == "tt":
                function_kind = infer_kind(args[0], environment)
                domain, result = t.parts(function_kind, "kk")
                self.assertEqual(infer_kind(args[1], environment), domain)
            else:
                self.fail("not type syntax")
            cache[key] = result
            return result

        def inspect(entry):
            tag, *args = t.data[entry]
            if tag == "tp":
                delta, kind, typ = args
                environment = tuple(t.linked(delta, "kc", "ke"))
                self.assertEqual(infer_kind(typ, environment), kind)
            elif tag == "ep":
                context, typ, value = args
                delta, declarations = t.parts(context, "ct")
                environment = tuple(t.linked(delta, "kc", "ke"))
                self.assertEqual(infer_kind(typ, environment), star)
                term_types = t.linked(declarations, "dl")
                for a in term_types:
                    self.assertEqual(infer_kind(a, environment), star)
                stack, seen = [(value, len(term_types))], set()
                while stack:
                    node, depth = stack.pop()
                    if (node, depth) in seen:
                        continue
                    seen.add((node, depth))
                    node_tag, *node_args = t.data[node]
                    if node_tag == "v":
                        self.assertLess(node_args[0], depth)
                    elif node_tag != "n":
                        self.assertIn(node_tag, {"l", "a", "s", "r", "q"})
                        stack.extend((x, depth + (node_tag == "l")) for x in node_args)

        accepted = 0
        for _ in range(1000):
            rule, sorts = rng.choice(tb.RULES)
            arguments = []
            for sort in sorts:
                if sort == "number":
                    arguments.append(t.numeral(rng.randrange(4)))
                else:
                    candidates = t.available(library, sort)
                    if not candidates:
                        break
                    arguments.append(rng.choice(candidates))
            if len(arguments) != len(sorts):
                continue
            try:
                entry = t.construct(rule, arguments, 3)
            except tb.BadConstruction:
                continue
            inspect(entry)
            library = t.make("li", entry, library)
            accepted += 1
        self.assertGreater(accepted, 100)


if __name__ == "__main__":
    unittest.main()
