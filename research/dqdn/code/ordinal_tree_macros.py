"""Ordinary System F macros for the existing DQDN interpreter.

This is a bounded authoring/typing experiment, NOT a new notation or an ordinal
rank oracle. In particular an independently authored graph is not automatically
a TOP-standard expression, and a builder path does not settle its prefix value.
"""

from functools import lru_cache
import json
from time import monotonic

import check_dqdn_seeds as check
import dqdn
import typed_builder as tb
from test_typed_builder import Author


N = ("nat",)
X = ("tv", "X")
arr = lambda a, b: ("arr", a, b)
var = lambda name: ("var", name)
lam = lambda name, typ, body: ("lam", name, typ, body)
num = lambda n: ("num", n)


def app(function, *arguments):
    for argument in arguments:
        function = ("app", function, argument)
    return function


O = ("all", "X", arr(X, arr(arr(X, X), arr(arr(arr(N, X), X), X))))
OO = arr(O, O)
NO = arr(N, O)


@lru_cache(maxsize=10000)
def compile_type(typ, names=()):
    tag = typ[0]
    if tag == "nat":
        return typ
    if tag == "tv":
        return (tag, names.index(typ[1]))
    if tag == "arr":
        return (tag, compile_type(typ[1], names), compile_type(typ[2], names))
    if tag == "all":
        return (tag, compile_type(typ[2], (typ[1],) + names))
    raise ValueError("not a System F type")


def compile_term(term, names=(), type_names=(), budget=None):
    if budget is not None:
        budget.tick()
    tag = term[0]
    recur = lambda node, ctx=names, tctx=type_names: compile_term(node, ctx, tctx, budget)
    if tag == "var":
        return (tag, names.index(term[1]))
    if tag == "num":
        return term
    if tag == "lam":
        return (tag, compile_type(term[2], type_names), recur(term[3], (term[1],) + names))
    if tag == "poly":
        return (tag, recur(term[2], names, (term[1],) + type_names))
    if tag == "inst":
        return (tag, recur(term[1]), compile_type(term[2], type_names))
    if tag in ("app", "rec", "query", "succ"):
        return (tag, *(recur(child) for child in term[1:]))
    raise ValueError("not a source term")


def fold(ordinal, carrier, zero, successor, limit):
    return app(("inst", ordinal, carrier), zero, successor, limit)


def algebra(body):
    return ("poly", "X", lam("z", X, lam("s", arr(X, X),
            lam("l", arr(arr(N, X), X), body))))


def iterate(function, seed, index, carrier):
    return ("rec", seed, lam("i", N, lam("r", carrier, app(function, var("r")))), index)


ZERO = algebra(var("z"))
SUCC = lam("a", O, algebra(app(var("s"),
        fold(var("a"), X, var("z"), var("s"), var("l")))))
LIMIT = lam("f", NO, algebra(app(var("l"), lam("n", N,
        fold(app(var("f"), var("n")), X, var("z"), var("s"), var("l"))))))
ADD = lam("a", O, lam("b", O,
      fold(var("b"), O, var("a"), var("succO"), var("limO"))))
MUL_OMEGA = lam("a", O, app(var("limO"), lam("n", N,
    iterate(lam("x", O, app(var("addO"), var("x"), var("a"))),
            var("zero"), var("n"), O))))
OMEGA_POW = lam("a", O,
    fold(var("a"), O, var("one"), var("mulOmega"), var("limO")))
CLOSURE = lam("f", OO, lam("a", O, app(var("limO"), lam("n", N,
    iterate(var("f"), var("a"), var("n"), O)))))
DERIVATIVE = lam("f", OO, lam("a", O,
    fold(var("a"), O, app(var("closure"), var("f"), var("zero")),
         lam("x", O, app(var("closure"), var("f"), app(var("succO"), var("x")))),
         var("limO"))))

# At a limit Veblen index, enumerate the common fixed points directly. Merely
# iterating the pointwise supremum of the earlier functions is not safe here:
# it can reach a fixed point in finitely many steps, and a constant Lim tail
# would add an unwanted successor to the tree rank.
VEBLEN_LIMIT = lam("family", arr(N, OO), lam("a", O,
    fold(var("a"), O,
         app(var("limO"), lam("n", N, app(var("family"), var("n"), var("zero")))),
         lam("x", O, app(var("limO"), lam("n", N,
             app(var("family"), var("n"), app(var("succO"), var("x")))))),
         var("limO"))))
VEBLEN = lam("a", O,
    fold(var("a"), OO, var("omegaPow"), var("derivative"), var("veblenLimit")))
DIAGONAL = lam("a", O, app(var("veblen"), var("a"), var("zero")))

# This reader forces the answer ONCE before it is passed to f. The naive
# f(Q(0)) may duplicate the query when f uses its numerical input more than once.
READ = lam("f", arr(N, N), ("rec", app(var("f"), num(0)),
    lam("k", N, lam("unused", N, app(var("f"), ("succ", var("k"))))),
    ("query", num(0))))
# One query before x. The recursive accumulator is deliberately discarded.
DELAY = lam("x", N, ("rec", var("x"),
    lam("k", N, lam("unused", N, var("x"))), ("query", num(0))))


DEFINITIONS = (
    ("zero", O, ZERO),
    ("succO", OO, SUCC),
    ("limO", arr(NO, O), LIMIT),
    ("one", O, app(var("succO"), var("zero"))),
    ("addO", arr(O, OO), ADD),
    ("mulOmega", OO, MUL_OMEGA),
    ("omegaPow", OO, OMEGA_POW),
    ("closure", arr(OO, OO), CLOSURE),
    ("derivative", arr(OO, OO), DERIVATIVE),
    ("read", arr(arr(N, N), N), READ),
    ("delay", arr(N, N), DELAY),
)

VEBLEN_DEFINITIONS = (
    ("veblenLimit", arr(arr(N, OO), OO), VEBLEN_LIMIT),
    ("veblen", arr(O, OO), VEBLEN),
    ("diagonal", OO, DIAGONAL),
)


def program_for(ordinal, definitions=DEFINITIONS):
    source = fold(ordinal, N, num(0), var("delay"), var("read"))
    for name, typ, value in reversed(definitions):
        source = app(lam(name, typ, source), value)
    return compile_term(source, budget=dqdn.Budget(seconds=2, operations=50000))


def program(derivatives=1):
    """D^k(omegaPow)(0): intended epsilon0, zeta0, eta0, ... for k=1,2,3.

    All definitions expand into ordinary typed lambda/application/recursor terms.
    Let-binding prevents duplicating entire macro bodies in the source graph.
    """
    function = var("omegaPow")
    for _ in range(derivatives):
        function = app(var("derivative"), function)
    return program_for(app(function, var("zero")))


def gamma_program():
    return program_for(app(var("closure"), var("diagonal"), var("zero")),
                       DEFINITIONS + VEBLEN_DEFINITIONS)


def finite_veblen_limit_program():
    functions = iterate(var("derivative"), var("omegaPow"), var("n"), OO)
    return program_for(app(var("limO"), lam("n", N, app(functions, var("zero")))))


class RecordingAuthor(Author):
    """Record actual generator fields, reusing already available judgments."""

    def __init__(self, terms, level=1):
        super().__init__(terms, level)
        self.library = self.t.initial_library()
        self.choices = []
        self.actions = []
        self.type_cache = {}
        self.term_cache = {}

    def do(self, rule, *args):
        entry = super().do(rule, *args)
        # Do not spend another construction on an identical fact already stored.
        if any(entry in self.t.available(self.library, sort)
               for sort, tags in tb.SORT_TAGS.items() if self.t.data[entry][0] in tags):
            return entry
        rule_index = [name for name, _ in tb.RULES].index(rule)
        fields = [rule_index]
        for sort, arg in zip(tb.RULES[rule_index][1], args):
            fields.append(self.t.parts(arg, "n")[0] if sort == "number" else
                          self.t.available(self.library, sort).index(arg))
        fields.append(0)
        self.choices.extend(fields)
        self.actions.append((rule, fields))
        self.library = self.t.make("li", entry, self.library)
        return entry

    def typ(self, typ, delta):
        key = typ, delta
        if key not in self.type_cache:
            self.type_cache[key] = super().typ(typ, delta)
        return self.type_cache[key]

    def term(self, source, context):
        key = id(source), context
        if key not in self.term_cache:
            self.term_cache[key] = super().term(source, context)
        return self.term_cache[key]


def inspect(derivatives=1, record=False, source=None):
    started = monotonic()
    source = program(derivatives) if source is None else source
    assert check.infer(source) == N
    terms = tb.Terms(dqdn.Budget(seconds=12, operations=3000000, nodes=100000))
    original = check.erase(source, terms)
    current = original
    warm_steps = 0
    while warm_steps < 5000:
        selected = terms.demand(current)
        if selected is None or terms.data[selected[0]][0] == "q":
            break
        current = terms.computation_child(current, 0)
        warm_steps += 1
    selected = terms.demand(current)
    assert selected is not None and terms.data[selected[0]][0] == "q"
    graph = dqdn.append_program((), terms, current)
    result = {"derivatives": derivatives, "typed": True,
              "warm_steps": warm_steps, "independent_columns": len(graph),
              "query_exposed": True, "standard_position_claimed": False}
    if record:
        terms.budget = dqdn.Budget(seconds=15, operations=5000000, nodes=150000)
        author = RecordingAuthor(terms)
        context = terms.available(author.library, "ctx")[0]
        proof = author.term(source, context)
        assert terms.parts(proof, "ep")[2] == original
        # Authoring and the independent field replay are separate bounded runs.
        # Keep the same limits for each, rather than spending the replay budget
        # during the preceding generation of its input.
        terms.budget = dqdn.Budget(seconds=15, operations=5000000, nodes=150000)
        state = terms.builder(1, len(author.choices), terms.initial_library())
        for choice in author.choices:
            state = terms.builder_child(state, choice)
        actual = terms.builder_child(state, 0)
        assert actual == original
        result.update(builder_actions=len(author.actions), fuel=len(author.choices),
                      generator_fs_bound=2 * len(author.choices) + 2,
                      fields_replayed=True)
    result["seconds"] = round(monotonic() - started, 3)
    return result


if __name__ == "__main__":
    print(json.dumps([inspect(k) for k in (1, 2, 3)], indent=2))
