"""Translate a fixed finite Buchholz tree-class fragment to ordinary System F.

Sources: Buchholz (1987), section 1; Arai (1997), Definition 1;
Schwichtenberg, Proofs as Programs, sections 1--2. The conventions differ.
No new reduction rule, generator rule, or public notation is introduced here.
This file checks a translation, not the ordinal name of an arbitrary source.
The correspondence of its cofinal families with BHO/BO needs a separate proof.
"""

from functools import lru_cache
import json

import ordinal_tree_macros as m


N, X = m.N, m.X
app, arr, lam, var, num = m.app, m.arr, m.lam, m.var, m.num


@lru_cache(maxsize=16)
def tree_type(level):
    """T_0 is native Nat; T_v has 0, successor, and T_r branches for r<v."""
    if level == 0:
        return N
    if not 1 <= level <= 5:
        raise ValueError("research authoring is bounded to five tree classes")
    body = X
    for branch in reversed(range(level)):
        body = arr(arr(arr(tree_type(branch), X), X), body)
    return ("all", "X", arr(X, arr(arr(X, X), body)))


def fold(tree, level, carrier, zero, successor, limits):
    if len(limits) != level:
        raise ValueError("one handler is required for each branch class")
    return app(("inst", tree, carrier), zero, successor, *limits)


def algebra(level, body):
    for branch in reversed(range(level)):
        body = lam("lim" + str(branch), arr(arr(tree_type(branch), X), X), body)
    return ("poly", "X", lam("z", X, lam("s", arr(X, X), body)))


def handler_vars(level):
    return [var("lim" + str(branch)) for branch in range(level)]


def name(operation, level, other=None):
    return f"{operation}{level}" + ("" if other is None else f"_{other}")


def product_type(types):
    result = X
    for typ in reversed(types):
        result = arr(typ, result)
    return ("all", "X", arr(result, X))


def tuple_term(values, types):
    handler_type = X
    for typ in reversed(types):
        handler_type = arr(typ, handler_type)
    return ("poly", "X", lam("tuple_handler", handler_type,
                             app(var("tuple_handler"), *values)))


def project(value, index, types):
    handler = var("component" + str(index))
    for i, typ in reversed(list(enumerate(types))):
        handler = lam("component" + str(i), typ, handler)
    return app(("inst", value, types[index]), handler)


def constructors(level):
    """Closed constructors and tree arithmetic for one fixed level."""
    tree = tree_type(level)
    zero_name, succ_name = name("zero", level), name("succ", level)
    limits = [var(name("limit", level, r)) for r in range(level)]
    definitions = [(zero_name, tree, algebra(level, var("z")))]
    definitions.append((succ_name, arr(tree, tree), lam("a", tree,
        algebra(level, app(var("s"), fold(var("a"), level, X,
            var("z"), var("s"), handler_vars(level)))))))
    for r in range(level):
        index = tree_type(r)
        child = fold(app(var("f"), var("index")), level, X,
                     var("z"), var("s"), handler_vars(level))
        limit = lam("f", arr(index, tree), algebra(level,
            app(var("lim" + str(r)), lam("index", index, child))))
        definitions.append((name("limit", level, r), arr(arr(index, tree), tree), limit))
    definitions.append((name("add", level), arr(tree, arr(tree, tree)),
        lam("a", tree, lam("b", tree, fold(var("b"), level, tree,
            var("a"), var(succ_name), limits)))))
    # Buchholz's actual successor clause uses n+1, not n. Both have rank a*omega
    # for nonzero a, but only n+1 agrees as a tree and in finite branch tests.
    multiply = lam("a", tree, app(limits[0], lam("n", N,
        m.iterate(lam("x", tree, app(var(name("add", level)), var("x"), var("a"))),
                  var(zero_name), ("succ", var("n")), tree))))
    definitions.append((name("timesOmega", level), arr(tree, tree), multiply))
    for lower in range(1, level):
        embedding = lam("a", tree_type(lower), fold(var("a"), lower, tree,
            var(zero_name), var(succ_name), limits[:lower]))
        definitions.append((name("embed", lower, level),
                            arr(tree_type(lower), tree), embedding))
    omega = app(limits[0], lam("n", N, m.iterate(var(succ_name),
                        var(zero_name), var("n"), tree)))
    definitions.append((name("regular", level, 0), tree, omega))
    for r in range(1, level):
        definitions.append((name("regular", level, r), tree,
                            app(limits[r], var(name("embed", r, level)))))
    return definitions


def simultaneous_collapse(level, convention="schwichtenberg"):
    """One fold returns D_0(a), ..., D_(v-1)(a) with different result types.

    For a T_r-indexed node and sigma<r, its iteration is in T_r, using
    D_(r-1) of the children, NOT D_sigma. The tuple retains this distinction.
    """
    if convention not in ("schwichtenberg", "arai", "buchholz"):
        raise ValueError("unknown tree-collapse convention")
    components = [tree_type(sigma + 1) for sigma in range(level)]
    result = product_type(components)
    zero_values = [var(name("regular", s + 1, s)) for s in range(level)]
    if convention in ("arai", "buchholz"):
        # Both papers use D_0(0)=1, unlike Schwichtenberg's convention.
        zero_values[0] = app(var(name("succ", 1)), var(name("zero", 1)))
    zero = tuple_term(zero_values, components)
    successor = lam("old", result, tuple_term([
        app(var(name("timesOmega", s + 1)), project(var("old"), s, components))
        for s in range(level)], components))
    limits = []
    for r in range(level):
        branch_type = tree_type(r)
        family_type = arr(branch_type, result)
        values = []
        for sigma in range(level):
            if r <= sigma:
                child = project(app(var("family"), var("index")), sigma, components)
                values.append(app(var(name("limit", sigma + 1, r)),
                                  lam("index", branch_type, child)))
            else:
                # Arai iterates from 1; Schwichtenberg from Omega_(r-1).
                # Original Buchholz instead uses ONE step from 1, with
                # identical children for every n. It is NOT that iteration.
                step = lam("index", branch_type,
                    project(app(var("family"), var("index")), r - 1, components))
                seed = (app(var(name("succ", r)), var(name("zero", r)))
                        if convention in ("arai", "buchholz")
                        else var(name("regular", r, r - 1)))
                index = (app(step, seed) if convention == "buchholz"
                         else m.iterate(step, seed, var("n"), branch_type))
                child = project(app(var("family"), index), sigma, components)
                values.append(app(var(name("limit", sigma + 1, 0)), lam("n", N, child)))
        limits.append(lam("family", family_type, tuple_term(values, components)))
    value = lam("a", tree_type(level), fold(var("a"), level, result, zero, successor, limits))
    definitions = [(name("allD", level), arr(tree_type(level), result), value)]
    for sigma in range(level):
        value = lam("a", tree_type(level),
                    project(app(var(name("allD", level)), var("a")), sigma, components))
        definitions.append((name("D", level, sigma), arr(tree_type(level), components[sigma]), value))
    return definitions


def definitions(level, convention="schwichtenberg"):
    result = []
    for v in range(1, level + 1):
        result.extend(constructors(v))
    result.extend(simultaneous_collapse(level, convention))
    result.extend((("read", arr(arr(N, N), N), m.READ),
                   ("delay", arr(N, N), m.DELAY)))
    return result


def program(ordinal, level, convention="schwichtenberg"):
    """Interpret a T_1 expression, with a fixed T_level collapse library."""
    assert tree_type(1) == m.O
    return m.program_for(ordinal, tuple(definitions(level, convention)))


def collapsed_regular(level=2):
    return app(var(name("D", level, 0)), var(name("regular", level, level - 1)))


def cofinal_candidate(level=2):
    """L(n -> D_0(D_(v-1)^n(0))). Name calibration is a separate task."""
    iterate_highest = m.iterate(var(name("D", level, level - 1)),
        var(name("zero", level)), var("n"), tree_type(level))
    return app(var(name("limit", 1, 0)), lam("n", N,
               app(var(name("D", level, 0)), iterate_highest)))


def free_variables(term):
    """Term-level variables of the small named authoring AST, not type names."""
    tag = term[0]
    if tag == "var":
        return {term[1]}
    if tag == "num":
        return set()
    if tag == "lam":
        return free_variables(term[3]) - {term[1]}
    if tag == "poly":
        return free_variables(term[2])
    if tag == "inst":
        return free_variables(term[1])
    return set().union(*(free_variables(child) for child in term[1:]))


def prune_definitions(ordinal, definitions):
    """Remove unused authoring let-bindings; do not change the runtime kernel."""
    needed = free_variables(ordinal) | {"read", "delay"}
    retained = []
    for binding in reversed(definitions):
        variable, _, value = binding
        if variable in needed:
            retained.append(binding)
            needed.remove(variable)
            needed.update(free_variables(value))
    if needed:
        raise ValueError("unbound authoring names: " + repr(sorted(needed)))
    return tuple(reversed(retained))


def variable_uses(term, variable):
    if term[0] == "var":
        return int(term[1] == variable)
    if term[0] == "num":
        return 0
    if term[0] == "lam":
        return 0 if term[1] == variable else variable_uses(term[3], variable)
    if term[0] == "poly":
        return variable_uses(term[2], variable)
    if term[0] == "inst":
        return variable_uses(term[1], variable)
    return sum(variable_uses(child, variable) for child in term[1:])


def substitute_global(term, variable, value):
    """Safe named substitution for our globally distinct library names."""
    if not variable_uses(term, variable):
        return term
    tag = term[0]
    if tag == "var":
        return value
    if tag == "lam":
        if term[1] in free_variables(value):
            raise ValueError("authoring substitution would capture a name")
        return (tag, term[1], term[2], substitute_global(term[3], variable, value))
    if tag == "poly":
        return (tag, term[1], substitute_global(term[2], variable, value))
    if tag == "inst":
        return (tag, substitute_global(term[1], variable, value), term[2])
    return (tag, *(substitute_global(child, variable, value) for child in term[1:]))


def inline_once_program(ordinal, bindings):
    """Inline only single-use bindings: no source-size explosion or new rule."""
    bindings = list(prune_definitions(ordinal, bindings))
    body = m.fold(ordinal, N, num(0), var("delay"), var("read"))
    # Process late bindings first, including occurrences in retained values.
    for i in reversed(range(len(bindings))):
        variable, _, value = bindings[i]
        uses = variable_uses(body, variable)
        uses += sum(variable_uses(entry[2], variable) for entry in bindings[i + 1:])
        if uses == 1:
            body = substitute_global(body, variable, value)
            for j in range(i + 1, len(bindings)):
                other, typ, term = bindings[j]
                bindings[j] = other, typ, substitute_global(term, variable, value)
            bindings.pop(i)
    for variable, typ, value in reversed(bindings):
        body = app(lam(variable, typ, body), value)
    return m.compile_term(body, budget=m.dqdn.Budget(seconds=2, operations=50000))


def compact_bho_program(ordinal=None, inline_once=False):
    """The original two-level fragment needs no simultaneous product.

    D_0's high branch is L(n -> f(f(1))). D_1 preserves both branch
    classes. Each can therefore be folded separately. This is a source
    optimization of exactly the original rules, not a new collapsing rule.
    """
    low, high = tree_type(1), tree_type(2)
    one = app(var(name("succ", 1)), var(name("zero", 1)))
    high_branch = lam("family", arr(low, low),
        app(var(name("limit", 1, 0)), lam("n", N,
            app(var("family"), app(var("family"), one)))))
    d0 = lam("a", high, fold(var("a"), 2, low, one,
        var(name("timesOmega", 1)), [var(name("limit", 1, 0)), high_branch]))
    d1 = lam("a", high, fold(var("a"), 2, high, var(name("regular", 2, 1)),
        var(name("timesOmega", 2)), [var(name("limit", 2, r)) for r in range(2)]))
    bindings = constructors(1) + constructors(2) + [
        (name("D", 2, 0), arr(high, low), d0),
        (name("D", 2, 1), arr(high, high), d1),
        ("read", arr(arr(N, N), N), m.READ), ("delay", arr(N, N), m.DELAY)]
    ordinal = cofinal_candidate(2) if ordinal is None else ordinal
    if inline_once:
        return inline_once_program(ordinal, bindings)
    return m.program_for(ordinal, prune_definitions(ordinal, bindings))


if __name__ == "__main__":
    source = program(cofinal_candidate(2), 2)
    print(json.dumps(m.inspect("Buchholz T2 cofinal candidate", record=True, source=source), indent=2))
