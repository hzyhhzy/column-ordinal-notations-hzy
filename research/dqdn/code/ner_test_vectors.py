"""Emit bounded Python reference fixtures on stdout, without changing rules."""
import json
import random

import dqdn
import typed_builder as tb
import check_dqdn_seeds as seeds
from test_typed_builder import Author
from locate_standard_small import Recorder, path_to_program


def text(columns):
    if columns == tb.TOP:
        return "TOP"
    return "".join("[" + ("!" if c[0] == "run" else c[0]) +
                   (":" + ",".join(map(str, c[1:])) if len(c) > 1 else "") + "]"
                   for c in columns)


class TracedTerms(tb.Terms):
    def __init__(self):
        super().__init__(dqdn.Budget(seconds=10, operations=5_000_000))
        self.commands = []
        self.inside = False

    def make(self, tag, *args):
        result = super().make(tag, *args)
        if not self.inside:
            values = list(map(str, args)) if tag in self.atom_arities else list(args)
            self.commands.append(["make", tag, values, result])
        return result

    def construct(self, rule, args, level):
        self.inside = True
        try:
            result = super().construct(rule, args, level)
        except tb.BadConstruction:
            self.commands.append(["construct", rule, list(args), level, None])
            raise
        else:
            self.commands.append(["construct", rule, list(args), level, result])
            return result
        finally:
            self.inside = False


def construction_trace():
    t = TracedTerms()
    star, delta, nil = (t.make(x) for x in ("ks", "ke", "nil"))
    context = t.make("ct", delta, nil)
    a = Author(t, 2)
    a.term(seeds.EPSILON, context)
    for height in range(4):
        a.term(seeds.tower(height), context)
    nat = a.do("nat_type", delta)
    d1 = a.do("kind_context", delta, star)
    var = a.do("type_variable", d1, t.numeral(0))
    identity = a.do("type_lambda", var)
    applied = a.do("type_application", identity, nat)
    eq = a.do("type_beta", applied, t.numeral(0))
    rev = a.do("equality_sym", eq)
    a.do("equality_refl", applied)
    a.do("equality_trans", eq, rev)
    zero = a.do("number", context, t.numeral(0))
    converted = a.do("convert", zero, rev)
    a.do("convert", converted, eq)
    a.do("weaken_type", nat, star)
    a.do("type_of", zero)
    function_kind = a.do("kind_arrow", star, star)
    d2 = a.do("kind_context", delta, function_kind)
    d3 = a.do("kind_context", d2, star)
    f = a.do("type_variable", d3, t.numeral(1))
    x = a.do("type_variable", d3, t.numeral(0))
    applied = a.do("type_application", f, x)
    a.do("type_eta", a.do("type_lambda", applied), t.numeral(0))
    a.do("successor", a.do("number", context, t.numeral(10**80 + 123)))
    a.do("term_context", delta)
    a.typ(seeds.CN, delta)
    rng = random.Random(20261005)
    library = t.initial_library()
    for _ in range(700):
        rule, sorts = rng.choice(tb.RULES)
        args = []
        for sort in sorts:
            if sort == "number":
                args.append(t.numeral(rng.randrange(5)))
            else:
                candidates = t.available(library, sort)
                if not candidates:
                    break
                args.append(rng.choice(candidates))
        if len(args) != len(sorts):
            continue
        try:
            result = t.construct(rule, args, 3)
        except tb.BadConstruction:
            continue
        library = t.make("li", result, library)
    return t.commands


def main():
    indices = [0, 1, 2, 3, 4, 8, 16, 40]
    queue, seen, rows = [tb.TOP], set(), []
    while queue and len(rows) < 160:
        columns = queue.pop(0)
        if columns in seen:
            continue
        seen.add(columns)
        children = [tb.expand(columns, n) for n in indices]
        rows.append([text(columns), [text(c) for c in children]])
        queue.extend(c for c in children if len(c) < 1200)
    recorder = Recorder()
    recorder.looping_query()
    path, endpoint, _ = path_to_program(recorder)
    current = tb.TOP
    for n in path:
        current = tb.expand(current, n)
        if current not in seen:
            seen.add(current)
            rows.append([text(current), [text(tb.expand(current, n)) for n in indices]])
    print(json.dumps({"indices": indices, "rows": rows, "path": path,
                      "endpoint": text(endpoint), "commands": construction_trace()},
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
