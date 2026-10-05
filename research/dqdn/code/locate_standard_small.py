"""Bounded, literal TOP paths for small DQDN standard expressions.

This checks reachability, not the paper ordinal-rank claims. No rules of the
notation are changed, and no independent program graph is admitted as a root.
"""

import json

import dqdn
import typed_builder as tb


def first_index(answer):
    return 0 if answer == 0 else 2 * answer + 1


class Recorder:
    def __init__(self):
        self.terms = tb.Terms(dqdn.Budget(seconds=5.0))
        self.library = self.terms.initial_library()
        self.choices = []

    def construct(self, rule, *arguments):
        t = self.terms
        index = [name for name, _ in tb.RULES].index(rule)
        self.choices.append(index)
        for sort, argument in zip(tb.RULES[index][1], arguments):
            if sort == "number":
                choice = t.parts(argument, "n")[0]
            else:
                choice = t.available(self.library, sort).index(argument)
            self.choices.append(choice)
        self.choices.append(0)
        entry = t.construct(rule, arguments, 0)
        self.library = t.make("li", entry, self.library)
        return entry

    def looping_query(self):
        """Seven essential local constructions, using 26 field actions."""
        t = self.terms
        context = t.available(self.library, "ctx")[0]
        nat = t.available(self.library, "type")[0]
        zero = t.available(self.library, "term")[0]
        context1 = self.construct("extend_context", context, nat)
        context2 = self.construct("extend_context", context1, nat)
        variable = self.construct("variable", context2, t.numeral(0))
        inner = self.construct("lambda", variable)
        step = self.construct("lambda", inner)
        query = self.construct("query", zero)
        return self.construct("recursor", query, step, query)


def path_to_program(record):
    """Follow the actual basic sequences; every selected child is last."""
    fuel = len(record.choices)
    path = [1, first_index(fuel) + 1]
    path += [first_index(choice) + 1 for choice in record.choices]
    path.append(1)  # B(0, library) -> last closed Nat program
    columns = tb.TOP
    lengths = []
    for n in path:
        columns = tb.expand(columns, n, dqdn.Budget(seconds=3.0, columns=20_000))
        lengths.append(len(columns))
    return path, columns, lengths


def run_lengths(word):
    result = []
    for value in word:
        if result and result[-1][0] == value:
            result[-1][1] += 1
        else:
            result.append([value, 1])
    return result


def main():
    record = Recorder()
    proof = record.looping_query()
    assert len(record.choices) == 26
    path, columns, lengths = path_to_program(record)
    roots = dqdn.decode(columns, record.terms)
    actual = roots[columns[-1][1]]
    expected = record.terms.parts(proof, "ep")[2]
    assert actual == expected
    selected, _ = record.terms.demand(actual)
    assert record.terms.data[selected][0] == "q"
    assert tb.is_standard(columns, dqdn.Budget(seconds=5.0, operations=5_000_000))
    print(json.dumps({
        "program": "R(Q(0), lambda k. lambda x. x, Q(0))",
        "fuel": len(record.choices),
        "choices": record.choices,
        "top_path": path,
        "columns": len(columns),
        "path_lengths": lengths,
        "count_runs": " ".join(f"{value}^{length}" for value, length in
                                 run_lengths(tb.counts(columns))),
        "literal_erasure_matches": True,
        "is_standard": True,
        "rank_warning": "Exact omega^omega uses the separate 26-action paper argument; this test only checks reachability.",
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
