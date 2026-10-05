"""Bounded witnesses for the paper classification of the first G(1) entries.

Finite tests check actual builder fields and selected computation branches.
They DO NOT establish the universal ordinal upper bounds used by the table.
Bounds through fuel 31 are argued separately in the paper. Fuel 32..35 has
replayed lower witnesses only: its proposed upper classification was interrupted
by the user's pause request and must not be treated as established.
"""

import json
import unittest

import dqdn
import typed_builder as tb
from locate_standard_small import Recorder


def identity_step(record):
    t = record.terms
    context = t.available(record.library, "ctx")[0]
    nat = t.available(record.library, "type")[0]
    context1 = record.construct("extend_context", context, nat)
    context2 = record.construct("extend_context", context1, nat)
    variable = record.construct("variable", context2, t.numeral(0))
    return record.construct("lambda", record.construct("lambda", variable))


def rank_witness(fuel):
    if not 0 <= fuel <= 35:
        raise ValueError("the bounded witness constructor supports fuel 0 through 35")
    record = Recorder()
    t = record.terms
    zero = t.available(record.library, "term")[0]
    if fuel < 26:
        result = zero
        for _ in range(fuel // 3):
            result = record.construct("query", result)
    else:
        step = identity_step(record)
        query_count = (1 + (fuel - 31) // 3 if fuel >= 31
                       else 1 + (fuel - 26) // 3)
        index = zero
        for _ in range(query_count):
            index = record.construct("query", index)
        # From fuel 31, keeping a queried result (rather than always returning
        # zero) matters: that result drives one more outer unbounded loop.
        base = index if fuel >= 31 else zero
        result = record.construct("recursor", base, step, index)
        if fuel >= 31:
            # Four independent queries, three unbounded finite loops.
            # Repeated DAG references are not cached evaluations.
            result = record.construct("recursor", result, step, result)
    padding = fuel - len(record.choices)
    assert 0 <= padding <= 2
    choices = record.choices + [0] * padding
    original = t.parts(result, "ep")[2]
    state = t.builder(1, fuel, t.initial_library())
    for choice in choices:
        state = t.builder_child(state, choice)
    assert t.builder_child(state, 0) == original
    return record, original, choices


def proposed_builder_rank(fuel):
    """Paper formula through 31; uncompleted upper-bound candidate at 32..35."""
    if 0 <= fuel <= 25:
        return 0, fuel + 1 + fuel // 3
    if 26 <= fuel <= 30:
        return 1, fuel + 1 + (fuel - 26) // 3
    if 31 <= fuel <= 35:
        return 3, fuel + 1 + (fuel - 31) // 3
    raise ValueError("no audited formula at this fuel")


def tail_cnf(index):
    """CNF after epsilon0; results above n=65 use uncompleted candidates."""
    if not 1 <= index <= 73:
        raise ValueError("this table covers 1..73 only")
    result = []
    for child in range(index):
        exponent = proposed_builder_rank(tb.fair_choice(child))
        while result and result[-1][0] < exponent:
            result.pop()
        if result and result[-1][0] == exponent:
            result[-1] = exponent, result[-1][1] + 1
        else:
            result.append((exponent, 1))
    return result


def bounded_runtime(record, source, answers, max_queries=8):
    """Count at most 250 genuine steps, with at most eight queries."""
    t = record.terms
    t.budget = dqdn.Budget(seconds=2, operations=100000, nodes=20000)
    queries = 0
    for steps in range(251):
        selected = t.demand(source)
        if selected is None:
            return steps, queries
        if steps == 250:
            raise AssertionError("finite trace bound exceeded")
        if t.data[selected[0]][0] == "q":
            if queries >= max_queries:
                raise AssertionError("query count bound exceeded")
            answer = answers[queries] if queries < len(answers) else 0
            queries += 1
            index = 0 if answer == 0 else 2 * answer + 1
        else:
            index = 0
        source = t.computation_child(source, index)
    raise AssertionError("unreachable")


def omega_squared_witness():
    """R(Q0, (lambda k x. R(x,I,x)), Q0), using 49 actual fields."""
    record = Recorder()
    t = record.terms
    context = t.available(record.library, "ctx")[0]
    nat = t.available(record.library, "type")[0]
    zero = t.available(record.library, "term")[0]
    contexts = [context]
    for _ in range(4):
        contexts.append(record.construct("extend_context", contexts[-1], nat))
    last = record.construct("variable", contexts[4], t.numeral(0))
    inner_step = record.construct("lambda", record.construct("lambda", last))
    accumulator = record.construct("variable", contexts[2], t.numeral(0))
    body = record.construct("recursor", accumulator, inner_step, accumulator)
    step = record.construct("lambda", record.construct("lambda", body))
    query = record.construct("query", zero)
    proof = record.construct("recursor", query, step, query)
    assert len(record.choices) == 49
    state = t.builder(1, 49, t.initial_library())
    for choice in record.choices:
        state = t.builder_child(state, choice)
    source = t.parts(proof, "ep")[2]
    assert t.builder_child(state, 0) == source
    return record, source


def doubled_loop_witness(depth, initial_queries=1):
    """t_0=Q^p(0), t_(r+1)=R(t_r,I,t_r), with bounded DAG depth.

    The paper continuation-profile lemma gives source rank
    omega*(2**depth-1)+(p-1) for depth>=1. This routine only replays fields.
    """
    if not 1 <= depth <= 8 or not 1 <= initial_queries <= 3:
        raise ValueError("bounded witness parameters exceeded")
    record = Recorder()
    t = record.terms
    result = t.available(record.library, "term")[0]
    step = identity_step(record)
    for _ in range(initial_queries):
        result = record.construct("query", result)
    for _ in range(depth):
        result = record.construct("recursor", result, step, result)
    fuel = 18 + 3 * initial_queries + 5 * depth
    assert len(record.choices) == fuel
    state = t.builder(1, fuel, t.initial_library())
    for choice in record.choices:
        state = t.builder_child(state, choice)
    source = t.parts(result, "ep")[2]
    assert t.builder_child(state, 0) == source
    return record, source, fuel


class SmallRankWitnessTests(unittest.TestCase):
    def test_all_finite_rank_witnesses_and_fields(self):
        for fuel in range(26):
            record, source, choices = rank_witness(fuel)
            self.assertEqual(len(choices), fuel)
            self.assertEqual(bounded_runtime(record, source, []),
                             (fuel // 3, fuel // 3))

    def test_first_omega_rank_sources(self):
        for fuel in range(26, 31):
            queries = 1 + (fuel - 26) // 3
            for answer in range(6):
                record, source, choices = rank_witness(fuel)
                self.assertEqual(len(choices), fuel)
                self.assertEqual(bounded_runtime(record, source,
                    [0] * (queries - 1) + [answer]),
                    (queries + 3 * answer + 1, queries))

    def test_shared_program_is_evaluated_twice(self):
        for first in range(4):
            for second in range(4):
                for third in range(4):
                    record, source, choices = rank_witness(31)
                    self.assertEqual(len(choices), 31)
                    self.assertEqual(bounded_runtime(record, source,
                        [first, second, third, 0]),
                        (3 * (first + second + third) + 7, 4))

    def test_two_recursors_through_fuel_35(self):
        for fuel in range(31, 36):
            record, source, choices = rank_witness(fuel)
            p = 1 + (fuel - 31) // 3
            self.assertEqual(len(choices), fuel)
            self.assertEqual(bounded_runtime(record, source, [1] * (4 * p)),
                             (4 * p + 12, 4 * p))
            self.assertEqual(proposed_builder_rank(fuel),
                             (3, fuel + p))

    def test_fair_indices_of_first_transitions(self):
        self.assertEqual(tb.fair_choice(53), 26)
        self.assertTrue(all(tb.fair_choice(i) < 26 for i in range(53)))
        self.assertEqual(tb.fair_choice(63), 31)
        self.assertTrue(all(tb.fair_choice(i) < 31 for i in range(63)))
        self.assertEqual(tail_cnf(53), [((0, 34), 1), ((0, 17), 1)])
        self.assertEqual(tail_cnf(54), [((1, 27), 1)])
        self.assertEqual(tail_cnf(64), [((3, 32), 1)])

    def test_omega_squared_source_query_counts(self):
        for n in range(4):
            record, source = omega_squared_witness()
            _, queries = bounded_runtime(record, source, [n] + [1] * 8,
                                         max_queries=16)
            self.assertEqual(queries, 1 + 2 ** n)

    def test_doubled_loop_profiles_finite_branches(self):
        for depth in range(1, 5):
            for queries_per_leaf in (1, 2):
                record, source, fuel = doubled_loop_witness(depth, queries_per_leaf)
                count = queries_per_leaf * 2 ** depth
                steps, queries = bounded_runtime(record, source, [1] * count,
                                                  max_queries=32)
                self.assertEqual(queries, count)
                # Every R occurrence takes one recursion and two beta steps
                # per iteration plus a zero step; all selected indices are 1.
                self.assertEqual(steps, count + 4 * (2 ** depth - 1))
                self.assertEqual(fuel, 18 + 3 * queries_per_leaf + 5 * depth)


if __name__ == "__main__":
    print(json.dumps({"paper_classification_not_computer_proof": True,
        "nodes": [{"n": n, "tail_cnf": tail_cnf(n)}
                  for n in (1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 30, 40, 50,
                            52, 53, 54, 55, 56, 58, 60, 62, 64, 65,
                            66, 67, 68, 69, 70, 71, 72, 73)]}, indent=2))
