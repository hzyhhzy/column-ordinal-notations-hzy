"""Literal TOP paths requested by the user; ordinal proofs are in the document.

All runs are bounded. This checks paths, counts and final source syntax, not
universal ordinal upper bounds for preceding builder branches.
"""

import json
import unittest

import dqdn
import typed_builder as tb
from locate_standard_small import Recorder, first_index, run_lengths
from small_generator_ranks import identity_step


FINITE_PATHS = {
    1: [1, 1], 2: [1, 4], 3: [1, 6], 4: [1, 8, 38],
    5: [1, 8], 6: [1, 10], 7: [1, 12], 8: [1, 14, 38],
    9: [1, 14], 10: [1, 16],
}


def replay(path):
    columns = tb.TOP
    for index in path:
        columns = tb.expand(columns, index,
            dqdn.Budget(seconds=3, operations=3000000, columns=15000, nodes=100000))
    return columns


def first_loop_path():
    record = Recorder()
    proof = record.looping_query()
    choices = record.choices
    path = [1, first_index(len(choices)) + 1]
    path += [first_index(choice) + 1 for choice in choices]
    return path + [1], record, proof


def first_double_loop_path():
    record = Recorder()
    t = record.terms
    zero = t.available(record.library, "term")[0]
    step = identity_step(record)
    query = record.construct("query", zero)
    first = record.construct("recursor", query, step, query)
    second = record.construct("recursor", first, step, first)
    assert len(record.choices) == 31
    path = [1, first_index(31) + 1]
    path += [first_index(choice) + 1 for choice in record.choices]
    path += [1, 1, 1]  # output u; first query answer 0; inner Rec-zero step
    expected = t.make("r", t.parts(first, "ep")[2],
                      t.parts(step, "ep")[2], t.parts(query, "ep")[2])
    return path, record, expected


def description(label, path):
    columns = replay(path)
    counts = tb.counts(columns)
    return {"label": label, "input": "TOP" + "".join(f"[{n}]" for n in path),
            "columns": len(columns), "count_runs": run_lengths(counts),
            "ordinal_proof_is_separate": True}


class RequestedPowerTests(unittest.TestCase):
    def test_finite_paths_and_count_lengths(self):
        for power, path in FINITE_PATHS.items():
            columns = replay(path)
            self.assertTrue(tb.is_standard(columns,
                dqdn.Budget(seconds=5, operations=5000000)))
            self.assertEqual(len(tb.counts(columns)), len(columns))

    def test_omega_plus_one_source_is_pending_output(self):
        path, record, proof = first_loop_path()
        columns = replay(path[:-1])
        roots = dqdn.decode(columns, record.terms)
        source = roots[columns[-1][1]]
        self.assertEqual(record.terms.data[source][0], "b")
        self.assertEqual(record.terms.builder_child(source, 0),
                         record.terms.parts(proof, "ep")[2])

    def test_omega_twice_source_exact_erasure(self):
        path, record, expected = first_double_loop_path()
        columns = replay(path)
        roots = dqdn.decode(columns, record.terms)
        self.assertEqual(roots[columns[-1][1]], expected)
        self.assertTrue(tb.is_standard(columns,
            dqdn.Budget(seconds=5, operations=5000000)))


def main():
    results = [description(f"omega^{power}", path)
               for power, path in FINITE_PATHS.items()]
    first_path, _, _ = first_loop_path()
    results.append(description("omega^(omega+1)", first_path[:-1]))
    second_path, _, _ = first_double_loop_path()
    results.append(description("omega^(omega*2)", second_path))
    print(json.dumps(results, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
