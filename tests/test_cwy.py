"""Bounded CWY core/bound regressions; optional public fixtures for Node tests.

No private research imports, network access, long descending searches, or proof
claims. Python integers are exact; resource exclusions are explicitly reported.
"""
import argparse
import json
from pathlib import Path
import sys
from time import perf_counter

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "notations/CWY"))
import compact_wy as core
import compact_wy_bound as bounded


def run():
    started = perf_counter()
    statistics = dict(states=0, core_fs=0, bound_fs=0, prefixes=0,
                      roundtrips=0, comparisons=0, guards=0, exclusions=0)
    records, queue, seen = [], [core.zero(), ((),)], set()
    queue += [core.seed(m) for m in range(1, 7)]
    queue.append(core.parse("[][0:(0,1,1)][1:(0,1,2)][2:(0,1,2)]"))

    def budget(**extra):
        return core.Budget(seconds=0.6, max_nodes=12000, max_columns=100,
                           max_payload=300000, **extra)

    def tick():
        if perf_counter() - started > 18:
            raise AssertionError("18-second total test deadline")

    while queue and len(records) < 80:
        tick()
        term = queue.pop(0)
        if term in seen:
            continue
        seen.add(term)
        if len(term) > 12:
            statistics["exclusions"] += 1
            continue
        try:
            outputs = [core.fs(term, n, budget()) for n in range(4)]
            stretched = bounded.stretch(term, budget())
            shifted = int(len(term) == 2 and bool(term[-1]))
            bound_outputs = [bounded.fs(stretched, n, budget()) for n in range(4)]
            for n, target in enumerate(bound_outputs):
                expected = stretched[:-1] if n == 0 else bounded.stretch(
                    core.fs(term, n + shifted, budget()), budget())
                assert target == expected
        except core.ResourceLimit:
            statistics["exclusions"] += 1
            continue
        assert outputs[0] == term[:-1]
        for n, target in enumerate(outputs):
            if term:
                assert core.compare(target, term) < 0
            assert core.parse(core.format_expr(target)) == target
            if n:
                assert target[:len(outputs[n-1])] == outputs[n-1]
                assert bound_outputs[n][:len(bound_outputs[n-1])] == bound_outputs[n-1]
                statistics["prefixes"] += 2
            statistics["roundtrips"] += 1
        assert bounded.unstretch(stretched, budget()) == term
        assert bounded.parse(bounded.format_expr(stretched)) == stretched
        assert bounded.parse(bounded.format_expr(stretched, True)) == stretched
        statistics["roundtrips"] += 3
        for previous in records[-4:]:
            other = previous["term"]
            other_stretched = previous["stretched"]
            assert core.compare(term, other) == bounded.compare(stretched, other_stretched)
            statistics["comparisons"] += 1
        records.append(dict(term=term, text=core.format_expr(term),
                            fs=[core.format_expr(t) for t in outputs],
                            stretched=stretched, stretched_text=bounded.format_expr(stretched)))
        statistics["states"] += 1
        statistics["core_fs"] += 4
        statistics["bound_fs"] += 4
        for child in outputs[1:]:
            if len(queue) < 180 and len(child) <= 12 and child not in seen:
                queue.append(child)

    previous = ()
    for n in range(10):
        target = bounded.fs(bounded.boundary(), n, budget())
        assert target[:len(previous)] == previous
        assert bounded.compare(target, bounded.boundary()) < 0
        expected = ((),) if n == 0 else ((), (), *([bounded.S] * (n - 1)))
        assert target == expected
        previous = target
        statistics["bound_fs"] += 1
        statistics["prefixes"] += 1
    # The full independent decrement oracle has the known nontrivial graft.
    regression = core.parse("[][0:(0,1,1)][1:(0,1,2)][2:(0,1,2)]")
    lowered = core.minus_column(regression, budget())
    assert lowered == ((2, (0, 1, 1)), (1, (0, 1, 3)))
    for operation in [lambda: core.fs(core.seed(3), 20, core.Budget(max_columns=3)),
                      lambda: bounded.fs(bounded.boundary(), 20, core.Budget(max_columns=3))]:
        try:
            operation()
        except core.ResourceLimit:
            statistics["guards"] += 1
        else:
            raise AssertionError("Expected an explicit resource refusal")
    tick()
    statistics["queued_unexplored"] = len(queue)
    statistics["elapsed_seconds"] = round(perf_counter() - started, 3)
    return dict(statistics=statistics, records=records)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", action="store_true")
    args = parser.parse_args()
    result = run()
    print(json.dumps(result if args.fixtures else result["statistics"], ensure_ascii=False))
