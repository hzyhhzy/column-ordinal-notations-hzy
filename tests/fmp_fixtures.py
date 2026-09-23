"""Bounded Python fixtures for tests/fmp_cross_language.cjs.

Run from the repository root:
    python -B tests/fmp_fixtures.py | node --max-old-space-size=512 tests/fmp_cross_language.cjs

No child process, temporary fixture or persistent search is created. Finite
tests are implementation checks, never evidence of global well-ordering.
"""
import json
from pathlib import Path
import random
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notations/FMP"))
from fmp import Pattern, seed
from fmp_tools import compare, counts, display, validate


class BudgetExceeded(Exception):
    pass


def main():
    started = time.monotonic()
    rng = random.Random(2026092307)
    fixtures, skipped = [], 0
    pattern = seed(3)

    def guard(size=0):
        if size > 200 or time.monotonic() - started > 15:
            raise BudgetExceeded()

    def count_guard(work=0):
        if work > 20000 or time.monotonic() - started > 15:
            raise BudgetExceeded()

    for _ in range(1800):
        if len(fixtures) >= 1000 or time.monotonic() - started > 14:
            break
        if not pattern.columns or rng.randrange(45) == 0:
            pattern = seed(rng.randrange(7))
        index = rng.choice((0, 0, 1, 1, 2, 3))
        try:
            child = pattern.expand(index, guard)
            validate(child)
            source_counts = counts(pattern, count_guard)
            child_counts = counts(child, count_guard)
            fixture = {
                "source": display(pattern),
                "index": index,
                "child": display(child),
                "sourceCounts": list(map(str, source_counts)),
                "childCounts": list(map(str, child_counts)),
                "compare": compare(child, pattern, count_guard),
            }
            if index:
                previous = pattern.expand(index - 1, guard)
                assert previous.columns == child.columns[:len(previous.columns)]
                fixture["previous"] = display(previous)
            assert child.columns[:len(pattern.columns) - 1] == pattern.columns[:-1]
            fixtures.append(fixture)
            pattern = child
        except BudgetExceeded:
            skipped += 1
            pattern = seed(rng.randrange(7))
    if len(fixtures) < 100:
        raise RuntimeError("Insufficient completed fixtures; do not report a pass.")
    output = {
        "schema": 1, "randomSeed": 2026092307, "fixtures": fixtures,
        "skipped": skipped, "elapsedSeconds": round(time.monotonic() - started, 3),
        "limits": {"attempts": 1800, "accepted": 1000, "columns": 200,
                   "seconds": 15, "countStates": 20000},
    }
    encoded = json.dumps(output, ensure_ascii=True, separators=(",", ":"))
    if len(encoded) > 32 * 1024 * 1024:
        raise RuntimeError("Fixture serialization exceeds 32 MiB.")
    print(encoded)


if __name__ == "__main__":
    main()
