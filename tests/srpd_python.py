"""Consume bounded JS vectors and compare with the independent Python kernel."""
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notations/SRPD"))
from srpd import INITIAL, counts, expand, valid

started = time.monotonic()
assert counts(INITIAL) == [2]
assert expand(INITIAL, 0) == []
assert expand(INITIAL, 3) == [[], [1], [2, 2]]
assert counts(expand(INITIAL, 4)) == [1, 2, 4, 8]
for invalid in (-1, True, 1.5):
    try:
        expand(INITIAL, invalid)
    except ValueError:
        pass
    else:
        raise AssertionError("Non-integer/negative index accepted")
raw = sys.stdin.read(2_000_001)
assert len(raw) <= 2_000_000, "input size guard"
cases = json.loads(raw)
assert 0 < len(cases) <= 150
states = steps = 0
for case in cases:
    assert time.monotonic() - started < 45, "Python comparison time guard"
    graph = case["graph"]
    assert len(graph) <= 27 and valid(graph)
    assert list(map(str, counts(graph))) == case["counts"]
    states += 1
    for child in case["children"]:
        assert 0 <= child["n"] <= 4
        result = expand(graph, child["n"])
        assert valid(result) and result == child["graph"]
        steps += 1
print(json.dumps({"states": states, "steps": steps, "unit_checks": "passed",
                  "elapsed_seconds": time.monotonic() - started}))
