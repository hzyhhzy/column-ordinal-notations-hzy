"""Bounded regression for the threshold-chain invariant in ard-le-ard2-13.

Tests actual ARD2 expansions, not a replacement rule. Budget exclusions and
unprocessed states are unknown; finite success is not a well-ordering proof.
"""
from collections import deque
import json
import random
import time

from ard_ard2_comparison import ARD2, control, safe_forest


def main():
    start = time.perf_counter()
    deadline = start + 25
    rng = random.Random(916260)
    raw = coherent = raw_steps = 0
    unknown = 0
    for _ in range(1200):
        if time.perf_counter() >= deadline:
            unknown += 1200 - raw
            break
        width = rng.randrange(1, 9)
        columns = [()]
        for j in range(1, width):
            columns.append(tuple((rng.randrange(j + 1), rng.randrange(j), rng.randrange(j + 1))
                                 for _ in range(rng.randrange(8))))
        graph = ARD2(tuple(columns))
        raw += 1
        if safe_forest(graph) is None:
            coherent += 1
            for n in range(4):
                output = graph[n]
                assert safe_forest(output) is None, (str(graph), n, str(output))
                raw_steps += 1

    queue = deque(ARD2.seed(n) for n in range(7))
    seen = set(queue)
    checked = steps = 0
    while queue and checked < 3500 and time.perf_counter() < deadline:
        graph = queue.popleft()
        checked += 1
        assert safe_forest(graph) is None, str(graph)
        for n in range(4):
            width = len(graph.columns) - 1
            if graph.columns and graph.columns[-1] and n:
                width += n * (width - control(graph)[1])
            if width > 12:
                unknown += 1
                continue
            output = graph[n]
            assert safe_forest(output) is None, (str(graph), n, str(output))
            steps += 1
            if output not in seen:
                if len(seen) >= 14000:
                    unknown += 1
                else:
                    seen.add(output)
                    queue.append(output)
    print(json.dumps({"result": "bounded_pass", "raw_graphs": raw,
                      "coherent_raw": coherent, "coherent_raw_steps": raw_steps,
                      "standard_states": checked, "standard_steps": steps,
                      "skipped_unknown": unknown, "queued_unknown": len(queue),
                      "seconds": round(time.perf_counter() - start, 3)}, indent=2))


if __name__ == "__main__":
    main()
