"""Bounded, independent full-tree vectors for the standalone NER adapter.

Reference lower() generates all child candidates; JS uses shared nodes and
exact pruning. Counts below run only the fixed-prefix local operation.
"""

import json
import random
import time

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'IPD'))
import ipd


class Bound(Exception):
    pass


started = time.perf_counter()
deadline = started + 20
case_end = deadline
fuel = 0


def tick():
    global fuel
    fuel += 1
    now = time.perf_counter()
    if fuel > 120000 or now > case_end or now > deadline:
        raise Bound("bounded parity oracle")


def reset(seconds=0.045):
    global fuel, case_end
    fuel = 0
    case_end = time.perf_counter() + seconds


original_compare = ipd.compare


def checked_compare(level, a, b):
    tick()
    return original_compare(level, a, b)


def tree(rng, level, parent, child, depth=2):
    if level == 0:
        return rng.choice((*range(parent + 1), child))
    if not depth or rng.randrange(4) == 0:
        return ipd.ZERO
    head = ipd.CAP if rng.randrange(3) == 0 else tree(rng, level - 1, parent, child, depth - 1)
    return ipd.node(head, (tree(rng, level, parent, child, depth - 1) for _ in range(rng.randrange(4))))


def small(graph):
    if len(graph.columns) > 48:
        return False
    stack = [(d, t) for col in graph.columns for _, (d, t) in col]
    weight = 0
    while stack:
        tick()
        level, term = stack.pop()
        weight += 1
        if weight > 18000:
            return False
        if level and term != ipd.ZERO:
            head, children = term
            if head != ipd.CAP:
                stack.append((level - 1, head))
            stack.extend((level, c) for c in children)
    return True


def main():
    rng = random.Random(2026091420)
    records, graphs, count_records = [], [], []
    stats = {"expansionSkipped": 0, "countSkipped": 0, "oracleSteps": 0}
    ipd.compare = checked_compare
    candidates = [(ipd.IPD(), True), (ipd.IPD(((),)), True)]
    candidates += [(ipd.IPD.seed(n), True) for n in range(8)]
    try:
        for _ in range(130):
            reset()
            cols = []
            for child in range(rng.randrange(1, 6)):
                column = []
                for parent in range(child):
                    if rng.random() < 0.5:
                        level = rng.randrange(5)
                        column.append((parent, (level, tree(rng, level, parent, child))))
                cols.append(column)
            candidates.append((ipd.IPD(cols), False))
        for _ in range(25):
            graph = ipd.IPD.seed(rng.randrange(6))
            for _ in range(5):
                reset()
                try:
                    graph = graph.fs(rng.randrange(1, 4), tick)
                    if len(graph.columns) > 12 or not small(graph):
                        break
                    candidates.append((graph, True))
                except (Bound, RecursionError):
                    break
        for graph, standard in candidates:
            reset()
            try:
                outputs = [graph.fs(n, tick) for n in range(4)]
                if not all(small(out) for out in outputs):
                    raise Bound("oracle flat output size")
                records.append({"text": str(graph), "cols": graph.columns,
                                "outputs": [g.columns for g in outputs], "standard": standard})
                graphs.append(graph)
            except (Bound, RecursionError):
                stats["expansionSkipped"] += 1
                continue
            reset(seconds=0.05)
            values = []
            try:
                for child in range(len(graph.columns)):
                    local = ipd.IPD(graph.columns[:child+1])
                    value = 0
                    while len(local.columns) > child:
                        tick()
                        if value >= 3000:
                            raise Bound("local count steps")
                        local = local.local_step(tick)
                        value += 1
                        stats["oracleSteps"] += 1
                    values.append(str(value))
                count_records.append({"text": str(graph), "values": values})
            except (Bound, RecursionError):
                stats["countSkipped"] += 1
        comparisons = []
        reset(seconds=1)
        for _ in range(500):
            a, b = rng.randrange(len(graphs)), rng.randrange(len(graphs))
            comparisons.append([a, b, (graphs[a] > graphs[b]) - (graphs[a] < graphs[b])])
    finally:
        ipd.compare = original_compare
        original_compare.cache_clear()
    stats["seconds"] = round(time.perf_counter() - started, 3)
    print(json.dumps({"records": records, "comparisons": comparisons, "countRecords": count_records,
                      "stats": stats}, separators=(",", ":")))


if __name__ == "__main__":
    main()
