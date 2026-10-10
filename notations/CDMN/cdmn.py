"""Independent immutable CDMN prototype.

A graph is a tuple of columns; a column is a tuple of (parent, row) pairs.
Rows are graphs in the context strictly before their owner. Python's tuple
order is exactly CDMN's recursive lexicographic comparison. The mathematical
rule has no resource cutoff; callers must bound experiments.

This is the prefix-zero revision: [0] deletes the last column at the active
copy layer, and enclosing layers replace only their control row. Positive
indices have not been shifted or otherwise changed.
"""

ZERO = ()
ONE = ((),)


def seed(n):
    if not isinstance(n, int) or n < 0:
        raise ValueError("seed must be a non-negative integer")
    if n == 0:
        return ONE
    row = ONE
    for _ in range(n - 1):
        row = (((0, row),),)
    return ((), ((0, row),))


def relocate(graph, cut, distance):
    return tuple(tuple((p + distance if p >= cut else p,
                        relocate(row, cut, distance))
                       for p, row in column) for column in graph)


def replace_last_row(graph, row):
    column = graph[-1]
    parent = column[-1][0]
    last = column[:-1] + (((parent, row),) if row else ())
    return graph[:-1] + (last,)


def prune(graph):
    """The current zero-index rule, not a one-syntax-column trim."""
    if not graph or not graph[-1]:
        return graph[:-1]
    row = graph[-1][-1][1]
    if row[-1]:
        return replace_last_row(graph, prune(row))
    return graph[:-1]


def fundamental(graph, n, context=ZERO):
    if not isinstance(n, int) or n < 0:
        raise ValueError("index must be a non-negative integer")
    if not graph or not graph[-1]:
        return graph[:-1]
    if n == 0:
        return prune(graph)

    earlier = context + graph[:-1]
    owner = len(earlier)
    parent, row = graph[-1][-1]
    if row[-1]:
        return replace_last_row(graph, fundamental(row, n, earlier))

    distance = owner - parent
    if distance <= 0:
        raise ValueError("parent is not earlier")
    seam = replace_last_row(graph, row[:-1])[-1]
    floor = max((r for _, r in seam), default=ZERO)
    for p, old_row in earlier[parent]:
        new_row = relocate(old_row, parent, distance)
        if new_row > floor:
            seam += ((p, new_row),)
            floor = new_row

    block = (seam,) + relocate(earlier[parent + 1:], parent, distance)
    return graph[:-1] + tuple(column for k in range(n)
                             for column in relocate(block, parent, k * distance))


def legal(graph, base=0):
    for j, column in enumerate(graph):
        previous = base + j
        for parent, row in column:
            if (not isinstance(parent, int) or not 0 <= parent < previous
                    or not row or not legal(row, base + j)):
                return False
            previous = parent
    return True


def from_json(graph):
    return tuple(tuple((e["p"], from_json(e["r"])) for e in col) for col in graph)


if __name__ == "__main__":
    import json
    import sys
    import time

    started = time.monotonic()
    count = 0
    for line in sys.stdin:
        if count >= 7000 or time.monotonic() - started > 30 or len(line) > 2_000_000:
            raise RuntimeError("cross-check budget exhausted")
        case = json.loads(line)
        graph, expected = from_json(case["graph"]), from_json(case["expected"])
        context = from_json(case.get("context", []))
        actual = fundamental(graph, case["n"], context)
        assert actual == expected, (count, case["n"], "FS mismatch")
        assert legal(graph, len(context)) and legal(actual, len(context))
        if graph:
            assert actual < graph
        count += 1
    print(json.dumps({"independent_exact_checks": count,
                      "elapsed_seconds": round(time.monotonic() - started, 3)}))
