"""SRPD (formerly RPD0): the zero layer of RPD, written as lists of parents.

Column 0 is an implicit empty root; visible column numbers start at 1.
In a column of length h, entries are nonincreasing and h-1 <= parent < child.
The fixed initial term is [[0]]. No visible columns means zero.
There is no external top or special seed expansion rule. Only descendants of
INITIAL are standard. Python integers are exact; callers control resource use.
"""

INITIAL = [[0]]


def expand(graph, n):
    """Default FS: one rule for all finite graphs, including INITIAL."""
    if type(n) is not int or n < 0:
        raise ValueError("Expected a nonnegative integer")
    if not graph or not n or not graph[-1]:
        return graph[:-1]
    result = graph.copy()
    for _ in range(n):
        column = result[-1]
        parent = column[-1]
        span = len(result) - parent
        source = result[parent - 1] if parent else []

        def move(source):
            moved = [p + span if p >= parent else p for p in source]
            return moved[:parent] + moved[parent:parent + 1] * span + moved[parent:]

        copies = [move(column) for column in result[parent:]]
        result[-1] = column[:-1] + source[len(column) - 1:]
        result.extend(copies)
    return result[:-1]


def counts(graph):
    """Exact fixed-prefix local counts; no long descending chain is enumerated."""
    tables = [[0]]  # The implicit root has zero local-lowering steps.
    for column in graph:
        table = [0] * (len(column) + 1)
        for t in range(len(column) - 1, -1, -1):
            prior = tables[column[t]]
            table[t] = table[t + 1] + 1 + (prior[t] if t < len(prior) else 0)
        tables.append(table)
    return [table[0] + 1 for table in tables[1:]]


def valid(graph):
    """Check raw legality, not membership in the standard initial-term cone."""
    return isinstance(graph, list) and all(
        isinstance(column, list)
        and all(type(p) is int and len(column) - 1 <= p < j for p in column)
        and all(a >= b for a, b in zip(column, column[1:]))
        for j, column in enumerate(graph, 1)
    )


def display(graph):
    return "".join("[" + ",".join(map(str, column)) + "]" for column in graph) or "0"


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="SRPD: expand [0], with an implicit empty root")
    parser.add_argument("indices", nargs="*", type=int)
    graph = INITIAL
    for index in parser.parse_args().indices:
        graph = expand(graph, index)
    print(display(graph))
    print(",".join(map(str, counts(graph))) or "0")
