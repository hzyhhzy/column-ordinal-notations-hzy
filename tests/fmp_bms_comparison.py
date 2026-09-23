"""Bounded audit of the paper BMS -> FMP(12242444) construction.

Run from the repository root: python -B tests/fmp_bms_comparison.py
This is a regression test, not the all-parameter embedding proof.
The small numerical BMS reference below implements the definition directly;
it does not import a private workspace or any external BMS source file.
"""

import json
from pathlib import Path
import random
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations/FMP'))
from fmp import Column, Pattern, copy_tail, seed
from fmp_tools import counts, parse, validate


def parents(matrix):
    """BMS parents: search the preceding row's ancestor chain."""
    table = []
    for x, column in enumerate(matrix):
        row_parents = []
        for q, value in enumerate(column):
            candidate = x - 1 if q == 0 else row_parents[q - 1]
            while candidate >= 0 and matrix[candidate][q] >= value:
                candidate = candidate - 1 if q == 0 else table[candidate][q - 1]
            row_parents.append(candidate)
        table.append(tuple(row_parents))
    return tuple(table)


def bms_step(matrix, n):
    """Short BMS fundamental sequence, retaining the fixed zero-padded height."""
    if not matrix:
        return matrix
    if not n or not any(matrix[-1]):
        return matrix[:-1]
    table = parents(matrix)
    row = max(q for q, value in enumerate(matrix[-1]) if value)
    root = table[-1][row]
    assert root >= 0
    delta = [matrix[-1][q] - matrix[root][q] if q < row else 0
             for q in range(len(matrix[-1]))]
    increments = []
    for x in range(root, len(matrix) - 1):
        column = []
        for q, change in enumerate(delta):
            ancestor = x
            while ancestor > root:
                ancestor = table[ancestor][q]
            column.append(change if ancestor == root else 0)
        increments.append(column)
    result = list(matrix[:-1])
    for copy in range(1, n + 1):
        for x, increment in zip(range(root, len(matrix) - 1), increments):
            result.append(tuple(value + copy * d for value, d in zip(matrix[x], increment)))
    return tuple(result)


def port(q, u, v):
    return Column(tuple((u + i, v + i) for i in range(q + 2)),
                  frozenset(range(v, v + q)))


def raw_block(j):
    u, c, b = 5 * j, 5 * j + 3, 5 * j + 5
    return (
        port(0, u, c),
        Column(((u, c), (u + 1, c + 1), (c, c + 2)), frozenset((c,))),
        port(0, u, b),
        Column(((u, b), (u + 1, b + 1), (c, b + 2)), frozenset((b,))),
        Column(((u, b), (u + 1, b + 1), (c, b + 2), (c + 1, b + 3)),
               frozenset((b, b + 1))),
    )


def truncate(pattern, length):
    """A checked finite sequence of actual [0] operations."""
    assert 0 <= length <= len(pattern.columns)
    while len(pattern.columns) > length:
        pattern = pattern[0]
    return pattern


def verify(state):
    graph, matrix, bases, height, spacing, floor = state
    validate(graph)
    assert len(matrix) == len(bases)
    assert len(graph.columns) == (bases[-1] + height - 1 if bases else floor)
    assert bases == tuple(floor + 1 + spacing * j for j in range(len(matrix)))
    assert spacing >= height + 1
    for column in graph.columns[floor:]:
        if column.edges:
            assert column.edges[-1][0] == column.pivot + 1
            assert column.edges[-1][0] not in bases
    table = parents(matrix)
    for j, base in enumerate(bases):
        for q in range(height):
            column = graph.columns[base + q - 1]
            u = column.minimum
            assert column.edges == tuple((u + i, base + i) for i in range(q + 2))
            parent = table[j][q]
            assert u == bases[parent] if parent >= 0 else u + height < bases[0]
            # Independently recover numerical entries as parent-chain depths.
            depth, ancestor = 0, j
            while table[ancestor][q] >= 0:
                ancestor = table[ancestor][q]
                depth += 1
            assert matrix[j][q] == depth


def advance(state, n, guard):
    graph, matrix, bases, height, spacing, floor = state
    assert matrix
    if not n or not any(matrix[-1]):
        new_bases = bases[:-1]
        length = new_bases[-1] + height - 1 if new_bases else floor
        child = truncate(graph, length)
    else:
        row = max(q for q, value in enumerate(matrix[-1]) if value)
        parent = parents(matrix)[-1][row]
        distance = bases[-1] - bases[parent]
        controller = truncate(graph, bases[-1] + row)
        child = controller.expand(n, guard)
        raw = controller
        for _ in range(n):
            raw = copy_tail(raw)
        assert child == raw[0], 'completion must be inactive in the band sector'
        new_bases = bases[:-1] + tuple(
            bases[j] + t * distance for t in range(1, n + 1)
            for j in range(parent, len(bases) - 1))
        child = truncate(child, new_bases[-1] + height - 1)
    new_matrix = bms_step(matrix, n)
    assert new_matrix < matrix
    assert child.columns[:floor] == graph.columns[:floor]
    result = child, new_matrix, new_bases, height, spacing, floor
    verify(result)
    return result


def main():
    start = time.monotonic()
    deadline = start + 20

    def guard(width=0):
        if time.monotonic() > deadline:
            raise TimeoutError('20-second audit deadline')
        if width > 1600:
            raise ValueError('1600-column audit bound')

    h = parse('[][1][1][1:3*;2][1][1:5*;2][1:5*,2:6*;3][1:5*,2:6*;3]')
    reached = seed(1)[0][1][2]
    for _ in range(4):
        reached = truncate(reached.expand(1, guard), 8)
    assert reached == h
    assert counts(h) == (1, 2, 2, 4, 2, 4, 4, 4)

    expected = list(h.columns[:-1])
    raw_expected = list(expected)
    raw = h
    anchors, rows = [], {}
    directed, peak = 0, 8
    for m in range(1, 13):
        guard()
        raw = copy_tail(raw)
        raw_expected.extend(raw_block(m))
        assert raw[0] == Pattern(tuple(raw_expected))
        g, u = m + 2, m * m + 3 * m + 1
        previous = Pattern(tuple(expected))
        expected.extend(port(q, u, u + g) for q in range(g))
        expected.extend(port(q, u, u + 2 * g) for q in range(g + 1))
        body = h.expand(m, guard)
        assert body == Pattern(tuple(expected))
        assert len(body.columns) == m * m + 6 * m + 7
        child = body[0].expand(1, guard)
        height, spacing, base = g - 1, 2 * g, u + 2 * g
        old_source = 1 if m == 1 else (m - 1) ** 2 + 3 * (m - 1) + 1
        prepared_suffix = (
            tuple(port(q, u, base) for q in range(g - 1))
            + (port(g - 1, old_source, base),)
            + tuple(port(q, base, base + g) for q in range(g))
            + tuple(port(q, base, base + 2 * g) for q in range(g - 1)))
        assert child.columns == body.columns[:base - 1] + prepared_suffix
        state = child, ((0,) * height, (1,) * height), (base, base + spacing), height, spacing, base - 1
        verify(state)
        assert child.columns[:len(previous.columns)] == previous.columns
        assert base - 1 > len(previous.columns)
        anchors.append(state)
        peak = max(peak, len(child.columns))
        for row in range(height - 1, -1, -1):
            assert row == max(q for q, value in enumerate(state[1][-1]) if value)
            state = advance(state, 1, guard)
            rows[row] = rows.get(row, 0) + 1
            directed += 1
        for _ in range(2):
            state = advance(state, 0, guard)
            directed += 1
        assert not state[1]

    rng = random.Random(23923329)
    pool = list(anchors)
    random_checked = width_skips = attempts = empty_skips = 0
    for _ in range(2000):
        if time.monotonic() > deadline - 1:
            break
        attempts += 1
        state = rng.choice(pool)
        if not state[1]:
            empty_skips += 1
            continue
        n = rng.choice((0, 1, 1, 2, 3))
        if (n + 1) * len(state[0].columns) > 1600:
            width_skips += 1
            continue
        child = advance(state, n, guard)
        random_checked += 1
        peak = max(peak, len(child[0].columns))
        pool.append(child)
        if len(pool) > len(anchors) + 100:
            del pool[rng.randrange(len(anchors), len(pool))]
    assert random_checked >= 100
    print(json.dumps(dict(suite='BMS -> original FMP(12242444)',
                         formula_parameters=12, directed_macros=directed,
                         directed_rows=rows, random_macros=random_checked,
                         attempts=attempts, width_skips=width_skips,
                         empty_skips=empty_skips, peak_columns=peak,
                         retained_states=len(pool),
                         seconds=round(time.monotonic() - start, 3))))


if __name__ == '__main__':
    main()
