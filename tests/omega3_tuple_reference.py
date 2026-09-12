"""Bounded checks for the one-column self-indexed LRD proposal.

Run from the repository root: python -B tests/omega3_tuple_reference.py
This is a diagnostic reference, not a NER implementation or a proof.
Internal triples are (parent, row_graph, maximum_root), so Python's recursive
tuple ordering agrees exactly with the prescribed column comparison.
"""

from functools import lru_cache
from time import monotonic
import json


ZERO = ()
WIDTH = 96
CALLS = 100_000
START = monotonic()
calls = 0


def tick():
    global calls
    calls += 1
    if calls > CALLS or monotonic() - START > 10:
        raise RuntimeError("bounded audit exhausted; no truncated term returned")


def normalize(columns):
    tick()
    if len(columns) > WIDTH:
        raise RuntimeError("bounded audit width exceeded")
    result = []
    for j, column in enumerate(columns):
        merged = {}
        for p, k, q in column:
            assert 0 <= q <= p < j
            merged[p, k] = max(q, merged.get((p, k), -1))
        result.append(tuple(sorted(((p, k, q) for (p, k), q in merged.items()),
                                   reverse=True)))
    return tuple(result)


def start_term(n):
    assert type(n) is int and 0 <= n <= 6
    g = ZERO
    for _ in range(n):
        m = len(g)
        g = g + (((m - 1, g, m - 1),),) if m else ((),)
    return g


@lru_cache(maxsize=2048)
def step(g, n):
    tick()
    assert type(n) is int and 0 <= n <= 3
    if not g:
        return g
    if n == 0 or not g[-1]:
        return g[:-1]
    c, k, r = max(g[-1], key=lambda e: (e[1], e[2], e[0]))
    x = len(g) - 1
    block = x - c
    if x + n * block > WIDTH:
        raise RuntimeError("bounded audit width exceeded")
    columns = [[] for _ in range(x + n * block)]
    for b in range(n + 1):
        def move(i):
            return i if i < c else i + b * block

        for j, column in enumerate(g[:-1]):
            columns[move(j)].extend((move(p), h, move(q)) for p, h, q in column)
        if b == n:
            break
        seam = columns[x + b * block]
        for p, h, q in g[-1]:
            allowed = move(q) if h < k else min(move(q), move(r) - 1)
            if h <= k and allowed >= 0:
                seam.append((move(p), h, allowed))
        if any(k):
            packet = {ZERO} | {step(k, t) for t in range(b + 1)}
            assert all(h < k for h in packet)
            seam.extend((move(c), h, move(c)) for h in packet)
    return normalize(columns)


def depth(g):
    return max((1 + depth(k) for column in g for _, k, _ in column), default=0)


def main():
    starts = [start_term(n) for n in range(7)]
    for n, g in enumerate(starts):
        assert len(g) == n
        assert normalize(g) == g
        assert depth(g) == max(0, n - 1)
        if n:
            assert not g[0] and all(g[j] for j in range(1, n))
            assert step(g, 0) == starts[n - 1]
    # Fixed bounded sample: four initial terms, then three rounds of n=0,1,2.
    states = set(starts[:5])
    frontier = set(states)
    for _ in range(3):
        newer = {step(g, n) for g in frontier for n in range(3)} - states
        states.update(newer)
        frontier = newer
        assert len(states) <= 256
    comparisons = prefixes = 0
    for g in states:
        values = [step(g, n) for n in range(4)]
        assert values[0] == g[:-1]
        for a in values:
            assert a < g or g == ZERO
            assert depth(a) <= depth(g)
            comparisons += 1
        for a, b in zip(values, values[1:]):
            assert b[:len(a)] == a
            assert (a < b) if g and g[-1] else (a == b)
            prefixes += 1
    print(json.dumps({"status": "passed", "initial_terms": len(starts),
                      "states": len(states), "descent_checks": comparisons,
                      "prefix_checks": prefixes, "recursive_calls": calls,
                      "seconds": round(monotonic() - START, 4),
                      "scope": "bounded definition checks, not a well-order proof"}))


if __name__ == "__main__":
    main()
