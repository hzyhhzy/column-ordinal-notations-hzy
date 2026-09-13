"""Bounded ARD checks, including its exact common RPD subtree.

Run: python -B tests/test_ard.py. Optional Node uses NOTATION_NODE or PATH.
No research checkout, host cache, browser, or external package is required.
These finite checks are separate from the published well-ordering proof.
"""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
from time import monotonic

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
STARTED = monotonic()


def deadline():
    if monotonic() - STARTED > 40:
        raise AssertionError("40-second ARD test deadline")


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


ard = load("release_ard", "notations/ARD/ard.py")
rpd = load("release_rpd", "notations/RPD/rpd.py")
Graph, ZERO, TOP = ard.AnchoredRows, ard.ZERO, ard.TOP


def legal(graph):
    for j, column in enumerate(graph.columns):
        assert column == tuple(sorted(column, key=lambda e: (e[1], e[0], e[2]), reverse=True))
        assert len({(k, p) for k, p, q in column}) == len(column)
        for k, p, q in column:
            assert all(type(i) is int for i in (k, p, q))
            assert 0 <= k < j and 0 <= q <= p < j


def width(graph, n):
    if not graph.columns:
        return 0
    x = len(graph.columns) - 1
    if n == 0 or not graph.columns[-1]:
        return x
    _, c, _ = max(graph.columns[-1], key=lambda e: (e[0], e[2], e[1]))
    return x + n * (x - c)


def atomic_step(graph, n):
    """Independent full-root finite union, then maximum-root compression."""
    if not graph.columns or not n or not graph.columns[-1]:
        return graph.columns[:-1]
    x = len(graph.columns) - 1
    k, c, r = max(graph.columns[-1], key=lambda e: (e[0], e[2], e[1]))
    length = x - c
    atoms = [[(h, p, t) for h, p, q in col for t in range(q + 1)]
             for col in graph.columns]
    out = [set() for _ in range(x + n * length)]
    for b in range(n + 1):
        def shift(i):
            return i if i < c else i + b * length
        for j in range(x):
            for h, p, t in atoms[j]:
                out[shift(j)].update((shift(h), shift(p), u) for u in range(shift(t) + 1))
        if b < n:
            for h, p, t in atoms[-1]:
                out[x + b * length].update(
                    (shift(h), shift(p), u) for u in range(shift(t) + 1)
                    if h < k or h == k and u < shift(r))
            out[x + b * length].update(
                (h, shift(c), u) for h in range(shift(k)) for u in range(shift(c) + 1))
    answer = []
    for col in out:
        maxima = {}
        for h, p, q in col:
            maxima[h, p] = max(q, maxima.get((h, p), -1))
        answer.append(tuple(sorted(((h, p, q) for (h, p), q in maxima.items()),
                                   key=lambda e: (e[1], e[0], e[2]), reverse=True)))
    return tuple(answer)


def local_counts(graph):
    """Literal local rewrites; no optimized pair profiles or threshold traces."""
    answer = []
    for j in range(len(graph.columns)):
        current = Graph(graph.columns[:j + 1])
        count = 1  # Includes the final deletion of an empty column.
        while current.columns[-1]:
            assert count < 20000, "bounded local-count reference"
            current = Graph(current[1].columns[:j + 1])
            count += 1
            deadline()
        answer.append(str(count))
    return answer


def main():
    seeds = [Graph.seed(n) for n in range(7)]
    for n, g in enumerate(seeds):
        assert g.columns == tuple(() if j == 0 else ((j - 1, j - 1, j - 1),) for j in range(n))
        assert TOP[n] == g and (not n or g[0] == seeds[n - 1])
        legal(g)
    assert ZERO == Graph() and str(TOP) == "Limit of ARD"
    for n in range(8):
        assert Graph.finite(n)[10**100] == Graph.finite(max(0, n - 1))
    malformed = [(((0, 0, 0),),), ((), ((1, 0, 0),)), ((), ((0, 1, 0),)),
                 ((), ((0, 0, 1),)), ((), ((-1, 0, 0),)), ((), ((True, 0, 0),)),
                 ((), ((0, 0.0, 0),)), ((), ((0, 0, False),))]
    for value in malformed:
        try:
            Graph(value)
        except (ValueError, TypeError):
            pass
        else:
            raise AssertionError("invalid coordinates accepted")
    for index in [-1, True, 1.0, "1", None]:
        try:
            TOP[index]
        except (ValueError, TypeError):
            pass
        else:
            raise AssertionError("invalid index accepted")
    after_parent = Graph(((), (), ((1, 0, 0),)))  # row > parent is permitted.
    assert after_parent < Graph(((), (), ((0, 1, 0),)))
    merged = Graph([[], [], [(1, 1, 0), (1, 1, 1), (1, 1, 1)]])
    assert merged == Graph([[], [], [(1, 1, 1)]])
    samples = list(dict.fromkeys(seeds + [after_parent, merged]))
    seen = set(samples)
    cursor = 0
    while cursor < len(samples) and len(samples) < 70:
        g = samples[cursor]
        cursor += 1
        for n in range(4):
            h = g[n]
            if h not in seen and width(h, 3) <= 64:
                samples.append(h)
                seen.add(h)
                if len(samples) == 70:
                    break
        deadline()
    rng = random.Random(13234)
    while len(samples) < 120:
        columns = []
        for j in range(rng.randrange(2, 9)):
            col = []
            if j:
                for _ in range(rng.randrange(5)):
                    p = rng.randrange(j)
                    col.append((rng.randrange(j), p, rng.randrange(p + 1)))
            columns.append(col)
        g = Graph(columns)
        if g not in seen:
            samples.append(g)
            seen.add(g)
        deadline()
    cases, comparisons = [], []
    for i, g in enumerate(samples):
        previous = None
        outputs = []
        for n in range(4):
            h = g[n]
            legal(h)
            assert len(h.columns) == width(g, n) <= 64
            assert h.columns == atomic_step(g, n)
            assert h < g if g.columns else h == ZERO
            if previous is not None:
                assert h.columns[:len(previous.columns)] == previous.columns
            previous = h
            outputs.append(str(h))
        cases.append({"notation": "ard", "id": i, "raw": str(g), "outputs": outputs})
        deadline()
    for i, g in enumerate(samples):
        for h in (g, samples[(i * 37 + 11) % len(samples)]):
            comparisons.append({"notation": "ard", "a": str(g), "b": str(h),
                                "expected": int(g > h) - int(g < h)})
    ordered = sorted(samples)
    for g, h in zip(ordered, ordered[1:]):
        assert g < h
        comparisons.append({"notation": "ard", "a": str(g), "b": str(h), "expected": -1})

    # T itself is an ARD boundary, not an asserted RPD standard term. Its
    # children coincide with shifted-index children of the RPD seed S_0.
    T = Graph(((), (), ((0, 1, 1),)))
    assert Graph.seed(2)[2][1] == T
    family = []
    for n in range(9):
        expected = Graph(((), ()) + tuple(((0, j - 1, j - 2),) for j in range(2, n + 2)))
        assert T[n] == expected == Graph(rpd.RPD.seed(0)[n + 1].columns)
        family.append(expected)
    common, common_seen = list(family), set(family)
    cursor = common_steps = 0
    while cursor < len(common) and cursor < 48:
        g = common[cursor]
        cursor += 1
        assert all(k == 0 and p >= 1 for col in g.columns for k, p, q in col)
        old = rpd.RPD(g.columns)
        for n in range(4):
            child = g[n]
            assert child == Graph(old[n].columns)
            common_steps += 1
            if child not in common_seen and width(child, 3) <= 64 and len(common) < 48:
                common.append(child)
                common_seen.add(child)
        for name, value in (("ard", g), ("rpd", old)):
            cases.append({"notation": name, "id": "common-" + str(cursor), "raw": str(value),
                          "outputs": [str(value[n]) for n in range(4)]})
        deadline()
    for g, h in zip(common, reversed(common)):
        expected = int(g > h) - int(g < h)
        a, b = rpd.RPD(g.columns), rpd.RPD(h.columns)
        assert expected == int(a > b) - int(a < b)
        for name, left, right in (("ard", g, h), ("rpd", a, b)):
            comparisons.append({"notation": name, "a": str(left), "b": str(right), "expected": expected})
    counts = [{"notation": "ard", "raw": str(g), "expected": local_counts(g)}
              for g in seeds[:6] + [after_parent, merged]]
    for n, g in enumerate(family):
        expected = ["1", "1"] + [str(2**(j - 1)) for j in range(2, n + 2)]
        assert local_counts(g) == expected
        counts.append({"notation": "ard", "raw": str(g), "expected": expected})
    node = os.environ.get("NOTATION_NODE") or shutil.which("node")
    summary = {"status": "passed", "graphs": len(samples), "atomicExpansions": 4*len(samples),
               "seedCases": len(seeds), "invalidGraphs": len(malformed),
               "boundaryCases": len(family), "commonGraphs": len(common), "commonSteps": common_steps,
               "localCountCases": len(counts), "node": "unavailable (optional checks skipped)"}
    if node:
        data = json.dumps({"cases": cases, "comparisons": comparisons, "counts": counts}, ensure_ascii=False)
        assert len(data) < 4000000
        result = subprocess.run([node, "--max-old-space-size=256", str(ROOT / "tests/python-reference.cjs")],
                                input=data, text=True, encoding="utf-8", capture_output=True, timeout=20)
        assert result.returncode == 0, result.stderr
        summary["node"] = json.loads(result.stdout)
        assert summary["node"]["expansions"] == 4*len(cases)
        assert summary["node"]["countChecks"] == len(counts)
        result = subprocess.run([node, "--max-old-space-size=192", str(ROOT / "tests/ard_arcs.cjs")],
                                text=True, encoding="utf-8", capture_output=True, timeout=20)
        assert result.returncode == 0, result.stderr
        summary["geometry"] = json.loads(result.stdout)
    deadline()
    summary["seconds"] = round(monotonic() - STARTED, 3)
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()
