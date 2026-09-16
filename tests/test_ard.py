"""Bounded skyline ARD checks: independent Python, legacy projection and NER.

Run from the repository root: python -B tests/test_ard.py
No network, unbounded descent or background process is used.
"""
import importlib.util
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
START = time.monotonic()


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


new = load("skyline_ard_test", "notations/ARD/ard.py")
old = load("legacy_ard_test", "notations/ARD-legacy/ard.py")
A = new.AnchoredRows
L = old.AnchoredRows


def deadline():
    assert time.monotonic() - START < 25, "25-second test deadline"


def projection(column):
    # Independent all-at-once dominance, not the production running-maximum scan.
    unique = set(column)
    kept = [e for e in unique if not any(
        e != f and e[1] <= f[1] and (e[0], e[2]) <= (f[0], f[2]) for f in unique)]
    return tuple(sorted(kept, key=lambda e: (e[1], e[0], e[2]), reverse=True))


def projected(graph):
    return tuple(projection(c) for c in graph.columns)


def output_width(g, n):
    if not g.columns:
        return 0
    if not n or not g.columns[-1]:
        return len(g.columns) - 1
    e = max(g.columns[-1], key=lambda e: (e[0], e[2], e[1]))
    return len(g.columns) - 1 + n * (len(g.columns) - 1 - e[1])


def main():
    seeds = [L.seed(n) for n in range(6)]
    queue, seen = list(seeds), set(seeds)
    for i in range(150):
        if i >= len(queue):
            break
        g = queue[i]
        for n in range(4):
            if output_width(g, n) > 14:
                continue
            h = g[n]
            if h not in seen and len(queue) < 150:
                queue.append(h)
                seen.add(h)
        deadline()
    standard = list(queue)
    rng = random.Random(916634771)
    for _ in range(100):
        cols = []
        for j in range(rng.randrange(1, 8)):
            col = []
            for _ in range(rng.randrange(5) if j else 0):
                p = rng.randrange(j)
                col.append((rng.randrange(p + 1), p, rng.randrange(p + 1)))
            cols.append(col)
        queue.append(L(cols))
    steps, cases = 0, []
    for i, g in enumerate(queue):
        a = A(g.columns)
        assert a.columns == projected(g)
        assert A(a.columns) == a
        for n in range(4):
            if output_width(g, n) > 48:
                continue
            child = a[n]
            assert child.columns == projected(g[n])
            assert child < a if a.columns else child == a
            assert child.columns == a[n + 1].columns[:len(child.columns)]
            steps += 1
        cases.append({"notation": "ard", "id": i, "raw": str(a),
                      "outputs": [str(a[n]) for n in range(4)]})
        deadline()
    comparisons = []
    for i in range(600):
        a, b = rng.choice(standard), rng.choice(standard)
        x, y = A(a.columns), A(b.columns)
        expected = int(a > b) - int(a < b)
        assert expected == int(x > y) - int(x < y)
        comparisons.append({"notation": "ard", "a": str(x), "b": str(y), "expected": expected})
    for bad in [-1, True, 1.5, "1"]:
        try:
            A.seed(bad)
            raise AssertionError("Invalid index accepted")
        except (ValueError, TypeError):
            pass
    try:
        A(((), (), ((1, 0, 0),)))
        raise AssertionError("anchor > parent accepted")
    except ValueError:
        pass
    assert new.TOP[3] == A.seed(3)
    assert A.seed(3)[1].columns == ((), ((0, 0, 0),), ((1, 1, 0),))
    assert new.ZERO[10**100] == new.ZERO
    assert A.finite(1)[10**100] == new.ZERO
    node = shutil.which("node")
    assert node, "Node is required for this cross-language regression"
    result = subprocess.run([node, "--max-old-space-size=256", str(ROOT / "tests/python-reference.cjs")],
                            input=json.dumps({"cases": cases, "comparisons": comparisons}),
                            text=True, encoding="utf-8", capture_output=True, timeout=15)
    assert result.returncode == 0, result.stderr
    deadline()
    print(json.dumps({"status": "passed", "graphs": len(queue), "standardGraphs": len(standard),
                      "projectedExpansions": steps, "standardComparisons": 600,
                      "node": json.loads(result.stdout), "seconds": round(time.monotonic()-START, 3)}))


if __name__ == "__main__":
    main()
