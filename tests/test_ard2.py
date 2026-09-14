"""Bounded ARD2 checks against an independent, fully root-closed oracle.

Run python -B tests/test_ard2.py. --vectors emits Python-checked vectors for
ard2_ner.cjs. One process; no subprocesses, network or file writes.
45 seconds, at most 64 output columns and 100,000 root atoms per expansion.
These finite tests do not prove global well-ordering or compare with IPD.
"""

import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import sys
from time import monotonic

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
START = monotonic()
TICKS = 0
spec = importlib.util.spec_from_file_location("release_ard2", ROOT / "notations/ARD2/ard2.py")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
Graph, ZERO, TOP = module.ARD2, module.ZERO, module.TOP


def peak_rss_mib():
    """Read this process only; report an actual RSS high-water mark."""
    if sys.platform == "win32":
        import ctypes
        from ctypes import wintypes
        class Counters(ctypes.Structure):
            _fields_ = [("cb", wintypes.DWORD), ("faults", wintypes.DWORD)] + [
                (name, ctypes.c_size_t) for name in (
                    "peak", "working", "peak_paged", "paged", "peak_nonpaged",
                    "nonpaged", "pagefile", "peak_pagefile")]
        data = Counters()
        data.cb = ctypes.sizeof(data)
        get_info = ctypes.windll.psapi.GetProcessMemoryInfo
        get_info.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
        get_info.restype = wintypes.BOOL
        if not get_info(wintypes.HANDLE(-1), ctypes.byref(data), data.cb):
            raise OSError("Cannot read the current process memory counter")
        return data.peak / 1048576
    import resource
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak / (1048576 if sys.platform == "darwin" else 1024)


def tick():
    global TICKS
    TICKS += 1
    assert monotonic() - START < 45, "45-second test deadline"
    if TICKS % 1024 == 0:
        assert peak_rss_mib() < 512, "512 MiB peak RSS ceiling"


def normalize(columns):
    answer = []
    for col in columns:
        groups = {}
        for k, p, q in col:
            groups[k, p] = max(q, groups.get((k, p), -1))
        answer.append(tuple(sorted(((k, p, q) for (k, p), q in groups.items()),
                                   key=lambda e: (e[1], e[0], e[2]), reverse=True)))
    return tuple(answer)


def atomic_step(columns, n):
    """Full root atoms, finite unions and reclosure; no compressed FS import."""
    tick()
    if not columns or not n or not columns[-1]:
        return columns[:-1]
    last = len(columns) - 1
    atoms = {(k, q, p, j) for j, col in enumerate(columns)
             for k, p, root in col for q in range(root + 1)}
    row, root, cut, _ = max(e for e in atoms if e[3] == last)
    width = last - cut
    assert last + n * width <= 64
    out = set()
    for block in range(n + 1):
        def move(i):
            return i if i < cut else i + block * width
        for k, q, p, j in atoms:
            if j < last:
                out.update((move(k), u, move(p), move(j)) for u in range(move(q) + 1))
            elif block < n:
                out.update((move(k), u, move(p), move(last)) for u in range(move(q) + 1)
                           if k < row or k == row and u < move(root))
        if block < n:
            out.update((h, u, move(cut), move(last))
                       for h in range(move(row)) for u in range(move(last) + 1))
        assert len(out) <= 100000, "root-atom bound"
    result = [[] for _ in range(last + n * width)]
    for k, q, p, j in out:
        result[j].append((k, p, q))
    return normalize(result)


def count_columns(graph, fuel=30000):
    """Literal positive atomic expansion, keep old width; no count shortcut."""
    values = []
    for width in range(1, len(graph.columns) + 1):
        current = graph.columns[:width]
        for count in range(fuel):
            tick()
            if len(current) < width:
                values.append(str(count))
                break
            current = atomic_step(current, 1)[:width]
        else:
            raise AssertionError("bounded local-count oracle exhausted")
    return values


def small_columns(j):
    pairs = [(k, p) for k in range(j + 1) for p in range(j)]
    for roots in product(range(-1, j + 1), repeat=len(pairs)):
        yield tuple((k, p, q) for (k, p), q in zip(pairs, roots) if q >= 0)


def main():
    seeds = [Graph.seed(n) for n in range(9)]
    for n, graph in enumerate(seeds):
        assert TOP[n] == graph
        assert graph.columns == tuple(() if j == 0 else ((j, j - 1, j),) for j in range(n))
        if n:
            assert graph[0] == seeds[n - 1]
    assert str(TOP) == "Limit of ARD2" and ZERO.kind == "zero"
    assert Graph.finite(1).kind == "successor" and seeds[2].kind == "limit"
    for n in range(9):
        assert Graph.finite(n)[10**100] == Graph.finite(max(0, n - 1))
    invalid = [(((0, 0, 0),),), ((), ((2, 0, 0),)), ((), ((0, 1, 0),)),
               ((), ((0, 0, 2),)), ((), ((-1, 0, 0),)), ((), ((0, -1, 0),)),
               ((), ((True, 0, 0),)), ((), ((0, 0.0, 0),)), ((), ((0, 0, False),))]
    for columns in invalid:
        try:
            Graph(columns)
        except (TypeError, ValueError):
            pass
        else:
            raise AssertionError("invalid graph accepted")
    for n in (-1, True, 1.0, "1", None):
        for construct in (TOP.fs, Graph.seed, Graph.finite):
            try:
                construct(n)
            except (TypeError, ValueError):
                pass
            else:
                raise AssertionError("invalid index accepted")
    assert Graph([[], [(1, 0, 0), (1, 0, 1)]]) == seeds[2]
    # Both SELF coordinates in C_cut must rebind at the first seam.
    expected = ((), ((1, 0, 1),), ((2, 1, 1), (1, 1, 2), (0, 1, 2), (2, 0, 2)))
    assert seeds[3].local_step().columns == expected

    samples = list(seeds)
    rng = random.Random(9142301)
    for _ in range(160):
        columns = []
        for j in range(rng.randrange(2, 9)):
            columns.append([(rng.randrange(j + 1), rng.randrange(j), rng.randrange(j + 1))
                            for _ in range(rng.randrange(2 * j + 1))])
        samples.append(Graph(columns))
    # Enumerate all canonical legal graphs of widths 0,1,2,3, streamed in memory.
    exhaustive = (Graph(columns) for width in range(4)
                  for columns in product(*(small_columns(j) for j in range(width))))
    checked = expansions = 0
    def verify(graph, indices):
        nonlocal checked, expansions
        outputs = []
        for n in indices:
            value = graph[n]
            assert value.columns == atomic_step(graph.columns, n)
            assert value.columns[:max(0, len(graph.columns) - 1)] == graph.columns[:-1]
            assert value < graph if graph.columns else value == ZERO
            if outputs:
                old = outputs[-1].columns
                assert value.columns[:len(old)] == old
            outputs.append(value)
            expansions += 1
        assert graph.local_step().columns == outputs[1].columns[:len(graph.columns)]
        checked += 1
        return outputs
    for graph in exhaustive:
        verify(graph, range(3))
    cases = []
    for graph in samples:
        outputs = verify(graph, range(4))
        cases.append({"raw": str(graph), "outputs": [str(value) for value in outputs]})
    comparisons = [{"a": str(a), "b": str(b), "expected": int(a > b) - int(a < b)}
                   for a, b in zip(samples, reversed(samples))]
    count_cases = [{"raw": str(g), "expected": count_columns(g)} for g in seeds[:6]]
    assert count_cases[-1]["expected"] == ["1", "5", "55", "969", "23751"]
    summary = {"ok": True, "graphs": checked, "atomicExpansions": expansions,
               "invalidGraphs": len(invalid), "localCountCases": len(count_cases),
               "peakRssMiB": round(peak_rss_mib(), 2),
               "seconds": round(monotonic() - START, 3),
               "limits": {"seconds": 45, "columns": 64, "atoms": 100000,
                          "localSteps": 30000, "processes": 1, "rssMiB": 512}}
    if "--vectors" in sys.argv:
        print(json.dumps({"summary": summary, "cases": cases, "comparisons": comparisons,
                          "counts": count_cases}))
    else:
        print(json.dumps(summary))


if __name__ == "__main__":
    main()
