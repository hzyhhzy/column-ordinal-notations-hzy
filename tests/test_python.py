"""Bounded standard-library tests; optional JS comparison needs Node.js.

Run: python -B tests/test_python.py
Set NOTATION_NODE to a Node executable if it is not available on PATH.
The notation modules themselves do not need Node or this test bridge.
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
import time
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
STARTED = time.monotonic()


def deadline():
    if time.monotonic() - STARTED > 30:
        raise AssertionError("30-second test deadline")


def load(name, relative):
    spec = importlib.util.spec_from_file_location("notation_test_" + name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


MODULES = {
    "rpd": load("rpd", "notations/RPD/rpd.py"),
    "lrd": load("lrd", "notations/LRD/lrd.py"),
    "omega3": load("omega3", "notations/Omega-LRD3/omega_lrd3.py"),
    "ard": load("ard", "notations/ARD/ard.py"),
}
CLASSES = {
    "rpd": MODULES["rpd"].RPD,
    "lrd": MODULES["lrd"].LRD,
    "omega3": MODULES["omega3"].OmegaLRD3,
    "ard": MODULES["ard"].AnchoredRows,
}


def sample_graphs(name):
    """Small descendants plus arbitrary valid inputs; no standardness claim."""
    cls = CLASSES[name]
    pending = [cls(), cls(((),))]
    pending += [cls.seed()] if name == "lrd" else [cls.seed(n) for n in (1, 2, 3)]
    seen = set()
    result = []
    # Keep both the queue and the number of explored graphs bounded.
    for cursor in range(100):
        deadline()
        if cursor >= len(pending) or len(result) >= 28:
            break
        graph = pending[cursor]
        if graph in seen:
            continue
        seen.add(graph)
        result.append(graph)
        for n in range(3):
            child = graph[n]
            if len(child.columns) <= 9 and len(str(child)) < 8000:
                pending.append(child)

    rng = random.Random(37691)
    if name in ("rpd", "ard"):
        rows = [0, 1, 2]
    elif name == "lrd":
        Row = MODULES[name].Row
        rows = [Row(), Row((2,)), Row((0, 1)), Row((1, 1)), Row(None)]
    else:
        rows = [cls.integer(0), cls.integer(1), cls.seed(1), cls.seed(2)]
    for _ in range(10):
        columns = [[]]
        for j in range(1, rng.randrange(2, 5)):
            column = []
            for _ in range(2):
                p = rng.randrange(j)
                row = rng.randrange(j) if name == "ard" else rng.choice(rows)
                column.append((row, p, rng.randrange(p + 1)))
            columns.append(column)
        result.append(cls(columns))
    return result


SAMPLES = {name: sample_graphs(name) for name in MODULES}


class Definitions(unittest.TestCase):
    def test_zero_successor_and_invalid_indices(self):
        for name, module in MODULES.items():
            with self.subTest(name=name):
                cls = CLASSES[name]
                self.assertEqual(module.ZERO, cls())
                for n in (0, 1, 3, 10**80):
                    self.assertEqual(module.ZERO[n], module.ZERO)
                    self.assertEqual(cls(((),))[n], module.ZERO)
                self.assertGreater(module.TOP, module.ZERO)
                for n in (-1, 0.5, "1", True):
                    with self.assertRaises((ValueError, TypeError)):
                        module.TOP[n]

    def test_seeds(self):
        for name in ("rpd", "omega3", "ard"):
            cls, module = CLASSES[name], MODULES[name]
            for n in range(6):
                deadline()
                self.assertEqual(module.TOP[n], cls.seed(n))
                self.assertGreater(module.TOP, cls.seed(n))
                if name in ("omega3", "ard"):
                    self.assertEqual(len(cls.seed(n).columns), n)
                    if n:
                        self.assertEqual(cls.seed(n)[0], cls.seed(n-1))
                elif n:
                    self.assertEqual(cls.seed(n)[1], cls.seed(n-1))
        lrd = MODULES["lrd"]
        self.assertEqual(lrd.TOP, lrd.T)
        self.assertEqual(lrd.T, lrd.LRD.seed())
        self.assertEqual(lrd.T[0], lrd.LRD(((),)))

    def test_row_arithmetic(self):
        Row = MODULES["lrd"].Row
        self.assertEqual(Row((1, 0, 0)), Row((1,)))
        self.assertEqual(Row(), Row(()))
        self.assertEqual(Row((0, 0, 1))[2], Row((0, 3)))
        self.assertEqual(Row((2, 1))[7], Row((1, 1)))
        for n in range(4):
            self.assertEqual(Row(None)[n], Row((0,)*(n+1)+(1,)))
            self.assertLess(Row(None)[n], Row(None))
        huge = 10**80
        self.assertEqual(Row((huge,))[0], Row((huge-1,)))
        self.assertGreater(Row((huge, 1)), Row((huge-1, 1)))

    def test_root_closure_and_structure(self):
        for name, cls in CLASSES.items():
            row = (0 if name in ("rpd", "ard") else MODULES[name].Row()
                   if name == "lrd" else cls())
            small = cls([[], [], [(row, 1, 1)]])
            repeated = cls([[], [], [(row, 1, 0), (row, 1, 1), (row, 1, 1)]])
            self.assertEqual(small, repeated)
            self.assertEqual(hash(small), hash(repeated))
            self.assertGreater(small, cls([[], [], [(row, 1, 0)]]))
            with self.assertRaises((ValueError, TypeError)):
                cls([[(row, 0, 0)]])
            with self.assertRaises((ValueError, TypeError)):
                cls([[], [(row, 0, 1)]])
            if name == "omega3":
                with self.assertRaises((ValueError, TypeError)):
                    cls([[], [(MODULES[name].TOP, 0, 0)]])

    def test_finite_expansion_and_prefix(self):
        steps = 0
        for name, graphs in SAMPLES.items():
            cls = CLASSES[name]
            for graph in graphs:
                deadline()
                previous = None
                for n in range(4):
                    child = graph[n]
                    if graph.columns:
                        self.assertLess(child, graph)
                    else:
                        self.assertEqual(child, graph)
                    if n == 0:
                        self.assertEqual(child, cls(graph.columns[:-1]))
                    if previous is not None:
                        self.assertGreaterEqual(len(child.columns), len(previous.columns))
                        self.assertEqual(child.columns[:len(previous.columns)], previous.columns)
                    previous = child
                    steps += 1
        print("Python finite checks:", steps, flush=True)

    def test_js_equivalence(self):
        node = os.environ.get("NOTATION_NODE") or shutil.which("node")
        if not node:
            self.skipTest("Node unavailable; Python-only checks still ran")
        cases, comparisons = [], []
        rng = random.Random(93472)
        for name, graphs in SAMPLES.items():
            samples = graphs + [MODULES[name].TOP]
            cls = CLASSES[name]
            # Check arbitrary-precision row coefficients without allocating
            # an arbitrary-precision NUMBER of columns or copies.
            if name == "rpd":
                samples += [cls(((), ((10**80+i, 0, 0),))) for i in range(2)]
            elif name == "lrd":
                Row = MODULES[name].Row
                samples += [cls(((), ((Row((10**80+i,)), 0, 0),))) for i in range(2)]
            for i, graph in enumerate(samples):
                deadline()
                cases.append({"notation": name, "id": i, "raw": str(graph),
                              "outputs": [str(graph[n]) for n in range(4)]})
            for _ in range(100):
                a, b = rng.choice(samples), rng.choice(samples)
                comparisons.append({"notation": name, "a": str(a), "b": str(b),
                                    "expected": int(a > b) - int(a < b)})
        data = json.dumps({"cases": cases, "comparisons": comparisons}, ensure_ascii=False)
        self.assertLess(len(data), 4000000)
        # subprocess.run kills and waits for its child on timeout. No persistent
        # workers or browser processes are created by these tests.
        process = subprocess.run(
            [node, "--max-old-space-size=256", str(ROOT/"tests/python-reference.cjs")],
            input=data, text=True, encoding="utf-8", capture_output=True, timeout=20,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        summary = json.loads(process.stdout)
        self.assertEqual(summary["expansions"], 4*len(cases))
        self.assertEqual(summary["comparisons"], 100*len(MODULES))
        print("JS cross-check:", summary, flush=True)

    def test_omega3_independent_tuple_definition(self):
        reference = load("omega3_tuple", "tests/omega3_tuple_reference.py")
        cls = CLASSES["omega3"]

        def encode(value):
            return tuple(tuple((p, encode(row), q) for row, p, q in column)
                         for column in value.columns)

        for n in range(7):
            self.assertEqual(encode(cls.seed(n)), reference.start_term(n))
        checks = 0
        for graph in SAMPLES["omega3"]:
            deadline()
            for n in range(4):
                self.assertEqual(encode(graph[n]), reference.step(encode(graph), n))
                checks += 1
        print("Omega3 independent tuple cross-check:", checks, flush=True)


if __name__ == "__main__":
    unittest.main(verbosity=2)
