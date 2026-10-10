"""Independent Python replay of the packaged CDMN JavaScript vectors."""
import importlib.util
import json
from pathlib import Path
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("cdmn", ROOT / "notations/CDMN/cdmn.py")
cdmn = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cdmn)


class CoreTests(unittest.TestCase):
    def test_zero_and_one(self):
        self.assertEqual(cdmn.seed(0), cdmn.ONE)
        for n in range(5):
            self.assertEqual(cdmn.fundamental(cdmn.ZERO, n), cdmn.ZERO)
            self.assertEqual(cdmn.fundamental(cdmn.ONE, n), cdmn.ZERO)

    def test_documented_paths(self):
        fixtures = json.loads((ROOT / "notations/CDMN/fixtures/regressions.json").read_text(encoding="utf-8"))
        for case in fixtures:
            with self.subTest(case=case["input"]):
                g = cdmn.seed(case["seed"])
                for n in case["route"]:
                    g = cdmn.fundamental(g, n)
                self.assertEqual(g, cdmn.from_json(case["graph"]))
                self.assertTrue(cdmn.legal(g))

    def test_invalid_indices(self):
        for n in (-1, 0.5, "2"):
            with self.assertRaises(ValueError):
                cdmn.seed(n)
            with self.assertRaises(ValueError):
                cdmn.fundamental(cdmn.ONE, n)

    def test_owner_exclusion(self):
        self.assertFalse(cdmn.legal((((0, cdmn.ONE),),)))
        self.assertFalse(cdmn.legal(((), ((1, cdmn.ONE),))))
        self.assertFalse(cdmn.legal(((), ((0, cdmn.ZERO),))))

    def test_prefix_zero(self):
        natural = lambda n: ((),) * n
        edge = lambda p, row: ((p, row),)
        self.assertEqual(cdmn.fundamental(cdmn.seed(2), 0), natural(2))
        for n in (1, 2, 3):
            self.assertEqual(cdmn.fundamental(cdmn.seed(2), n),
                             ((), edge(0, natural(n))))
        growing = ((), edge(0, natural(2)), edge(1, natural(2)))
        self.assertEqual(cdmn.fundamental(growing, 0), growing[:-1])
        first = growing[:-1] + (((1, cdmn.ONE), (0, natural(2))),)
        self.assertEqual(cdmn.fundamental(growing, 1), first)
        self.assertEqual(cdmn.fundamental(first, 0), growing[:-1])
        self.assertEqual(cdmn.fundamental(((), edge(0, natural(2))), 1), cdmn.seed(1))

    def test_adjacent_reader_research_entrances(self):
        edge = lambda p, row: ((p, row),)
        w = lambda p: (edge(p, cdmn.ONE),)
        adjacent = ((), edge(0, w(0) + ((),)))

        def follow(graph, route):
            for n in route:
                child = cdmn.fundamental(graph, n)
                self.assertTrue(cdmn.legal(child))
                self.assertLess(child, graph)
                graph = child
            return graph

        self.assertEqual(follow(cdmn.seed(3), [2, 2, 1, 1, 0]), adjacent)
        for n in range(9):
            expected = ((),) + tuple(edge(j, w(j)) for j in range(n))
            self.assertEqual(cdmn.fundamental(adjacent, n), expected)
        c2 = cdmn.fundamental(adjacent, 2)
        stem = ((), edge(0, w(0)), edge(0, cdmn.ONE), edge(2, w(0)))
        minimum = stem + (edge(2, cdmn.ONE),)
        frontier = stem + (edge(2, cdmn.ONE * 2),
                           ((4, cdmn.ONE), (2, cdmn.ONE)), edge(5, w(0)))
        self.assertEqual(follow(c2, [1, 0, 1, 1, 0, 1, 2, 1, 0, 0, 0, 1, 2, 1,
                                    0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0,
                                    0, 1, 0, 0]), minimum)
        self.assertEqual(follow(c2, [1, 0, 1, 1, 0, 1, 2, 1, 0, 0, 0, 1, 2, 1,
                                    0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0,
                                    1, 2, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0]), frontier)


def vectors():
    start = time.monotonic()
    checks = 0
    for line in sys.stdin:
        if checks >= 6000 or len(line) > 2_000_000 or time.monotonic() - start > 30:
            raise RuntimeError("CDMN vector replay budget exhausted")
        case = json.loads(line)
        g, context = cdmn.from_json(case["graph"]), cdmn.from_json(case["context"])
        expected = cdmn.from_json(case["expected"])
        actual = cdmn.fundamental(g, case["n"], context)
        assert actual == expected, (checks, "Python/JS mismatch")
        assert cdmn.legal(g, len(context)) and cdmn.legal(actual, len(context))
        assert not g or actual < g
        checks += 1
    assert checks == 6000, (checks, "incomplete test stream")
    print(json.dumps({"independent_expansions": checks, "elapsed_seconds": round(time.monotonic()-start, 3)}))


if __name__ == "__main__":
    if "--vectors" in sys.argv:
        vectors()
    else:
        unittest.main()
