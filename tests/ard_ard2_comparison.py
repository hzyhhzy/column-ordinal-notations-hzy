"""Bounded actual-step ARD-legacy -> ARD2 coverage experiment.

No global theorem is inferred from successful samples.  All source/target
operations call the repository implementations; only local fixed-width
preparation is iterated.  Budget exits are unknown, never counted as success.
"""
import argparse
from collections import deque
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[1]


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


ARD = module("comparison_legacy", "notations/ARD-legacy/ard.py").AnchoredRows
ARD2 = module("comparison_ard2", "notations/ARD2/ard2.py").ARD2


def control(graph):
    return max(graph.columns[-1], key=lambda edge: (edge[0], edge[2], edge[1]))


def covers(source, target):
    if len(source.columns) != len(target.columns):
        return False
    for first, second in zip(source.columns, target.columns):
        roots = {(k, p): q for k, p, q in second}
        if any(roots.get((k, p), -1) < q for k, p, q in first):
            return False
    return True


def safe_forest(graph, threshold=True):
    """Priority-threshold graph, restricted to parents >= max(k,u)."""
    width = len(graph.columns)
    for k in range(width):
        for u in range(width):
            ancestors = []
            for j, column in enumerate(graph.columns):
                direct = {p for h, p, q in column
                          if ((h, q) >= (k, u) if threshold else h == k and q >= u)
                          and p >= max(k, u)}
                whole = set(direct)
                for p in direct:
                    whole.update(ancestors[p])
                for p in whole:
                    for c in whole:
                        if p < c and p not in ancestors[c]:
                            return {"priority": [k, u], "child": j, "parents": [p, c]}
                ancestors.append(whole)
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=20)
    parser.add_argument("--states", type=int, default=1200)
    parser.add_argument("--width", type=int, default=12)
    parser.add_argument("--prepare", type=int, default=3000)
    args = parser.parse_args()
    start = time.perf_counter()
    stats = {"states": 0, "simulations": 0, "preparations": 0,
             "max_preparation": 0, "unknown": 0, "forest_failures": 0}
    queue, seen = deque(), set()
    for width in range(1, 7):
        source = ARD.seed(width)
        target = ARD2.seed(2)[1][1][width - 1]
        assert covers(source, target)
        pair = (source, target)
        seen.add(pair)
        queue.append((source, target, width, []))
    first_forest = None
    while queue and stats["states"] < args.states:
        if time.perf_counter() - start > args.seconds:
            stats["unknown"] += len(queue)
            break
        source, target, seed, path = queue.popleft()
        stats["states"] += 1
        assert covers(source, target)
        bad_forest = safe_forest(target)
        if bad_forest:
            stats["forest_failures"] += 1
            if first_forest is None:
                first_forest = {"seed": seed, "path": path, "target": str(target), **bad_forest}
            raise AssertionError(first_forest)
        if not source.columns:
            continue
        prepared = target
        preparation = 0
        if source.columns[-1]:
            wanted = control(source)
            while prepared.columns[-1] and control(prepared) != wanted:
                if preparation >= args.prepare or time.perf_counter() - start > args.seconds:
                    stats["unknown"] += 1
                    prepared = None
                    break
                actual = control(prepared)
                if (actual[0], actual[2]) < (wanted[0], wanted[2]):
                    print(json.dumps({"result": "exposure_failed", "source": str(source),
                          "target": str(target), "prepared": str(prepared),
                          "wanted": wanted, "actual": actual, "seed": seed,
                          "source_path": path, "preparation": preparation,
                          "first_forest": first_forest, "stats": stats}, indent=2))
                    raise AssertionError("Required controller priority lost")
                previous = prepared
                prepared = prepared.local_step()
                actual_path = previous[1]
                while len(actual_path.columns) > len(previous.columns):
                    actual_path = actual_path[0]
                assert prepared == actual_path and prepared < previous
                assert safe_forest(prepared) is None
                preparation += 1
            if prepared is not None and not prepared.columns[-1]:
                print(json.dumps({"result": "empty_before_exposure", "source": str(source),
                      "target": str(target), "wanted": wanted, "seed": seed,
                      "source_path": path, "preparation": preparation,
                      "first_forest": first_forest, "stats": stats}, indent=2))
                raise AssertionError("Target emptied before exposure")
            stats["preparations"] += preparation
            stats["max_preparation"] = max(stats["max_preparation"], preparation)
        if prepared is None:
            continue
        for index in range(4):
            x = len(source.columns) - 1
            width = x if not index or not source.columns[-1] else x + index * (x - control(source)[1])
            if width > args.width:
                stats["unknown"] += 1
                continue
            child = source[index]
            output = target[0] if not index or not source.columns[-1] else prepared[index]
            if not covers(child, output):
                print(json.dumps({"result": "step_cover_failed", "source": str(source),
                      "target": str(target), "prepared": str(prepared),
                      "child": str(child), "output": str(output), "index": index,
                      "seed": seed, "source_path": path, "preparation": preparation,
                      "first_forest": first_forest, "stats": stats}, indent=2))
                raise AssertionError("Actual target step failed to cover source child")
            stats["simulations"] += 1
            pair = (child, output)
            if pair not in seen and len(seen) < args.states * 4:
                seen.add(pair)
                queue.append((child, output, seed, [*path, index]))
    print(json.dumps({"result": "bounded_pass", "stats": stats,
                      "queued": len(queue), "first_forest": first_forest,
                      "seconds": round(time.perf_counter() - start, 3)}, indent=2))


if __name__ == "__main__":
    main()
