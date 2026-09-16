"""Bounded check of the frozen-prefix RPD -> published ARD simulation.

This executes the actual two Python definitions. It checks the proposed paper
invariants and finite exposure paths; it is not a universal comparison proof.
"""
from collections import deque
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True


ROOT = Path(__file__).resolve().parents[1]


def module(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


RPD = module("rpd_comparison_source", "notations/RPD/rpd.py").RPD
ARD = module("ard_comparison_target", "notations/ARD-legacy/ard.py").AnchoredRows
DEADLINE = time.perf_counter() + 25
MAX_LOCAL = 2000
MAX_STATES_PER_SEED = 80
MAX_SOURCE_WIDTH = 10
MAX_TARGET_WIDTH = 32
STATS = {"seed_checks": 0, "states": 0, "simulated_steps": 0,
         "local_preparation_steps": 0, "max_preparation": 0,
         "same_priority_detours": 0, "outside_cut_preparations": 0,
         "nonunique_source_top": 0, "raw_exposure_cases": 0,
         "forest_checks": 0, "v_checks": 0}


def tick():
    if time.perf_counter() >= DEADLINE:
        raise RuntimeError("25-second total test deadline")


def atoms(graph):
    return [set((k, p, r) for k, p, q in col for r in range(q + 1))
            for col in graph.columns]


def control(graph):
    return max(graph.columns[-1], key=lambda e: (e[0], e[2], e[1]))


def covered(source, target, d):
    assert len(target.columns) == d + len(source.columns)
    target_atoms = atoms(target)
    for j, col in enumerate(source.columns):
        for k, p, q in col:
            assert (k, d + p, d + q) in target_atoms[d + j], (
                "coverage", str(source), str(target), (k, p, q, j))


def invariants(target, level, d):
    tick()
    assert target.columns[:d] == ARD.seed(2)[level].columns
    assert all(k <= level for col in target.columns for k, p, q in col)
    closed = atoms(target)
    for col in closed:
        for k, p in {(k, p) for k, p, q in col if p >= d}:
            assert all((h, p, r) in col for h in range(k) for r in range(p + 1)), (
                "active V", str(target), (k, p))
    STATS["v_checks"] += 1
    labels = {(k, r) for col in closed for k, p, r in col if r >= d}
    for k, r in labels:
        ancestors = []
        for col in closed:
            parents = {p for h, p, q in col if (h, q) == (k, r)}
            reach = set(parents)
            for p in parents:
                reach.update(ancestors[p])
            for p in parents:
                for c in parents:
                    if p < c:
                        assert p in ancestors[c], ("F", str(target), (k, r, p, c))
            ancestors.append(reach)
    STATS["forest_checks"] += len(labels)


def local(target):
    """Actual [1] followed by enough actual [0] steps; not an added rule."""
    width = len(target.columns)
    x = width - 1
    _, c, _ = control(target)
    assert x + (x - c) <= MAX_TARGET_WIDTH
    result = target[1]
    while len(result.columns) > width:
        result = result[0]
    assert len(result.columns) == width and result < target
    assert result.columns[:-1] == target.columns[:-1]
    return result


def simulate(source, target, n, level, d):
    tick()
    covered(source, target, d)
    if not source.columns:
        return source, target
    child = source[n]
    if n == 0 or not source.columns[-1]:
        result = target[0]
    else:
        k, p, r = control(source)
        desired = (k, d + p, d + r)
        priority = (k, d + r)
        top_parents = {v for h, v, q in source.columns[-1] if (h, q) == (k, r)}
        if len(top_parents) > 1:
            STATS["nonunique_source_top"] += 1
        original_lower = {(h, v, q) for h, v, q in atoms(target)[-1] if (h, q) < priority}
        prepared = target
        steps = 0
        while control(prepared) != desired:
            assert steps < MAX_LOCAL, "bounded preparation cap"
            h, c, q = control(prepared)
            assert (h, q) >= priority
            if (h, q) == priority:
                assert c > desired[1]
                STATS["same_priority_detours"] += 1
            if c < d:
                STATS["outside_cut_preparations"] += 1
            prepared = local(prepared)
            assert original_lower <= atoms(prepared)[-1]
            invariants(prepared, level, d)
            steps += 1
        STATS["local_preparation_steps"] += steps
        STATS["max_preparation"] = max(STATS["max_preparation"], steps)
        assert len(prepared.columns) - 1 + n * (len(prepared.columns) - 1 - desired[1]) <= MAX_TARGET_WIDTH
        result = prepared[n]
    assert result < target
    covered(child, result, d)
    invariants(result, level, d)
    STATS["simulated_steps"] += 1
    return child, result


def main():
    started = time.perf_counter()
    for level in range(4):
        tick()
        d = level + 1
        bound = ARD.seed(2)
        target = bound[level + 2]
        prefix = target.columns[:-1]
        for _ in range(level + 1):
            target = target[1]
        expected = ARD(prefix + (tuple((h, d, d) for h in range(level + 1)) + prefix[-1],))
        assert target == expected
        assert target < bound
        source = RPD.seed(level)
        covered(source, target, d)
        invariants(target, level, d)
        STATS["seed_checks"] += 1
        queue = deque([(source, target, 0)])
        seen = {(source, target)}
        while queue:
            source, target, depth = queue.popleft()
            STATS["states"] += 1
            if not source.columns:
                continue
            # Deliberately demand a nonmaximal parent at one priority. These
            # auxiliary source graphs are raw, not claimed to be standard;
            # the paper's one-step simulation lemma applies to them as well.
            if STATS["raw_exposure_cases"] < 4:
                parents = {p for k, p, q in atoms(target)[-1] if k == 0 and q == d}
                if len(parents) > 1:
                    raw_columns = [() for _ in source.columns]
                    raw_columns[-1] = ((0, min(parents) - d, 0),)
                    raw_source = RPD(tuple(raw_columns))
                    simulate(raw_source, target, 1, level, d)
                    STATS["raw_exposure_cases"] += 1
            for n in range(4):
                tick()
                if source.columns[-1] and n:
                    _, c, _ = control(source)
                    x = len(source.columns) - 1
                    if x + n * (x - c) > MAX_SOURCE_WIDTH:
                        continue
                child, output = simulate(source, target, n, level, d)
                pair = (child, output)
                if depth < 4 and len(seen) < MAX_STATES_PER_SEED and pair not in seen:
                    seen.add(pair)
                    queue.append((child, output, depth + 1))
    print(json.dumps({"passed": True, "uniform_ARD_bound": str(ARD.seed(2)), **STATS,
                      "seconds": round(time.perf_counter() - started, 3)}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        print(json.dumps({"passed": False, **STATS}, indent=2), flush=True)
        raise


