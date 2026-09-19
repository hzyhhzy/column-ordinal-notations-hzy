"""Bounded Python fixtures for the 2026-09-20 ACD/CSD/ICP import.

No search for global termination. At most 120 states per notation, indices
0..3, 40 output columns, 25 seconds. Run with -B to avoid bytecode artifacts.
"""
import importlib.util
import json
from pathlib import Path
import sys
from time import monotonic

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
START = monotonic()


def tick():
    if monotonic() - START > 25:
        raise RuntimeError('25-second test deadline')


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


acd = load('acd', ROOT / 'notations/ACD/acd.py')
csd = load('csd', ROOT / 'notations/CSD/csd.py')
clock = load('csd_clock', ROOT / 'notations/CSD/local_clock.py')
icp = load('icp', ROOT / 'notations/ICP/icp.py')


def bounded_counts(name, value):
    work = 0

    def local_tick():
        nonlocal work
        tick()
        work += 1
        if work > 20000:
            raise RuntimeError('Local count budget')

    try:
        if name == 'ACD':
            values = value.counts(local_tick)
        elif name == 'CSD':
            values = [clock.Clock(value.columns[:j], local_tick).work(c) + 1
                      for j, c in enumerate(value.columns)]
        else:
            values = icp.counts(value, icp.Budget(max_work=20000, seconds=0.1))
        return list(map(str, values))
    except RuntimeError:
        tick()  # Never downgrade the whole-suite deadline to a count skip.
        return None


def fixtures(name):
    if name == 'ACD':
        seed, expand, show = acd.ACD.seed, lambda g, n: g.fs(n), str
        columns = lambda g: g.columns
        compare = lambda a, b: a.compare(b)
    elif name == 'CSD':
        seed, expand, show = csd.CSD.seed, lambda g, n: g.fs(n), str
        columns = lambda g: g.columns
        compare = lambda a, b: (a > b) - (a < b)
    else:
        seed, expand, show = icp.seed, lambda g, n: icp.expand(g, n, icp.Budget()), icp.display
        columns = lambda g: g
        compare = lambda a, b: (a > b) - (a < b)
    queue = [seed(j) for j in range(4)]
    seen = {show(g) for g in queue}
    cases, skipped, count_skips = [], 0, 0
    index = 0
    while index < len(queue) and index < 120:
        tick()
        current = queue[index]
        index += 1
        text = show(current)
        outputs = []
        for n in range(4):
            tick()
            out = expand(current, n)
            assert show(current) == text, 'Input mutation'
            assert columns(out)[:max(0, len(columns(current)) - 1)] == columns(current)[:-1]
            if columns(current):
                assert compare(out, current) < 0
            if n:
                assert columns(out)[:len(columns(outputs[-1]))] == columns(outputs[-1])
            outputs.append(out)
            if len(columns(out)) > 40 or len(show(out)) > 12000:
                skipped += 1
                continue
            key = show(out)
            if len(columns(out)) <= 12 and len(key) <= 2000 and key not in seen and len(queue) < 180:
                seen.add(key)
                queue.append(out)
        values = bounded_counts(name, current)
        count_skips += values is None
        for n, out in enumerate(outputs):
            if len(columns(out)) <= 40 and len(show(out)) <= 12000:
                cases.append({'input': text, 'index': n, 'output': show(out), 'counts': values})
    return {'name': name, 'states': index, 'cases': cases, 'size_skips': skipped,
            'count_skips': count_skips}


def main():
    result = {'notations': [fixtures(name) for name in ('ACD', 'CSD', 'ICP')]}
    if '--fixtures' in sys.argv:
        print(json.dumps(result, ensure_ascii=True, separators=(',', ':')))
    else:
        print(json.dumps([{k: len(v) if k == 'cases' else v for k, v in item.items()}
                          for item in result['notations']], indent=2))


if __name__ == '__main__':
    main()
