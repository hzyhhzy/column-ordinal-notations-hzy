"""Unified SPD regression: independent tuple oracle, properties, counts and JS.

Run python -B tests/test_spd.py; --reference-only runs just the tuple parity.
No dependency on the private research output directory. Each child and the
entire runner have a <55-second deadline; Node uses a 256-MiB heap ceiling.
"""
from collections import deque
import random
import time
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'notations'/'SPD'))
import spd
import spd_tuple_reference as oracle
from spd_test_limits import install

START = time.monotonic()
GUARD = install(spd,seconds=54)


def random_raw(rng):
    columns = [[]]
    for j in range(1, rng.randrange(2, 7)):
        rows = []
        for _ in range(rng.randrange(6)):
            p = rng.randrange(j)
            h, s = rng.randrange(p + 1), rng.randrange(p + 1)
            q = rng.choice((*range(p + 1), j, j + 1))
            rows.append([h, p, s, q])
            if rng.randrange(4) == 0:
                rows.append([h, p, s, rng.choice((*range(p + 1), j, j + 1))])
        rng.shuffle(rows)
        columns.append(rows)
    return columns


def reference_main():
    queue = deque((spd.seed(n), n, ()) for n in range(4))
    seen, samples = set(), []
    steps = local_counts = 0
    while queue and len(seen) < 65:
        g, seed_index, path = queue.popleft()
        if g in seen or len(g) > 10 or sum(map(len, g)) > 1200:
            continue
        seen.add(g)
        samples.append(g)
        old = oracle.read(g)
        assert spd.normalize(g) == tuple(old.columns)
        assert spd.counts(g) == tuple(oracle.count(old, j) for j in range(len(g)))
        previous = ()
        for n in range(4):
            actual, expected = spd.fs(g, n), oracle.fs(g, n)
            assert actual == expected, (seed_index, path, n)
            assert actual[:len(previous)] == previous
            assert actual[:max(0, len(g) - 1)] == g[:-1]
            assert not g or spd.compare(actual, g) < 0
            if n and g and g[-1]:
                assert spd.counts(actual)[len(g) - 1] == spd.counts(g)[-1] - 1
                local_counts += 1
            previous = actual
            steps += 1
            if len(actual) <= 10:
                queue.append((actual, seed_index, path + (n,)))
    rng = random.Random(914)
    raw_steps = 0
    for _ in range(45):
        raw = random_raw(rng)
        normalized = spd.normalize(raw)
        d = oracle.read(raw)
        assert normalized == tuple(d.columns)
        assert spd.counts(raw) == tuple(oracle.count(d, j) for j in range(len(raw)))
        for n in range(4):
            assert spd.fs(raw, n) == oracle.fs(raw, n)
            raw_steps += 1
        samples.append(normalized)
    comparisons = 0
    for _ in range(100):
        left, right = rng.choice(samples), rng.choice(samples)
        assert spd.compare(left, right) == oracle.graph_compare(left, right)
        comparisons += 1
    invalid = [lambda: spd.seed(True), lambda: spd.seed(-1),
               lambda: spd.fs((), False), lambda: spd.fs((), 1.0),
               lambda: spd.normalize([[], [(False, 0, 0, 1)]]),
               lambda: spd.normalize([[], [(0, 0, 0, -1)]]),
               lambda: spd.Budget(max_events=True), lambda: spd.Budget(seconds=True),
               lambda: spd.Budget(seconds=float('nan'))]
    for bad in invalid:
        try:
            bad()
        except ValueError:
            pass
        else:
            raise AssertionError('Invalid natural number/budget accepted')
    for call in (lambda: spd.seed(2, spd.Budget(max_columns=2)),
                 lambda: spd.fs(spd.seed(2), 3, spd.Budget(max_rows=12)),
                 lambda: spd.normalize(spd.seed(3), spd.Budget(max_events=3)),
                 lambda: spd.seed(1, spd.Budget(max_slots=1))):
        try:
            call()
        except (OverflowError, TimeoutError):
            pass
        else:
            raise AssertionError('Resource exhaustion did not raise')
    tall = spd.seed(1199)
    assert len(tall) == 1200 and spd.fs(tall, 0) == tall[:-1]
    assert spd.seed(0) == ((),)
    assert spd.counts(spd.seed(5)) == (1, 3, 16, 45, 96, 175)
    print({'status': 'SPD_matches_independent_tuple_oracle', 'standard_states': len(seen),
           'standard_steps': steps, 'raw_graphs': 45, 'raw_steps': raw_steps,
           'local_count_decrements': local_counts, 'cross_graph_comparisons': comparisons,
           'invalid_inputs_rejected': len(invalid), 'resource_limits_raised': 4,
           'iterative_chain_columns': len(tall), 'oracle_events': oracle.events,
           'seconds': round(time.monotonic() - START, 3),
           'peak_rss_mib':round(GUARD.peak_mib(),2)},flush=True)


def child(arguments,payload=None):
    remaining=54-(time.monotonic()-START)
    if remaining<=0:
        raise TimeoutError('54-second unified SPD runner deadline')
    result=subprocess.run(arguments,cwd=ROOT,input=payload,capture_output=True,
                          text=True,encoding='utf-8',timeout=min(50,remaining),
                          env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    if len(result.stdout)>16*1024*1024 or len(result.stderr)>1024*1024:
        raise OverflowError('SPD child-output bound')
    if result.returncode:
        raise RuntimeError(f'{arguments}:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def main():
    reference_main()
    if '--reference-only' in sys.argv[1:]:
        return
    for filename in ('test_spd_properties.py','test_spd_counts.py'):
        print(child([sys.executable,'-B',str(ROOT/'tests'/filename)]).strip(),flush=True)
    node=shutil.which('node')
    if node is None:
        raise RuntimeError('Node.js is required for the SPD cross-language suite')
    vectors=child([sys.executable,'-B',str(ROOT/'tests'/'spd_vectors.py')])
    print(child([node,'--max-old-space-size=256',str(ROOT/'tests'/'spd_ner.cjs'),'--vectors'],
                vectors).strip(),flush=True)
    count_vectors=child([sys.executable,'-B',str(ROOT/'tests'/'test_spd_counts.py'),'--vectors'])
    print(child([node,'--max-old-space-size=256',str(ROOT/'tests'/'spd_count_ner.cjs')],
                count_vectors).strip(),flush=True)
    GUARD.check()
    print(json.dumps({'ok':True,'suite':'SPD portable integration',
                      'seconds':round(time.monotonic()-START,3),
                      'parent_peak_rss_mib':round(GUARD.peak_mib(),2)}))


if __name__ == '__main__':
    main()
