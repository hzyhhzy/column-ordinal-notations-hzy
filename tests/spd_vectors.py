"""Emit JSON-only SPD conformance vectors to stdout, within a 5-second budget.

No research-probe dependency. Node may JSON.parse(execFileSync('python',
['-B', 'spd_vectors.py'], {encoding:'utf8', maxBuffer:16*1024*1024})).
"""
from collections import deque
import json
import random
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'SPD'))
import spd
from spd_test_limits import install

GUARD = install(spd, seconds=45)

START = time.monotonic()


def check():
    if time.monotonic() - START > 5:
        raise TimeoutError('SPD JSON-vector five-second construction budget')


def make_case(name, graph, origin):
    check()
    outputs = [spd.fs(graph, n) for n in range(4)]
    return {'id': name, 'origin': origin, 'graph': graph,
            'normalized': spd.normalize(graph), 'counts': spd.counts(graph),
            'outputs': outputs, 'output_counts': [spd.counts(g) for g in outputs]}


def main():
    queue = deque((spd.seed(n), n, ()) for n in range(4))
    seen, cases = set(), []
    while queue and len(seen) < 36:
        check()
        graph, seed_index, path = queue.popleft()
        if graph in seen or len(graph) > 9 or sum(map(len, graph)) > 800:
            continue
        seen.add(graph)
        case = make_case(f'std-{len(cases)}', graph, {'seed': seed_index, 'path': path})
        cases.append(case)
        for n, output in enumerate(case['outputs']):
            if len(output) <= 9:
                queue.append((output, seed_index, path + (n,)))
    rng = random.Random(20260914)
    for index in range(8):
        graph = [[]]
        for j in range(1, rng.randrange(2, 7)):
            rows = []
            for _ in range(rng.randrange(1, 6)):
                p = rng.randrange(j)
                h, s = rng.randrange(p + 1), rng.randrange(p + 1)
                q = rng.choice((*range(p + 1), j, j + 1))
                rows.append([h, p, s, q])
                if rng.randrange(3) == 0:
                    rows.append([h, p, s, rng.choice((*range(p + 1), j, j + 1))])
            rng.shuffle(rows)
            graph.append(rows)
        cases.append(make_case(f'raw-{index}', graph, {'raw': index}))
    comparisons = []
    for _ in range(100):
        i, j = rng.randrange(len(cases)), rng.randrange(len(cases))
        check()
        comparisons.append({'left': i, 'right': j,
                            'expected': spd.compare(cases[i]['graph'], cases[j]['graph'])})
    seeds = [{'n': n, 'graph': spd.seed(n), 'counts': spd.counts(spd.seed(n))} for n in range(6)]
    result = {'format': 'SPD-conformance-v1',
              'seed_convention': 'seed(n)=S_n has n+1 columns; S_0=[[]]; empty graph=[]',
              'fixed_rule': 'LATENT; highest visible head fiber; canonical fullguard; typed carry',
              'output_indices': [0, 1, 2, 3], 'seeds': seeds, 'cases': cases,
              'comparisons': comparisons,
              'invalid_graphs': [[[], [[True, 0, 0, 1]]], [[], [[0, 0, 0, -1]]],
                                 [[], [[0, 1, 0, 1]]], [[], [[0, 0, 0, 3]]]],
              'invalid_indices': [-1, True, 1.5],
              'seconds': round(time.monotonic() - START, 4)}
    check()
    json.dump(result, sys.stdout, separators=(',', ':'))
    sys.stdout.write('\n')


if __name__ == '__main__':
    main()
