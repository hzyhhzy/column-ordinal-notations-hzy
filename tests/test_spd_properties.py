"""Deterministic bounded one-step properties on mixed-parent raw diagrams.

These are local checks, NOT a standard-membership or global well-order proof.
No descent-to-zero enumeration. Each allocation and the entire run are bounded.
"""
import random
import time
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'SPD'))
import spd
from spd_test_limits import install

GUARD = install(spd, seconds=45)


def main():
    started = time.monotonic()
    randomizer = random.Random(14092026)
    graphs = expansions = decrements = 0
    for case in range(160):
        if time.monotonic() - started > 18:
            raise TimeoutError('Overall property probe deadline')
        raw = [[]]
        for j in range(1, randomizer.randrange(2, 9)):
            rows = []
            for _ in range(randomizer.randrange(9)):
                p = randomizer.randrange(j)
                h, s = randomizer.randrange(p + 1), randomizer.randrange(p + 1)
                q = randomizer.choice((*range(p + 1), j, j + 1))
                rows.append((h, p, s, q))
                if randomizer.randrange(5) == 0:
                    rows.append((h, p, s, j + 1))
            randomizer.shuffle(rows)
            raw.append(rows)
        budget = spd.Budget(seconds=2, max_events=1_000_000,
                            max_columns=50, max_rows=50_000,
                            max_nodes=15_000, max_slots=100_000,
                            max_pairs=60_000, max_contexts=20_000)
        graph = spd.normalize(raw, budget)
        old_counts = spd.counts(graph, budget)
        assert spd.normalize(graph, budget) == graph
        for j, value in enumerate(old_counts):
            upper = 1 + (j * (j + 1) // 2) ** 2 + j * (j + 1) * (2 * j + 1) // 3
            assert 1 <= value <= upper, (case, j, value, upper)
        previous = ()
        for n in range(4):
            result = spd.fs(graph, n, budget)
            assert spd.normalize(result, budget) == result
            assert result[:len(previous)] == previous
            assert result[:len(graph) - 1] == graph[:-1]
            assert spd.compare(result, graph, budget) < 0
            if n == 0:
                assert result == graph[:-1]
            elif graph[-1]:
                assert spd.counts(result, budget)[len(graph) - 1] == old_counts[-1] - 1
                decrements += 1
            previous = result
            expansions += 1
        graphs += 1
    print({'ok': True, 'raw_graphs': graphs, 'one_step_expansions': expansions,
           'count_decrements': decrements, 'seconds': round(time.monotonic() - started, 3),
           'peak_rss_mib':round(GUARD.peak_mib(),2)})


if __name__ == '__main__':
    main()
