"""Bounded standard count decoding, rejection, and raw-collision checks."""
from collections import deque
from itertools import product
import json
import sys
import time
from pathlib import Path
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'SPD'))
import spd
from spd_count_decode import decode_counts, InvalidCounts, column_bound, is_standard
from spd_test_limits import install

GUARD = install(spd, seconds=50)


def main():
    started = time.monotonic()
    total = spd.Budget(seconds=50,max_events=70000000,max_nodes=6000000,
                       max_slots=30000000,max_pairs=8000000,max_contexts=8000000,
                       max_columns=250,max_rows=35000000)
    # An independent actual T_m chain enumerates the finite width<=3 cone.
    small = {}
    g = spd.seed(2,total)
    for _ in range(100):
        small[spd.counts(g,total)] = g
        if not g:
            break
        g = spd.fs(g,3,total)[:3]
    else:
        raise AssertionError('small finite-width state cap')
    exhaustive = accepted = 0
    for m in range(4):
        for values in product(*(range(1,column_bound(j)+1) for j in range(m))):
            exhaustive += 1
            try:
                decoded = decode_counts(values,budget=total)
            except InvalidCounts:
                assert values not in small
            else:
                assert values in small and decoded == small[values]
                accepted += 1
    for invalid in ((0,),(-1,),(True,),(1,0),(2,),(1,5)):
        try:
            decode_counts(invalid,budget=total)
        except InvalidCounts:
            pass
        else:
            raise AssertionError(('invalid accepted',invalid))
    print({'small_exhaustive':exhaustive,'accepted':accepted,
           'finite_width_states':len(small)},flush=True)
    # Reproduce the same 65 true Std states as test_spd.py.
    queue = deque(spd.seed(n,total) for n in range(4))
    seen = set()
    collision = None
    steps = 0
    while queue and len(seen)<65:
        g = queue.popleft()
        if g in seen or len(g)>10 or sum(map(len,g))>1200:
            continue
        seen.add(g)
        values = spd.counts(g,total)
        report = {}
        assert decode_counts(values,budget=total,stats=report) == g
        steps += report['local_d_steps']
        if collision is None:
            d = spd.read(g,total)
            for j,col in enumerate(g):
                for row in col:
                    if any(e[1]==row[1] and d.profile(e,row)>0 for e in col):
                        raw = (*g[:j],tuple(e for e in col if e!=row),*g[j+1:])
                        if spd.counts(raw,total)==values:
                            collision=(g,raw,values)
                            break
                if collision is not None:
                    break
        for n in range(4):
            child = spd.fs(g,n,total)
            if len(child)<=10:
                queue.append(child)
    assert len(seen)==65
    assert collision is not None
    good,raw,values=collision
    assert good!=raw and spd.counts(good,total)==spd.counts(raw,total)
    assert decode_counts(values,budget=total)==good
    assert is_standard(good,budget=total)
    assert not is_standard(raw,budget=total)
    assert is_standard((),budget=total)
    try:
        is_standard((((0,0,0,0),),),budget=total)
    except ValueError:
        pass
    else:
        raise AssertionError('illegal graph did not raise')
    try:
        is_standard(good,budget=total,max_width=0)
    except OverflowError:
        pass
    else:
        raise AssertionError('membership resource limit did not propagate')
    # Resource exhaustion must never be reported as invalidity.
    try:
        decode_counts((1,2),max_d_steps=0,budget=total)
    except OverflowError:
        pass
    else:
        # This target uses one T_m and no frozen D; use the lower target.
        try:
            decode_counts((1,1),max_d_steps=0,budget=total)
        except OverflowError:
            pass
        else:
            raise AssertionError('local-D limit did not propagate')
    print({'status':'standard_counts_decode_uniquely_not_raw_inverse',
           'standard_states':len(seen),'exhaustive_count_words':exhaustive,
           'local_D_steps':steps,'raw_collision_counts':values,
           'seconds':round(time.monotonic()-started,3),'events':total.used['events'],
           'peak_rss_mib':round(GUARD.peak_mib(),2)})


def vectors():
    budget = spd.Budget(seconds=25,max_events=25000000,max_nodes=2500000,
                        max_slots=12000000,max_pairs=4000000,max_contexts=4000000,
                        max_columns=150,max_rows=15000000)
    cases = {}
    for m in range(4):
        for values in product(*(range(1,column_bound(j)+1) for j in range(m))):
            try:
                graph = decode_counts(values,budget=budget)
            except InvalidCounts:
                graph = None
            cases[values] = graph
    queue = deque(spd.seed(n,budget) for n in range(4))
    seen = set()
    additions = 0
    while queue and len(seen)<100 and additions<20:
        graph = queue.popleft()
        if graph in seen or len(graph)>6:
            continue
        seen.add(graph)
        values = spd.counts(graph,budget)
        if values not in cases:
            assert decode_counts(values,budget=budget)==graph
            cases[values] = graph
            additions += 1
        for n in range(4):
            child = spd.fs(graph,n,budget)
            if len(child)<=6:
                queue.append(child)
    print(json.dumps({'cases':[{'counts':values,'graph':graph}
                              for values,graph in cases.items()]},separators=(',',':')))


if __name__=='__main__':
    vectors() if '--vectors' in sys.argv[1:] else main()
