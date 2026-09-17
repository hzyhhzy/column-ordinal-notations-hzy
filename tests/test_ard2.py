"""Bounded skyline/legacy audit; run with -B, optionally --vectors.

One process; 35 seconds, 48 output columns, 3500 stored states, 512 MiB RSS.
Imports both releases and the independent legacy atom oracle. No file writes,
network, background jobs, or unbounded full-FS descent.
"""
import importlib.util
import json
from collections import deque
from itertools import product
from pathlib import Path
import random
import sys
from time import monotonic

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
START = monotonic()

def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

new = load('skyline_ard2', 'notations/ARD2/ard2.py')
old = load('legacy_ard2', 'notations/ARD2-legacy/ard2.py')
oracle = load('ard2_atom_oracle', 'tests/test_ard2_legacy.py')

def tick():
    assert monotonic() - START < 35, '35-second audit ceiling'
    assert oracle.peak_rss_mib() < 512, '512 MiB RSS ceiling'

def independent_skyline(column):
    entries = set(column)
    return tuple(sorted((e for e in entries if not any(
        a != e and a[1] >= e[1] and (a[0], a[2]) >= (e[0], e[2])
        for a in entries)), key=lambda e:(e[1], e[0], e[2]), reverse=True))

def Q(columns):
    return tuple(independent_skyline(c) for c in columns)

def main():
    stats = dict(raw_graphs=0, standard_graphs=0, steps=0, atomic_steps=0,
                 local_steps=0, prefix_checks=0, standard_order_pairs=0)
    vectors=[]
    def verify(g, atomic=False):
        tick()
        qg=new.ARD2(g.columns)
        assert qg.columns == Q(g.columns)
        assert new.ARD2(qg.columns) == qg
        previous=None
        outputs=[]
        for n in range(4):
            if g.columns and g.columns[-1]:
                c=max(g.columns[-1],key=lambda e:(e[0],e[2],e[1]))[1]
                if len(g.columns)-1+n*(len(g.columns)-1-c)>48:
                    break
            original=g[n]
            simplified=qg[n]
            assert simplified.columns == Q(original.columns), (str(g),n)
            if atomic:
                assert simplified.columns == Q(oracle.atomic_step(g.columns,n))
                stats['atomic_steps']+=1
            assert simplified < qg if qg.columns else simplified == new.ZERO
            if previous is not None:
                assert simplified.columns[:len(previous.columns)] == previous.columns
                stats['prefix_checks']+=1
            previous=simplified
            outputs.append(original)
            stats['steps']+=1
        assert qg.local_step().columns == Q(g.local_step().columns)
        assert qg.local_step().columns == qg[1].columns[:len(qg.columns)]
        stats['local_steps']+=1
        if len(vectors)<180:
            vectors.append({'raw':str(qg),'outputs':[str(new.ARD2(v.columns)) for v in outputs]})
        return outputs

    for roots in product(range(-1,2),repeat=2):
        verify(old.ARD2(((),tuple((k,0,q) for k,q in enumerate(roots) if q>=0))),True)
        stats['raw_graphs']+=1
    rng=random.Random(20260917)
    for i in range(800):
        cols=[]
        for j in range(rng.randrange(1,13)):
            cols.append(tuple((rng.randrange(j+1),rng.randrange(j),rng.randrange(j+1))
                              for _ in range(rng.randrange(3*j+1))))
        verify(old.ARD2(tuple(cols)),i<60)
        stats['raw_graphs']+=1

    queue=deque(old.ARD2.seed(n) for n in range(9))
    seen={g.columns for g in queue}
    standards=[]
    while queue and stats['standard_graphs']<1200:
        g=queue.popleft()
        outputs=verify(g)
        standards.append(g)
        stats['standard_graphs']+=1
        for child in outputs:
            if len(child.columns)<=20 and child.columns not in seen and len(seen)<3500:
                seen.add(child.columns);queue.append(child)
    ordered=sorted(standards)
    for a,b in zip(ordered,ordered[1:]):
        assert a<b and new.ARD2(a.columns)<new.ARD2(b.columns)
        stats['standard_order_pairs']+=1

    counts=[]
    for width in range(1,6):
        g=new.ARD2.seed(width)
        legacy=old.ARD2.seed(width)
        for value in range(30000):
            if value%128==0: tick()
            assert g.columns==Q(legacy.columns)
            if len(g.columns)<width:
                counts.append(str(value));break
            g=g.local_step();legacy=legacy.local_step()
        else: raise AssertionError('30000 local-step ceiling')
    assert counts==['1','5','55','969','23751']
    for n in range(9):
        assert new.TOP[n]==new.ARD2.seed(n)
        if n: assert new.ARD2.seed(n)[0]==new.ARD2.seed(n-1)
    assert str(new.TOP)=='Limit of ARD2'
    assert str(new.ARD2.seed(2)[1])=='[][(1,0,0)]'
    assert str(new.ARD2.seed(2)[1][1])=='[][(0,0,1)]'
    for invalid in ((((0,0,0),),), ((),((2,0,0),)),((),((0,0,2),)),
                    ((),((0,1,0),)),((),((True,0,0),))):
        try: new.ARD2(invalid)
        except ValueError: pass
        else: raise AssertionError('Invalid input accepted')
    summary={'ok':True,**stats,'seed_counts':counts,'queued_unexplored':len(queue),
             'seconds':round(monotonic()-START,3),'peak_RSS_MiB':round(oracle.peak_rss_mib(),2),
             'limits':{'seconds':35,'width':48,'stored_states':3500,'RSS_MiB':512}}
    if '--vectors' in sys.argv:
        comparisons=[{'a':str(new.ARD2(a.columns)),'b':str(new.ARD2(b.columns)),
                      'expected':-1} for a,b in zip(ordered[:150],ordered[1:151])]
        print(json.dumps({'summary':summary,'cases':vectors,'comparisons':comparisons,
                          'counts':[{'raw':'[][(1,0,1)][(2,1,2)][(3,2,3)][(4,3,4)]',
                                     'expected':counts}]}))
    else: print(json.dumps(summary))

if __name__=='__main__': main()
