# Small ordinal locations in CTN · [中文版](small-ordinals.zh-CN.md)

Research dated 2026-09-27–28; renamed and packaged on 2026-10-01. This uses the [current CTN rules](definition.md), formerly CTN2, without changing the checker, domain or expansions. The following are paper calculations of **global strict-lower-set order types**, not estimates from sampled fundamental sequences. They have not been Lean-formalized.

| Ordinal | Raw expression | Status |
| --- | --- | --- |
| Finite m | m copies of `1` | Exact |
| ω | `12` | Exact |
| ω² | `12112112112112112112112112211212` | Exact; 32 columns |
| ω³ | `12112112112112112112221121122112211211211211211211211212` | Exact; 56 columns |
| ω^ω | F(g)2 from the [sparse table](fixtures/omega-omega.sparse.json) | [Paper argument](omega-omega.md); 69,593,927 columns |
| ε₀ | Not explicitly located | Existence in the well-founded part does not locate a finite expression |

Write F(a)=`encode_table(a)`, using **actual** table values: each aᵢ produces `1` followed by aᵢ+1 twos and then `1`. This already includes the positive coding and must not be incremented a second time.

## 1. The ω² expression

Let $s_2=(0,0,0,0,0,0,0,0,1,0)$. Its expression F(s₂)2 is eight `121` blocks, then `1221`, then `121`, then `2`. In the secondary block-count view it is

```text
2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,3,1,2,2
```

Those are 20 display groups, not the 32 actual columns.

The table passes, but every extension by one value fails. Address 0 fixes M(0,0)=0, address 6 fixes C(x=0)=0, and address 8 fixes V(x=0,x:=0)=1. The next address 10 is a comprehension test that must itself contain 0 and would require 0=1. Thus no natural-number choice works; this is a universal obstruction, not a bounded trial.

Every earlier alternative along s₂ fails immediately: encoded 0 is always terminal; the additional smaller actual value 0 at address 8 contradicts true arithmetic. The failed alternatives contribute eleven ω-chains before the entry, yielding

$$|F(s_2)|=\omega\cdot11+1.$$

All children of s₂ fail. From its entry to its cap there are ω successive ω-chains, so

$$|F(s_2)2|=(\omega\cdot11+1)+\omega^2=\omega^2.$$

Its indexed fundamental sequence is not the conventional ω·n sequence:

$$|\omega^2[0]|=\omega\cdot11+1,\qquad |\omega^2[1]|=\omega\cdot11+2,$$

$$|\omega^2[n]|=\omega\cdot(n+10)+1\qquad(n\ge2).$$

It is nevertheless cofinal in ω².

## 2. A local order-type formula

For a well-founded encoded table subtree at s, let δ(s) be the interval type from its entry inclusive to its cap exclusive. The kth branch contributes

$$B(s,k)=\begin{cases}
\delta(s^\frown k)+\omega,&s^\frown k\in U,\\
\omega,&s^\frown k\notin U,
\end{cases}\qquad \delta(s)=\sum_{k<\omega}B(s,k).$$

The final ω includes the cap's successor tail or the failed-child terminal tail; finite separator contributions are absorbed. Thus a leaf has δ=ω²; a node with exactly one leaf child has δ=ω²·2; and a node whose every positive-coded child has δ=ω²·2 has δ=ω³. Use the formula only after proving the relevant subtree well-founded.

## 3. The ω³ expression

Take

```text
s₃ = (0,0,0,0,0,0,2,0,1,1,0,0,0,0,0,0,0).
```

The only strictly longer accepted actual tables are s₃⌢(a) and s₃⌢(a,0), for arbitrary natural a:

1. Address 17 is a comprehension choice, so a is free. Address 18 is an invalid-scope witness and must be 0.
2. Address 11 chose row 0 for C(x=x), but address 0 made M(0,0)=0.
3. Address 16 consequently demands that address 19's V(x=x,x:=0) be 0.
4. Address 19's arithmetic clause demands 1. Every length-20 extension therefore fails, independently of a.

Each s₃⌢(a,0) is a leaf, and each s₃⌢a has exactly that one child. The local type is ω³.

For the global equality, earlier viable alternatives occur only at address 6 (choose 0 or 1 instead of 2) and address 9 (choose 0 instead of 1). All fail by address 10 and have only finitely many finitely branching table nodes before failure. They contribute types below a finite multiple of ω². All other smaller candidates fail immediately. Hence $|F(s_3)|<\omega^3$, and

$$|F(s_3)2|=|F(s_3)|+\omega^3=\omega^3.$$

## 4. Why ω^ω requires a different certificate

The preceding obstructions have fixed finite failure depths, so their local orders need only finite powers of ω. The [ω^ω construction](omega-omega.md) instead finds a table with extensions of every finite length, although each fixed next child has a finite failure bound. It also controls every earlier branch; a large local subtree alone would not establish a global equality.

The huge ω^ω word and the lack of an ε₀ location illustrate a limitation: cheap steps, simple successor recognition and a CK-sized well-founded part do not make familiar ordinal positions short or transparent. No extra Cantor-normal-form branch has been attached to disguise this.

## 5. Reproduction

[ctn_small_ordinals.py](../../tests/ctn_small_ordinals.py) checks encodings, displays, expansion formulas and the decisive addresses. [ctn_omega_omega.py](../../tests/ctn_omega_omega.py) checks the sparse artifact and its finite arithmetic certificates. Tests corroborate the implementation; they do not replace the universal arguments above.
