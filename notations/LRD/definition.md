# LRD: ordinal-row column diagrams — [中文版](definition.zh-CN.md)

Release definition, 2026-09-13. [PDF](definition.pdf) · [NER expander](LRD.ne-rewritten.js) · [Python](lrd.py) · [well-ordering proof](../../proofs/paper/well-ordering.md).

This is the fixed polynomial-row LRD. Its top is an ordinary two-column seed, not an additional external symbol. The finite rules below do not use a well-ordering oracle or resource thresholds.

## 1. Rows and finite diagrams

Put $\Lambda=\omega^\omega$. Rows belong to

$$
L=\{\xi:\xi<\Lambda\}\cup\{\Lambda\}.
$$

Below $\Lambda$, write each row uniquely as a finite polynomial $\omega^d a_d+\cdots+\omega a_1+a_0$, with natural-number coefficients and no leading zero coefficient except for zero itself. Compare these polynomials by degree, then lexicographically from the highest coefficient. $\Lambda$ is greater than every polynomial.

A finite graph is $G=(m,E)$ with relations

$$
(\xi,q,p,j),\qquad \xi\in L,\quad 0\le q\le p<j<m.
$$

The fields are row, root, parent, child. Require root closure: with a relation of root $q$, include every otherwise identical relation of root $u\le q$. The closure operator $\downarrow$ only adds smaller roots, not smaller rows. Duplicate relations are ignored; empty columns are retained.

The empty graph is $0$, printed `∅`; a single empty column is `[]`. A list triple `(row,parent,maximum_root)` in column $j$ abbreviates all roots from zero through its maximum. Merge equal `(row,parent)` groups by maximum root. For example, `[][(w,0,0)]` has two columns and one nonempty column. A graph, not its construction history, is the identity of a term.

## 2. Row approximations and generation packets

For every $t\in\mathbb N$, define

$$
\begin{aligned}
0\langle t\rangle&=0,\\
(\beta+1)\langle t\rangle&=\beta,\\
(\beta+\omega^d)\langle t\rangle&=\beta+\omega^{d-1}(t+1)\quad(d\ge1),\\
\Lambda\langle t\rangle&=\omega^{t+1}.
\end{aligned}
$$

The third case applies to a nonzero limit polynomial: remove one copy of its last nonzero Cantor monomial $\omega^d$ to obtain $\beta$. Equivalently, for coefficients $(a_0,\ldots,a_d)$, find the least index $e$ with $a_e>0$, decrease $a_e$ by one, and, when $e>0$, set $a_{e-1}=t+1$. Remove leading zero coefficients. Every nonzero row has a strictly smaller approximation.

For seam number $b$, the generation packet is the finite set

$$
P_b(K)=\begin{cases}
\varnothing&K<\omega,\\
\{0\}\cup\{K\langle t\rangle:0\le t\le b\}&K\ge\omega.
\end{cases}
$$

The upper bound is $b$, inclusive. Duplicates in the packet are removed. Finite rows generate no new rows.

## 3. Expansion rule

Set $0[n]=0$, which is not a strict descent step. For nonempty $G$, write $x=m-1$ and let $\partial G$ delete the last column and its incoming relations. Set $G[0]=\partial G$. If the last column is empty, set $G[n]=\partial G$ for all $n$.

Otherwise let $n>0$. Choose the greatest last-column relation by $(\xi,q,p)$ and write it $(K,r,c,x)$. Set

$$
\ell=x-c>0,\qquad
\phi_b(i)=\begin{cases}i&i<c,\\i+b\ell&i\ge c,\end{cases}
\qquad E^- =\{(\xi,q,p,j)\in E:j<x\}.
$$

When applying $\phi_b$ to a relation, move its root, parent and child indices, but not its row. Define the ordinary and generated seams by

$$
\begin{aligned}
U_b=\{(\xi,u,\phi_b(p),x+b\ell):\;&(\xi,q,p,x)\in E,\quad0\le u\le\phi_b(q),\\
&\xi<K\text{ or }(\xi=K\text{ and }u<\phi_b(r))\},\\
V_b=\{(\delta,u,\phi_b(c),x+b\ell):\;&\delta\in P_b(K),\quad0\le u\le\phi_b(c)\}.
\end{aligned}
$$

Then the complete rule is

$$
G[n]=\left(x+n\ell,\ \downarrow\left(
\bigcup_{b=0}^{n}\phi_b(E^-)
\ \cup\ \bigcup_{b=0}^{n-1}(U_b\cup V_b)\right)\right).
$$

All the sets here are finite. There are $n+1$ occurrences of the source block, including the original. The generated packet is attached to the translated control parent, with all allowed roots. Root closure after translation fills any skipped root indices.

## 4. Column order, seed and standard domain

In each column, sort the maximum-root triples $(\xi,p,q)$ in decreasing order of $(p,\xi,q)$. Compare those lists lexicographically using that key, then compare graphs from the leftmost column. Proper prefixes are smaller at both levels. Explicitly expanding all small roots gives the same comparison.

The control edge uses priority **row, root, parent**; the order uses **parent, row, root**. They must not be interchanged.

The seed is

$$
T=\bigl(2,\{(\Lambda,0,0,1)\}\bigr).
$$

Its list is `[][(w^w,0,0)]`. The standard domain is exactly the graphs reachable from $T$ by a finite expansion path, including $T$. There is no extra external top. In particular, $T[0]=[]$ and $T[0][0]=0$. A constructor or parser only checks finite graph structure; it does not establish membership in this standard domain.

For finite $G$, all columns before its old last column are unchanged by expansion. $G[n]$ is a complete-column prefix of $G[n+1]$, proper when the old last column has relations; every nonzero expansion decreases column order. If all row labels are finite numbers, the expansion rule agrees with current RPD on that diagram. This does not by itself prove an initial-segment relation between the notation systems.

The linked paper proves the standard-domain order well founded in $KP_\omega+\exists\text{ an uncountable ordinal}$. The release also contains the ordinary classical Lean proof; it is not an encoded weak-set-theory derivation. Neither a minimal axiom strength nor an order-type comparison is asserted here.

## 5. Local counts and displays

The NER file has a lossless one-line list view, a count-sequence view, and a mountain view. The count sequence is presentation only: different graphs may have the same sequence, and the sequence is not the comparison key or an accepted inverse encoding.

For each column, hold the left prefix fixed, treat that column as last, expand with any positive index, and discard newly appended columns. Repeat this fixed-width local operation until the column has no relations, then delete it. Its count is the number of local operations including that last deletion. An empty relation column has count one. At the retained position only seam $b=0$ is relevant, so all positive indices give the same local operation, including the packet $P_0(K)$.

The displayed counts are exact when completed; a computational limit is reported as incomplete rather than silently truncating the result. Count termination is a local property and must not be used alone to establish global expansion termination.

| Term | Count sequence |
| --- | --- |
| $T$ | `1,5` |
| $T[1]$ | `1,4` |
| $T[2]$ | `1,4,19` |
| $T[2][1]$ | `1,4,18` |

## 6. Software use

Import `LRD.ne-rewritten.js` into NER's custom-notation control and select LRD. The three interfaces `FS`, `FS_alter` and `FS_short` are identical. The script is copied unchanged, including its Chinese display labels and resource guards. Guards are operational safeguards, not additional mathematical cases.

The independent Python definition needs Python 3.10+ and no third-party packages. From this directory:

```sh
python lrd.py 2 1
```

This starts at $T$ and prints $T[2][1]$. Library example:

```python
from lrd import Row, LRD, T
assert Row((0, 0, 1))[2] == Row((0, 3))  # (w^2)[2] = w*3
a = T[2]
assert a < T
assert a[0] == LRD(a.columns[:-1])
```

`Row((a0,...,ad))` stores coefficients in increasing degree; `Row(None)` is $\omega^\omega$. Integers have arbitrary precision. The Python library has no time, width or memory guard; very large expansions can exhaust resources. Release tests are deliberately bounded and cross-check the independent Python algorithm against the NER implementation.
