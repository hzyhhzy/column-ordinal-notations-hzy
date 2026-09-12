# RPD: finite column diagrams — [中文版](definition.zh-CN.md)

Release definition, 2026-09-13. [PDF](definition.pdf) · [NER expander](RPD-mountain.ne-rewritten.js) · [Python](rpd.py) · [well-ordering proof](../../proofs/paper/well-ordering.md).

This defines the current column-ordered RPD, not the older path notation. An expression is its diagram; different construction histories do not create different expressions. Resource guards in software are not mathematical rules.

## 1. Finite syntax and root closure

A finite diagram is $G=(m,E)$, with columns $0,\ldots,m-1$ and a finite set of relations

$$
(k,q,p,j),\qquad k\in\mathbb N,\quad 0\le q\le p<j<m.
$$

Here $k$ is the row, $q$ the root, $p$ the parent, and $j$ the child column. Require downward closure in the root:

$$
(k,q,p,j)\in E\implies(k,u,p,j)\in E\quad(0\le u\le q).
$$

Write $\downarrow E$ for this closure. It adds smaller roots, not all smaller rows. Ignore duplicate relations but retain empty columns. The empty diagram $0=(0,\varnothing)$ is written `∅`; `[]` is one empty column and is different from $0$.

In list notation each pair of brackets is one column. A triple `(k,p,q)` means row, parent, maximum root; the child is determined by its column. A maximum root $q$ abbreviates all roots $0,\ldots,q$. Merge triples with equal $(k,p)$ by taking their maximum root. One may instead list all roots explicitly. The Python implementation stores all roots; the NER list compresses them. These are two encodings of the same diagram.

## 2. Comparison

For each column, sort its triples in decreasing order of the key $(p,k,q)$. Compare the resulting lists lexicographically by that key, then compare diagrams lexicographically from the leftmost column. A proper prefix is smaller at both levels. Equal diagrams are equal, independently of history. The compressed-root and all-root encodings give the same comparison.

Adjoin an external symbol $\Omega$, greater than every finite diagram. It is not a row label.

## 3. Fundamental sequences

The index $n$ is a nonnegative integer. Define two-column seeds

$$
S_n=\bigl(2,\{(k,0,0,1):0\le k\le n\}\bigr),\qquad \Omega[n]=S_n.
$$

Set $0[n]=0$; this identity is not a strict descent step. For nonempty $G$, let $x=m-1$ and let $\partial G$ delete column $x$ and all relations whose child is $x$. Then

$$
G[0]=\partial G,\qquad
G[n]=\partial G\text{ for every }n\text{ if the last column is empty.}
$$

For the remaining case $n>0$ with a nonempty last column, select the greatest last-column relation by the key $(k,q,p)$, and write it $(K,r,c,x)$. This control priority is **row, root, parent**, unlike the comparison priority **parent, row, root**. Put

$$
\ell=x-c>0,\qquad
\phi_b(i)=\begin{cases}i&i<c,\\i+b\ell&i\ge c,\end{cases}
\qquad E^- =\{(k,q,p,j)\in E:j<x\}.
$$

The map $\phi_b$ moves all three column indices of a relation, leaving its row fixed. For each seam $0\le b<n$, define

$$
\begin{aligned}
U_b=\{(k,u,\phi_b(p),x+b\ell):\;&(k,q,p,x)\in E,\quad 0\le u\le\phi_b(q),\\
&k<K\ \text{or}\ (k=K\text{ and }u<\phi_b(r))\}.
\end{aligned}
$$

The complete positive-index rule is

$$
G[n]=\left(x+n\ell,\ \downarrow\left(
\bigcup_{b=0}^{n}\phi_b(E^-)
\ \cup\ \bigcup_{b=0}^{n-1}U_b\right)\right).
$$

Thus the old last column is deleted; the source block $[c,x)$ occurs in its original position plus $n$ translated copies. There are $n+1$ copies in total. The seams retain lower rows and same-row smaller roots. There is no additional row-generation packet in RPD. All unions, loops and closure operations above are finite; no reachability test or semantic oracle is part of an expansion.

For finite $G$, $G[n]$ is a complete-column prefix of $G[n+1]$, a proper prefix when the old last column has relations. The columns before the old last column remain unchanged. The external top's sequence $S_n$ is not required to be a column-prefix chain.

## 4. Standard domain and well-ordering scope

The standard finite diagrams form the smallest set containing every $S_n$ and closed under every operation $G\mapsto G[n]$. The notation consists of this set together with $\Omega$. Structurally valid hand-written diagrams need not be standard. In particular, the theorem about the column order must not be extended to the entire raw syntax.

Every nonzero finite expansion is strictly smaller in column order. The seeds satisfy $S_{n+1}[1]=S_n$. The linked paper proves that the standard domain, with its top, is well ordered in $KP_\omega+\exists\text{ an uncountable ordinal}$. The accompanying Lean proof is an ordinary classical Lean proof, not an encoded derivation in that weak set theory. No comparison of order types with Y or LRD is claimed here.

## 5. Displays and local counts

The NER script provides lists, count sequences, operation traces and a full mountain diagram. Operation traces are provenance only. Counts are not comparison keys and are not an injective encoding of diagrams.

For column $j$, fix its left context $P$ and regard its relations $C$ as the last column. If $C\ne\varnothing$, perform any positive-index expansion, then discard all newly appended columns. Call the resulting relation set at position $j$ $T_P(C)$. Equivalently, if $(K,r,c,j)$ is the control,

$$
T_P(C)=C_c\cup\{(k,p,q)\in C:k<K\text{ or }(k=K\text{ and }q<r)\},
$$

Here $C$ and $C_c$ mean the full root-closed relation sets, not compressed maximum-root lists; $C_c$ is the source column's relations now attached to child $j$. When a compressed triple's maximum root is at least $r$, the formula can still retain its smaller roots below $r$. Define

$$
h_P(\varnothing)=1,\qquad h_P(C)=1+h_P(T_P(C))\quad(C\ne\varnothing).
$$

The final deletion of the empty column is included. This local process terminates: it strictly decreases the column order on subsets of a fixed finite collection of relations. A positive expansion decreases the number at the old last-column position by one and may append further numbers; index zero deletes the last number. A zero diagram displays `0`.

Examples:

| Term | Count sequence |
| --- | --- |
| $\Omega[0]$ | `1,2` |
| $\Omega[1]$ | `1,3` |
| $\Omega[1][2]$ | `1,2,5` |
| $\Omega[1][2][1]$ | `1,2,4` |

## 6. Running the expanders

Import `RPD-mountain.ne-rewritten.js` into NER's custom-notation control and select RPD. `FS`, `FS_alter` and `FS_short` use the same index convention. The file is copied unchanged from the current implementation; its display labels remain Chinese. Guards reject oversized work rather than returning a truncated mathematical answer.

Python 3.10+ needs only the standard library. From this directory:

```sh
python rpd.py 1 2
```

This prints $\Omega[1][2]$. Library example:

```python
from rpd import RPD, ZERO, TOP
a = TOP[1][2]
assert a < TOP[1]
assert a[0] == RPD(a.columns[:-1])
```

The library uses arbitrary-precision integers, has no protective truncation, and does not decide standardness. Very large expansions may exhaust available resources. The release's bounded tests compare Python with NER; they are not a proof of universal implementation equivalence.
