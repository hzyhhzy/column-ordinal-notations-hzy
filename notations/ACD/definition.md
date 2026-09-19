# ACD — Ancestral-Context Diagrams · [中文版](definition.zh-CN.md)

Version: 2026-09-18; packaged 2026-09-20. **Research candidate: global well-ordering is unproved.** This package adds a definition and implementations, not a well-ordering claim. The [comparison catalogue](../../research/order-comparisons/README.md) records the separate BMS and RPD low-segment results.

[NER expander](ACD.ne-rewritten.js) · [Python core](acd.py)

## 1. Columns and ancestral views

A finite expression is a sequence of columns $G=(C_0,\ldots,C_{m-1})$. At position $j$, a column is a finite partial map $p\mapsto h$ with $0\le p,h<j$. The two integers are a **parent address** and a **head-source address**; neither need be smaller than the other. Store records in decreasing parent order.

For column $i$, collect $i$ and the closure of all its parent and head references. Retain their original order and renumber them consecutively. This finite diagram is its **ancestral view** $V_i$. Preserve shared references: do not unfold it into a tree. An empty column has the one-empty-column view.

Lists use one pair of brackets per column and semicolons between records:

```text
[][0:0][1:0;0:0][2:1;1:0;0:0]
```

Addresses start at zero. `0` has no columns; `[]` is one. The external `Limit of ACD` is not a column or an address.

## 2. Comparison and merging

Compare diagrams lexicographically by columns. Compare a column's records in decreasing parent order, using the key $(p,V_h,h)$. Compare the views by the same recursive rule, with addresses renumbered inside each view. A proper prefix is smaller at either list level.

The recursion enters a strictly smaller ancestral diagram, so it terminates. This defines a total order, **not a proof that the order is well-founded**. When two records have the same parent, merging retains the larger head according to $(V_h,h)$.

## 3. Lowering the last column

Suppose the nonempty last column is at position $x$.

1. Choose its control record $(c,h)$ maximizing $(V_h,c)$.
2. Among all $k<x$ with $V_k<V_h$, choose the greatest view; break a tie by the greatest address $k$.
3. Replace the control by $(c,k)$, or remove it if there is no smaller view.
4. Merge in the old parent column $C_c$, resolving equal parents as above.

Call the resulting column $D$. No earlier column changes. This operation scans a finite prefix; it does not execute a whole fundamental-sequence descent to zero.

## 4. Reflection and fundamental sequences

Put $L=x-c$ and let $\phi(i)=i$ for $i<c$, and $\phi(i)=i+L$ otherwise. Apply $\phi$ to **both** fields of every copied record. A reflection is

$$
R(G)=(C_0,\ldots,C_{x-1},D,\phi(C_{c+1}),\ldots,\phi(C_x)).
$$

The last copied column is the **old** nonempty template, not $D$. Each subsequent reflection recomputes ancestral views and the control in its new actual context.

Let $\partial$ delete the last column. Set $0[n]=0$. If the last column is empty, set $G[n]=\partial G$; otherwise set

$$
G[n]=\partial R^n(G),\qquad n\in\mathbb N.
$$

Thus $G[0]=\partial G$ and $G[n]$ is a complete-column prefix of $G[n+1]$. The copied block need not be the same in successive reflections. Every nonzero expansion strictly lowers the specified column order; this alone does not establish global termination.

## 5. Seeds and the standard domain

The seed $S_n$ has $n+1$ columns: $C_0=\varnothing$ and $C_j=\{(j-1,j-1)\}$ for $1\le j\le n$. Define $\mathsf{Top}[n]=S_n$. Seeds satisfy $S_{n+1}[0]=S_n$.

**Only finite fundamental-sequence descendants of these seeds are standard.** A successfully parsed arbitrary diagram is not thereby certified standard.

```text
S1    = [][0:0]                         counts 1,2
S1[n] = n+1 empty columns
S2    = [][0:0][1:1]                    counts 1,2,4
S2[1] = [][0:0][1:0;0:0]                counts 1,2,3
S2[2] = [][0:0][1:0;0:0][2:1;1:0;0:0]  counts 1,2,3,5
```

## 6. Counts and use

For each column, freeze its earlier prefix, repeatedly apply the local lowering rule until empty, and add one for deleting that empty column. Empty columns have count one. This is **not** repeated expansion of the entire diagram. For a fixed position $j$, ordering the $j$ available head sources bounds the countdown by $(j+1)^j$; no unbounded-width well-ordering follows.

Import the complete JS file into NER's custom-notation facility and select **ACD候选**. It supports the full list, exact count sequence and full triangular adjacency table. Inputs include `S2`, `0`, `Limit of ACD`, and full lists. `FS`, `FS_alter` and `FS_short` share one rule. Budget exhaustion is not nontermination; unknown counts appear as `?` and never participate in comparison.

Python uses only the standard library. From this directory:

```python
from acd import ACD
g = ACD.seed(2)
print(g.fs(2))
print(g.counts())
```

The readable Python core has no automatic expansion budget. Keep indices and widths bounded; pass a bounded `tick` callback for expensive `counts` calls. No global well-ordering proof or claim that ACD exceeds e0MN, IPD or wY is included.
