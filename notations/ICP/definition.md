# ICP — Interpolating Copy Patterns · [中文版](definition.zh-CN.md)

Version: 2026-09-19; packaged 2026-09-20. **This version is not well-ordered.** From the standard term `S3[1][1][0]` (counts `1,2,5,10`), repeated `[1]` expansions form an infinite strict descending chain, of widths `4,7,10,13,…`. The [all-step manuscript](non-well-founded.zh-CN.md) proves the regenerating-tail identity. This package preserves the failed candidate for reproducibility; it is not a well-ordering claim.

[NER](ICP.ne-rewritten.js) · [Python](icp.py) · [bounded counterexample check](check_infinite_chain.py) · [valid low-segment comparisons](../../research/order-comparisons/README.md)

## 1. Expressions and order

A finite expression is a column sequence $A=(C_0,\ldots,C_{m-1})$. Column $j$ is a finite partial map $p\mapsto q$ with $0\le p,q<j$. The fields are parent and root addresses. **Do not impose $q\le p$.** Normalize duplicate parents by keeping the greatest root, and store records in decreasing parent order.

Lists use commas between records, for example `[][0:0][1:1,0:1]`. Zero has no columns; `[]` is one. Compare records by $(p,q)$, columns lexicographically, then diagrams lexicographically; proper prefixes are smaller. The external top is `Limit of ICP` and is not an address.

The control of a nonempty column is its record maximizing **$(q,p)$**. Expression comparison and control selection deliberately use different priorities.

## 2. Local lowering

Write $N$ for same-parent normalization. For control $(c,r)$, lower the current column by

$$
T_A(C)=N\left((C\setminus\{(c,r)\})\cup C_c
       \cup\begin{cases}\{(c,r-1)\}&r>0,\\\varnothing&r=0.\end{cases}\right).
$$

The old parent column is inherited; the root is decremented or its edge removed. Earlier columns are fixed. Parent $c$ decreases and all inherited parents are smaller, so the local column order strictly decreases.

## 3. One interpolating reflection

Set $R(A)=A$ for zero or an empty last column. Otherwise let $x=m-1$ and $(c,r)$ be the last control.

1. Start output $B$ with $(C_0,\ldots,C_{x-1},T_A(C_x))$.
2. Define the partial address map $\phi(p)=p$ for $p<c$ and $\phi(c)=x$.
3. Process each **original** source column $i=c+1,\ldots,x$ exactly once. Newly inserted columns are not additional sources.
4. Move both coordinates to form $V=N\{(\phi(p),\phi(q)):(p,q)\in C_i\}$.
5. If $V$ is nonempty with control $(a,b)$, start with the control parent of current output column $b$. Follow control parents to the left, collecting just the addresses greater than $a$, stopping at an empty column or an address at most $a$. List the collected addresses increasingly as $s_1<\cdots<s_t$. An empty $V$ gives an empty list.
6. Append $V$. For each $s_\ell$, let $v$ be the last position just appended, replace $V$ by $N(V\cup\{(s_\ell,v)\})$, and append that new $V$ too.
7. Set $\phi(i)$ to the final position of this source block. Continue with the next original source.

Parent lookup uses the **current output prefix**, not a frozen copy of the input. The resulting $\phi$ is strictly increasing, and every parent chain is finite. One reflection is finite even though repeated fundamental-sequence descent need not terminate.

## 4. Fundamental sequences and seeds

Let $\partial$ delete the last column, fixing zero. Define

$$
A[n]=\partial R^n(A).
$$

Thus $A[0]=\partial A$ and an empty last column is deleted at every index. A reflection changes only the work column and appends new columns, so $A[n]$ is a complete-column prefix of $A[n+1]$. Nonzero expansions strictly lower the specified column order.

Seed $S_h$ has $h+1$ columns: $C_0=\varnothing$ and $C_j=\{(p,j-1):0\le p<j\}$ for $j>0$. Set $\mathsf{Top}[n]=S_n$. Standard terms are finite descendants of these compatible seeds, not every syntactically legal graph.

```text
S1       = [][0:0]                          counts 1,2
S1[1]    = [][]                            counts 1,1
S1[2]    = [][][1:0]                       counts 1,1,2
S1[3]    = [][][1:0][2:1,1:0]              counts 1,1,2,4
S3[1][1][0] = [][0:0][1:1,0:1][2:1,1:1,0:2]
```

The last line is the standard start of the infinite chain, not an arbitrary raw counterexample.

## 5. Counts, interface and scope

Counts freeze each earlier prefix, iterate the local $T$ to an empty column, and add one for deletion. At position $j$ there are only $(j+1)^j$ normalized columns, and $T$ strictly decreases their finite order. Thus local counts are finite despite the global infinite chain.

Import the NER file and select **ICP候选**. Displays are list, exact count sequence and triangular adjacency table. Inputs include `S3`, `Limit of ICP`, `0`, and full lists; path strings such as `S3[1][1][0]` are not parser input. Obtain that path by clicking or calling the Python API. `FS`, `FS_alter` and `FS_short` coincide. Unknown counts are `?`, not approximate numbers.

From this directory:

```python
from icp import Budget, display, expand, seed
a = seed(3)
for n in (1, 1, 0):
    a = expand(a, n, Budget())
print(display(a))
```

Run `python -B check_infinite_chain.py` for the bounded regression. It supplements, not replaces, the symbolic infinite-chain argument. The packaged source changes only proof-status comments/help, not expansion rules. No global ordinal order type is assigned to ICP. The established correspondences below ICP `1,2` and `1,2,4` remain separate, valid local results in the archived manuscripts.
