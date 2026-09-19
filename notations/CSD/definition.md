# CSD — Contextual Stack Diagrams · [中文版](definition.zh-CN.md)

Version: 2026-09-17; packaged 2026-09-20. **Global well-ordering is open. No actual infinite fundamental-sequence chain was found in the research records reviewed for this import.** This is not evidence that none exists. The [BMS embedding](../../research/order-comparisons/README.md) does not assume global CSD well-ordering.

[NER expander](CSD.ne-rewritten.js) · [Python core](csd.py) · [exact local clock](local_clock.py)

## 1. Syntax and order

A diagram is a finite sequence of columns. Column $j$ is a list of records $(p,W)$, with **strictly decreasing** parents $j>p_1>\cdots>p_s\ge0$. A word $W=(r;t_1,\ldots,t_m)$ has a head and a nonempty tail $(m\ge1)$; every word address lies in $0,\ldots,j$, including possible SELF $j$.

There is no sorting, deduplication, skyline or dominance cleanup. Duplicate or out-of-order parents are rejected. An example is `[][0:(1;1)][1:(2;2)]`. Zero has no columns; one has one empty column. The external top cannot be an address.

Compare words by $(r,m,t_1,\ldots,t_m)$, records by parent then word, columns lexicographically by their stored records, and diagrams lexicographically by columns. Proper prefixes are smaller. The control is the **last record** of the last column, not the record with greatest word.

## 2. Lowering a word in its actual context

For a current seam $N$ and its already constructed prefix $P$, let $R_N(D)$ be the flat address list starting with $N$, followed by every record's parent, head and tail, in stored order. For instance $R_2([0:(1;0)])=(2,0,1,0)$.

Lower an already transported $W=(r;t_1,\ldots,t_m)$ by the first applicable rule:

1. If the tail has a positive entry, decrement its rightmost positive entry and replace all entries to its right by $N$.
2. If the tail is all zero and $m>1$, replace it by $m-1$ copies of $N$.
3. If the tail is a single zero and $r>0$, replace the word by $(r-1;R_N(P_{r-1}))$.
4. Otherwise delete the word.

Rule 3 reads the actual output prefix, which can contain newly produced seams. Even SELF only reads $r-1<N$. It does not recursively expand that earlier column.

## 3. Fundamental sequence

Set $0[n]=0$. Index zero deletes the last column; an empty last column is deleted for every index.

Otherwise write $x$ for the last position and $(c,W)$ for its last record. Put $L=x-c$, $N_b=x+bL$, and

$$
\phi_b(i)=\begin{cases}i&i<c,\\i+bL&i\ge c.\end{cases}
$$

Start with the old prefix before $x$. For each $b=0,\ldots,n-1$:

1. Begin the seam with $\phi_b(C_x\text{ without its last record})$.
2. Lower $\phi_b(W)$ using the current output prefix; if it survives, append it at parent $\phi_b(c)$.
3. Directly concatenate $\phi_{b+1}(C_c)$, even if the control was deleted.
4. Append the seam and then copies $\phi_{b+1}(C_{c+1}),\ldots,\phi_{b+1}(C_{x-1})$.

All parent and word addresses move. In the source cut column, SELF $c$ becomes the current seam $N_b$. The three seam parts already have decreasing parents, so no cleanup is needed.

The result has $x+nL$ columns. It is a complete-column prefix of the next indexed result, and every nonzero expansion strictly lowers the column order. These finite facts do not prove global well-ordering.

## 4. Seeds and counts

Let $A_n$ have $n$ columns: column zero is empty and $C_j=[j-1:(j;j)]$. Define $\mathsf{Top}[n]=A_n$, including $A_0=0$. The standard domain consists only of finite descendants of these seeds.

A column's count freezes its prefix, locally lowers that column to empty, and adds one for deletion. The exact finite workload can be computed without iterating that many steps: [local_clock.py](local_clock.py) implements `Clock(prefix).work(column) + 1`.

More explicitly, at position $j$, let $s_j(t)$ be the zero-based shortlex rank of the nonempty tail over $0,\ldots,j$. Put

$$
\tau_j(r;t)=s_j(t)+1+\sum_{h<r}(s_j(R_j(C_h))+1).
$$

Rebind SELF $p$ in source column $C_p$ to $j$, and recursively set $H_p=\sum_{(u,W)\in C_p\text{ rebound}}\tau_j(W)(1+H_u)$. The count of $C$ is $1+\sum_{(p,W)\in C}\tau_j(W)(1+H_p)$. All dependencies have smaller parent addresses. This is a local finite counter, not a global descending rank.

## 5. Use and limits

Import the JS as **CSD** in NER. It has list and exact-count displays; inputs include `A3`, `Limit[3][2]`, `A3[2][0]`, and full lists. The three FS entry points use the same rule. Resource guards are implementation limits, not modifications of the mathematics.

From this directory:

```python
from csd import CSD
from local_clock import Clock
g = CSD.seed(3)
print(g[2])
print(Clock(g.columns[:-1]).work(g.columns[-1]) + 1)
```

The Python expansion kernel has no resource guards. Bound experiments externally. The known BMS lower bound, unproved global well-ordering, and failures of particular proposed embeddings are distinct statements; none is replaced by finite testing.
