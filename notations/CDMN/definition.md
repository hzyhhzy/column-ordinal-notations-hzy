# CDMN Compact Deep Mountain Notation · [中文版](definition.zh-CN.md)

Updated October 10, 2026 to the prefix-zero rule. **Global well-ordering is open. No standard infinite descent has been found for this rule. There is no Lean well-ordering proof or established axiom upper bound.** Strict decrease and adjacent retreat do not imply well-ordering.

[NER expander](CDMN.ne-rewritten.js) · [Python core](cdmn.py) · [Finite properties and BMS lower bound](../../proofs/paper/cdmn-properties.md) · [Research status](../../research/cdmn/README.md) · [Provenance](provenance.json)

## 1 Finite graphs and scope

A graph is a finite column sequence $G=(C_0,\ldots,C_{s-1})$. A column is a finite list of records $(p,R)$: p is a nonnegative parent address, and R is a nonzero graph of the same kind. Parents strictly decrease within each column; **rows need not increase**. Zero is the empty graph, written `0`; one is a single empty column, written `[]`.

Relative to an external context Γ, local column j has address $|\Gamma|+j$. Its parents must be smaller. Each row sees Γ followed by the preceding j local columns, **excluding the entire column that owns that row**. Its own local columns start at that same address. Addresses belong to scopes, not to a global preorder numbering of the whole syntax tree.

For example, a row in outer column1 has its local column0 at address1, but cannot read its outer owner. Its local column1 may read its own preceding local column0.

The list `[][0:3]` has an empty first column and then parent0 with row3. A number k used as a row abbreviates k empty columns, so its full form is `[][0:[][][]]`. **This is not a count sequence.** There are no `@` sharing names or suspended computations.

## 2 Comparison and relocation

Compare records by parent and then recursively by row; compare columns by their record lists and graphs by their column lists. Proper prefixes are smaller at every level. This finite syntactic comparator agrees with reachability on the standard domain; the raw legal lexicographic order is not asserted to be well founded.

Relocation at cut c by distance d adds d to every parent address p≥c, recursively throughout all rows, and fixes smaller addresses. It does not change column, record or nesting shapes. In particular, finite natural rows do not increase during relocation.

## 3 Prefix-zero pruning

Zero remains zero, and an empty final column is removed at every index. Otherwise inspect the final record's row R:

- If R ends in a nonempty column, recursively take R[0] and replace only that row; remove its record if the result is zero.
- If R ends in an empty column, this is the active copy layer. Delete its **whole final column**, including all its records.

Thus index zero deletes one whole column at the active layer, not necessarily at the outermost layer. It strictly reduces finite syntax, but may delete many nested column occurrences. For example,

```text
[][0:2][1:2][0] = [][0:2]
[][0:[0:1]][0]  = [][]
```

The last `[0]` on each left-hand side is an operation index. Positive indices retain their original meaning: **there is no index shift**. In particular, `()(1^2)[1]=()(1)` is not skipped.

For comparison with the previous rule, write δ for the separate hereditary trim that recursively deletes just one innermost column occurrence. In general $G[0]\ne\delta G$. The [finite-properties proof](../../proofs/paper/cdmn-properties.md#2-hereditary-trim-and-prefix-zero) constructs finite simulations in both directions. Consequently the old and new rules have the same finite reachable graphs and the same standard order, without assuming global well-ordering. This is not same-index fundamental-sequence equality.

## 4 Positive expansion

Let n>0 and suppose the final column is nonempty. If its final record's row ends in a nonempty column, recursively expand that row and only replace the result in its owner. Continue to the unique deepest active position. **There is no additional outer copying in the same step.**

At that position let the visible columns be $C_0,\ldots,C_m$, with control $(c,R)$, R ending in an empty column, and $d=m-c>0$. Put

$$
\phi_t(p)=\begin{cases}p,&p<c,\\p+td,&p\ge c.\end{cases}
$$

Apply these maps recursively to all parent addresses:

1. Remove the last empty column of R to obtain $R^-$. Replace the control row by it, or delete the control if it becomes zero. **Retain every other record.** Call this lowered column L.
2. Start Q=L and let H be the largest row in Q, or zero if Q is empty. Scan the source column $C_c$ in stored order. A source record $(p,U)$ has p<c, so its parent stays fixed. Append $(p,\phi_1(U))$ only if $\phi_1(U)>H$, then update H to that row. Equality is rejected.
3. Form the fixed block of d columns

$$
B=(Q)\mathbin{\|}\phi_1(C_{c+1},\ldots,C_{m-1}).
$$

Retain the active graph's old prefix before its last column and append

$$
B\mathbin{\|}\phi_1(B)\mathbin{\|}\cdots\mathbin{\|}\phi_{n-1}(B).
$$

Every source existed before this active operation. Newly produced seams are not recursively expanded during the same call. Insert the result back into the unchanged enclosing syntax.

At an active outer copy layer, all $G[n]$, including $G[0]$, are literal column prefixes of $G[n+1]$. At an enclosing layer the same prefix property holds inside the active row; the outer columns need not be literal prefixes. In either case there is a finite actual expansion path from $G[n+1]$ to $G[n]$. Such a path may use both indices 0 and 1, not only zeros.

## 5 Top and standard domain

Let $R_0=1$, $R_{k+1}=[0:R_k]$, $S_0=1$, and $S_n=[][0:R_{n-1}]$ for n≥1. In particular S0 is not zero.

```text
S0 = []
S1 = [][0:1]
S2 = [][0:[0:1]]
S3 = [][0:[0:[0:1]]]
```

The external top `Limit of CDMN` has nth fundamental term Sn. Standard finite graphs are precisely the finite descendants of these seeds. A legal hand-written graph is not automatically standard. Until well-ordering is established, the top is a generation entry, not a certified ordinal.

## 6 Representative expansions

```text
S2[3]       = [][0:3]
S2[3][2]    = [][0:2][1:2]
S3[2][2]    = [][0:[0:1][1:1]]

S3[2][2][1][1][0][2][1][1]
             = [][0:[0:1]][1:[0:[][2:[2:1]]]]

S2[4][2][1][1][0][1][0]
             = [][0:3][1:2;0:1]
```

The penultimate graph exceeds its seed's nesting depth. The last graph has active row1 below retained row2. Both are genuine standard phenomena that a well-ordering argument must handle, not counterexamples by themselves.

## 7 Established and open claims

The [finite-properties paper](../../proofs/paper/cdmn-properties.md) gives self-reviewed arguments for legality preservation, strict decrease, finite adjacent retreat $G[n+1]\to^*G[n]$, standard-domain comparability, and the one-step fully unfolded syntax bound for closed inputs

$$\operatorname{size}(G[n])\le(n+1)\operatorname{size}(G)\quad(n\ge1).$$

This is not a uniform bound after arbitrarily many steps. The earlier embedding includes the whole ordinary BMS standard order below S2; that embedding alone does not establish equality. A separate [sibling-code paper](../../research/cdmn/papers/s2-equals-bms.md) gives `S2=()(1^(1))=lim(BMS)` and `[][0:h]=BMS(0^h)(1^h)` for every h≥1, including `()(1^3)=BO`. These are self-reviewed exact order-type arguments, not same-index FS identities or Lean certification. Later local well-ordering and comparison results, including their proof status and remaining gaps, are collected in the [research status](../../research/cdmn/README.md). Whole-system comparisons with RPD, the ARD family, SRPD, Y, wY, ordinary e0MN and strong e0MN remain unfinished.

The [dilation lemma](../../research/cdmn/dilation.md) supplies a sufficient self-replication certificate for infinite descent, but no instance is known. The earlier notations' weak-KP upper bound is not inherited by CDMN.

## 8 Implementations and use

Load the complete [CDMN.ne-rewritten.js](CDMN.ne-rewritten.js) in [NER](https://smilelee-lyx.github.io/ne-rewritten/)'s custom-notation feature and select CDMN. Inputs include `S3[2][2]`, `Limit[3]` and explicit graphs. There are four views: **BTBMS-style (default)**, List, Full List and Count Sequence; no mountain view is supplied. `FS`, `FS_alter` and `FS_short` use identical rules and indices.

The default view uses parentheses for columns and commas for records. A parent address p is displayed as p+1, with its recursively formatted row graph as a superscript; row1 omits the superscript. Natural rows remain decimal numbers and empty columns are `()`. Thus `[][0:3][1:2;0:1]` appears as $()(1^3)(2^2,1)$, while `[][0:[0:1]]` appears as $()(1^{(1)})$. These superscripts are structural labels, **not ordinary exponentiation or a translation into BTBMS**.

Copyable plain text uses `^`, for example `()(1^3)(2^2,1)` and `()(1^(1))`; braces such as `()(1^{(1)})` are also accepted. The first three views accept the new syntax as well as the existing square-bracket lists and seed paths. Count Sequence has no inverse numeric parser: arbitrary legal nonstandard graphs need not have unique counts. The internal canonical strings and FS outputs stay in the original square-bracket format, so this view does not change comparisons, expansions, scope or mathematical rules. The definitions and examples above use the original List view.

Count Sequence displays integer columns only when **every row graph is a natural number**, equivalently when BTBMS-style superscripts contain no parentheses. Nested rows, the external top, or a counting resource limit cause the whole expression to fall back to the original BTBMS-style rendering, without question marks or approximate numbers. Fallback does not prove that finite counts are impossible in every larger region.

In Python a graph is a tuple of columns; a column is a tuple of `(parent,row)` pairs. The independent core exports `seed(n)`, `fundamental(graph,n,context=ZERO)`, `prune(graph)`, `relocate(graph,cut,distance)` and `legal(graph,base=0)`. Tuple comparison is the recursive lexicographic order. Python integers are arbitrary precision and the mathematical core has no artificial cutoff; callers must bound their experiments.

The JS factory is `createCDMN`, with safe-integer addresses. NER retains time, event, width, depth, cache and output-length guards. Exhaustion raises an error, never a truncated expression, and does not mean nontermination. Parsing or comparison does not certify standardness.

The self-contained bundle is deterministically built from local sources with `node notations/CDMN/build-ner.cjs`; add `--check` for a read-only check. Reproduction commands and finite validation scope are in the [repository validation record](../../VALIDATION.md).

## 9 Exact counts in the natural-row fragment

Freeze the prefix before column j. Replace this column by the **first seam column** of a positive-index expansion, discarding newly copied columns after it. Repeat until the column is empty, and include one final empty-column deletion. This defines its count; an empty column counts as 1 and the zero graph displays `0`. It is not repeated `[1]` expansion of the entire expression.

This fragment is closed under expansion. If all row heights are at most H, the fixed-prefix column has at most $(H+1)^j$ possible states. Every seam step strictly decreases their finite lexicographic order and keeps heights bounded by H, so the local count is finite without assuming global CDMN well-ordering. A positive-index expansion's first new column loses exactly one count; **index zero may skip several counts**.

For example, `()(1^3)` displays `1,4`, and its second term `()(1^2)(2^2)` displays `1,3,7`. The latter's first fundamental term has first-seam count 6, whereas its zeroth term deletes the whole last column and displays `1,3`. The count assigned to a fixed graph is unchanged by the new zero-index convention.

The implementation uses BigInt dynamic programming, not enumeration of a potentially huge countdown. Let $K_p(f)$ be the work needed to clear the strictly increasing records selected from donor column p above threshold f, excluding outer-column deletion. With a retained shell whose maximum row is f, the work to clear an appended record $(p,h)$ is

$$W(p,h,f)=h+\sum_{k=0}^{h-1}K_p(\max(f,k)).$$

A column's total work is the sum of W over its records, using the maximum height of preceding records for f. Likewise $K_p$ sums W over the filtered donor records. All donor references point to parents smaller than p, so tables are built from left to right. Prefix sums of $K_p$ evaluate the entire displayed sum at once. Add 1 to obtain the final column count.

The counter independently allows about 180 milliseconds, 250,000 work units and 80,000 table/record cells. Exhaustion affects this display only, not expansion or comparison. An [independent replay test](../../tests/cdmn_counts.cjs) checks actual first-seam transitions, integers beyond $2^{63}$, nested-row fallback and resource fallback. These are display-algorithm and finite-property results, not a global well-ordering proof.
