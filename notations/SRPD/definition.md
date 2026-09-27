# SRPD: parent-list notation · [中文版](definition.zh-CN.md)

Packaged on 2026-09-28. SRPD, formerly RPD0, is a redundancy-free parent-list
presentation of RPD's zero-layer sector. It extracts a **common initial segment**,
not the whole RPD system and not a strength extension. The [NER](SRPD.ne-rewritten.js)
and [Python](srpd.py) implementations retain the 2026-09-26 implicit-root rules.

## 1. Expressions and the standard domain

The common root $C_0=[]$ is implicit. An expression is a finite sequence
$G=(C_1,\ldots,C_N)$ of columns. Column j is empty or a nonincreasing list
of h natural-number parent addresses satisfying

$$j>p_0\ge\cdots\ge p_{h-1}\ge h-1.$$

No visible columns denotes zero; one empty column denotes one. The fixed initial
expression is $S=([0])$, displayed as `2` in counts. **Only S and its finite
fundamental-sequence descendants are standard.** Parsing certifies raw syntax,
not standard reachability. The limit order type of SRPD means the strict
descendant domain of S; including S adds a greatest element.
The NER input `Limit` is an alias for this ordinary finite expression, not an external top.

## 2. The single expansion rule

The index n is a nonnegative integer. Zero stays zero. If n=0 or the last column
is empty, delete that column. Otherwise perform n reflections as follows, then
delete the temporary last column.

Let N be the current visible width, C its last column, h its length, c its last
parent, and $d=N-c$ the span.

1. Save moved copies of columns $c+1,\ldots,N$, using the rule below.
2. Replace the current last column by `C[:-1] + C_c[h-1:]`.
3. Append the saved copies.

To move a source column A, replace each parent $p\ge c$ by $p+d$, obtaining B.
If its zero-based position c exists, insert d extra copies of `B[c]` just before
that position. Otherwise insert nothing. Reading parent 0 returns the implicit
empty root; parent numbers need no renumbering.

```python
def expand(graph, n):
    if not graph or not n or not graph[-1]:
        return graph[:-1]
    result = graph.copy()
    for _ in range(n):
        column = result[-1]
        parent = column[-1]
        span = len(result) - parent
        source = result[parent - 1] if parent else []

        def move(column):
            moved = [p + span if p >= parent else p for p in column]
            return moved[:parent] + moved[parent:parent + 1] * span + moved[parent:]

        copies = [move(column) for column in result[parent:]]
        result[-1] = column[:-1] + source[len(column) - 1:]
        result.extend(copies)
    return result[:-1]
```

The full Python file also validates n. No RPD, e0MN or TBMS engine is called.
Deleting the temporary controller is essential. Each reflection changes only
the current last column and appends to the right, so $G[0]$ deletes the last
column and $G[n]$ is a whole-column prefix of $G[n+1]$.

| n | S[n] | Counts |
| --- | --- | --- |
| 0 | `0` | `0` |
| 1 | `[]` | `1` |
| 2 | `[][1]` | `1,2` |
| 3 | `[][1][2,2]` | `1,2,4` |
| 4 | `[][1][2,2][3,3,3]` | `1,2,4,8` |

Row insertion depends on the **source column having length greater than the
control parent c**, not on the last column being `[1]`. For example, the standard
term `[][1][2,2][3,3,3][2]` has child `[1]` equal to
`[][1][2,2][3,3,3][1][5,5][6,6,6,6,6,6]`.
See the [standard-path fixture](fixtures/completion-counterexample.json).
Deleting row insertion while moving only parent numbers changes standard
expansions, even their columnwise infinite limits.

## 3. Order, local lowering and counts

Compare columns from left to right; within a column use ordinary lexicographic
order on natural-number lists, with a proper prefix smaller. Every display
uses this same internal parent-list comparator. Prefix coherence and last-column
locality must be combined with standard reachability and strict descent;
raw syntactic legality alone does not prove well-ordering.

With the preceding columns fixed, local lowering is

$$C\longmapsto C[:h-1]\mathbin{\frown}C_c[h-1:].$$

It is realized by actual `[1]` followed by deletion of newly appended columns.
A column's count is the number of these local lowerings to reach the empty
column, plus its final deletion. It is neither the length of a full expansion
countdown nor the number of rows.

Exact dynamic programming avoids enumerating that long local countdown. Put
$T_0(t)=0$, and $T_j(t)=0$ beyond column j; otherwise

$$T_j(t)=T_j(t+1)+1+T_{C_j[t]}(t),\qquad \operatorname{count}(C_j)=T_j(0)+1.$$

All references point to earlier columns, so evaluate columnwise, with positions
in reverse order. Python integers and JS BigInt are exact. The arrays themselves
can still be large: the rules are shorter, but dense parent lists can use more
space than sparse `(parent, greatest root)` records.

## 4. Three NER views

The default list is the actual parent list. The equivalent-display menu adds
two views without duplicating the default entry.

* **Counts:** one exact local count per column; preserve a computed prefix and
  show `?` at uncomputed positions if the display budget is exhausted.
* **Height lists:** BMS-style node heights $H_j(r)=1+H_{C_j[r]}(r)$, with a missing
  cell assigned height 0.

For example `[][1][2,2][3,3,3]` becomes `[][1][2,1][3,2,1]` in heights.
These are same-row parent-chain lengths, not parents, root indices or counts.
Changing the display does not change the expansion rule to BMS.
Parent recovery at a higher row follows the next-lower-row parent chain to a
smaller height, rather than scanning that row for any nearest smaller entry.
A [standard counterexample](fixtures/height-naive-counterexample.json) records
the failure of the latter shortcut.

Height lists are not injective on all raw legal graphs: `[][1][1][2]` and
`[][1][1][3]` have the same heights. The display must recover and compare the
entire parent graph first, rejecting lossy cases; the parser also checks the
recomputed heights. Every successful display is therefore lossless.
**Universal coverage of the standard domain by this view remains unproved**;
bounded round trips are not that theorem.

## 5. Common initial segment and well-ordering

Write $\alpha_{\rm SRPD}$ for the order type strictly below S. With the finite
bottom and endpoint conventions in the recorded paper correspondences,

$$\alpha_{\rm SRPD}
=|\mathrm{RPD}(1,2)|
=|\mathrm{ARD}(1,1,3)|
=|\mathrm{ARD2}(1,1,3)|
=|\mathrm{IPD}(1,2)|
=|\mathrm{e0MN}(1,3)|.$$

Here e0MN is @test_alpha0's ordinary version. The specified newer strong e0MN
has endpoint `1,2`. These are common segments **strictly below** the indicated
terms, not the complete RPD/ARD/ARD2/IPD systems. Similarity of rules does not
automatically add LRD or Ω-LRD3 to this equality chain.

The [correspondence and well-ordering note](correspondence.md) gives the
coordinate projection and links the existing papers. Hiding RPD's first empty
column removes its leading count 1; old zero and old one both project to new
zero. A genuine order isomorphism needs the finite-bottom adjustment, not a
false claim that this raw projection is injective everywhere.
Ordinary M13 and SRPD have identical strict-descendant graphs and indexed
expansions, but at their endpoints

$$S[n+1]=\mathrm{M13}[n],\qquad S[0]=0.$$

Standard-domain well-ordering transfers through the paper correspondence with
the RPD low segment, retaining the repository's paper bound
$KP_\omega+\text{there exists an uncountable ordinal}$, with full set induction.
**No separate Lean theorem certifies the SRPD projection, the common-segment
comparisons, or the TBMS comparison.** Existing RPD Lean code does not by itself
certify this JS implementation.

## 6. Use, version and checks

Load the entire [JS file](SRPD.ne-rewritten.js) into the custom-notation facility
of [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/), and select SRPD.
Input `Limit`, `SRPD[4][1]`, a parent-list string, or a natural number denoting
that many empty columns. Count strings are not a supported inverse syntax.
The old `RPD0` path alias remains. Old explicit-root lists must lose their first
`[]`; registration ID `srpd-implicit-root-v02` prevents silent cache reinterpretation.

```sh
python -B notations/SRPD/srpd.py 4 1
node --max-old-space-size=512 tests/srpd.cjs
node --max-old-space-size=512 tests/srpd.cjs --python-cases | python -B tests/srpd_python.py
```

The JS one-second work budget, 8192-column cap and one-million-cell cap are
software guards, not mathematical axioms. The Python kernel has no expansion
size limit; batch callers must supply budgets. The [provenance manifest](provenance.json)
pins both implementations and fixtures. The [package checks](../../tools/srpd-validation.json)
separate completed, skipped and unvisited cases; they are not unrestricted
verification or a new browser-click acceptance test.
The [SRPD/TBMS research summary](../../research/srpd-tbms/README.md) records the
latest paper bounds and open candidates separately.
