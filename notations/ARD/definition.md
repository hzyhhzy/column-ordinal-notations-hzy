# ARD: skyline edition — definition · [中文版](definition.zh-CN.md)

This is the repository's default ARD, an **exact alternative presentation of standard ARD**, not a stronger or weaker notation. The syntax remains `[column][column]…`, with triples `(anchor,parent,maximum root)`. Expressions usually become shorter because dominated records are removed. Column counts, local counting sequences, fundamental-sequence indices and the standard order type are preserved. The implementation operates directly on skylines; it does not reconstruct the original redundant graph.

The original [definition](../ARD-legacy/definition.md) and [well-ordering paper](../../proofs/paper/ard-legacy-well-ordering.md) provide the reference system. The new exact-compression lemma has a [paper argument](../../proofs/paper/ard-well-ordering.md), not a separate Lean formalization.

## Syntax, normalization and order

A finite term is a string of columns $G=(C_0,\ldots,C_{m-1})$. A record in column $j$ is $(k,p,q)$ with $0\le k,q\le p<j$. All three coordinates are addresses relocated during copying. Interpret $q$ as the maximum of the downward-closed roots $0,\ldots,q$, without explicitly enumerating them.

To normalize a column, first keep only the lexicographically greatest $(k,q)$ for each parent $p$. Scan parents in decreasing order and keep a record only when its pair is strictly greater than all previous pairs. Write $S$ for this operation. Thus parents strictly decrease and pairs strictly increase. Empty columns are retained. A column may have several incomparable records; retaining only its single greatest pair would be incorrect.

The zero term `∅` has no columns. Natural $m$ has $m$ empty columns. Compare columns lexicographically by record keys $(p,k,q)$, and compare terms lexicographically by columns. A proper prefix is smaller at either level. Adjoin a largest external term `Limit of ARD`.

The restriction $k\le p$ is stronger than the original raw parser's restriction, but every original standard term satisfies it. This simplification does not purport to cover original nonstandard inputs with $k>p$.

## Fundamental sequences

Set $0[n]=0$. For a nonzero term let $x=m-1$ and let $\partial G$ delete its last column. If $n=0$ or the last column is empty, return $\partial G$.

Otherwise the last record of $C_x$ is the control $e=(K,c,R)$. Put $L=x-c$ and let $\phi_b$ fix addresses below $c$ and add $bL$ to all other addresses. Apply it to all three coordinates of each record. Let $C_x^-$ delete the control record.

For a record $(k,p,q)$, its predecessor $\delta$ is the singleton $(k,p,q-1)$ if $q>0$, the singleton $(k-1,p,p)$ if $q=0<k$, and the empty set if $k=q=0$. Start with $\partial G$. For $b=0,\ldots,n-1$, append the block

$$
\left(
S\bigl(\phi_b(C_x^-)\cup\delta(\phi_b(e))\cup C_c\bigr),
\phi_{b+1}(C_{c+1}),\ldots,\phi_{b+1}(C_{x-1})
\right).
$$

Each block has $L$ columns. Its first column combines the seam with the beginning of the copied source block; these are not separate column positions. All references in $C_c$ lie below $c$, so it needs no relocation. Always relocate the control **before** taking its predecessor. These operations do not commute, including when $c=R=0$.

Use the original seeds: $A_0=0$, the first column of $A_n$ is empty, and its column $j>0$ is the singleton $(j-1,j-1,j-1)$. Set $\mathsf{Top}[n]=A_n$. The finite standard domain is the set of finite descendants of these seeds under the simplified rule. Structural legality alone does not imply standard reachability.

The old prefix preceding the last column is unchanged. Each $G[n]$ is a complete-column prefix of $G[n+1]$, strictly so for a nonempty last column. Every nonzero step strictly decreases column order. The rule uses finite loops only and does not recursively expand newly created terms.

## Exact equivalence and proof scope

Apply $S$ columnwise to obtain $Q$. On all original graphs satisfying $k,q\le p<j$,

$$
Q(G[n]_{\rm old})=Q(G)[n]_{\rm simplified}.
$$

The original lower-row package and lower-priority entries under the control parent reduce to their greatest surviving record, exactly $\delta$. Taking skylines commutes with union and strictly increasing relocation. These facts establish the displayed equation without assuming that the input is already a skyline.

The simplified standard domain is consequently the image of the original one. The original paper's reachability-comparison theorem says that two distinct standard terms are connected by a nonempty expansion path, oriented from larger to smaller. The displayed equation sends that path to a strictly descending simplified path, so its endpoints cannot merge. Hence $Q$ is an order isomorphism on the standard domains, preserving the entire indexed fundamental-sequence system and the order type.

The original ARD well-ordering result, including its paper upper bound $KP_\omega+$ “there exists an uncountable ordinal”, therefore transfers through this finite combinatorial correspondence. The new rule also has a direct ordinary Lean well-ordering proof; the full correspondence itself remains a paper result. There is no claim that arbitrary legal inputs are mapped injectively, that the compressed images are literally original-standard graphs, or that the whole raw column order is well-founded. No comparison with wY is established here.

## Counts, software and verification

Fixing the earlier columns, the local operation on a nonempty column is $T(C)=S(C^-\cup\delta(e)\cup C_p)$, where $e=(k,p,q)$ is its control. Its count is the number of local steps to the empty column plus the final deletion. Empty columns count as one. This operation commutes with $Q$, so counts match the original system. Seed counts remain the prefixes of `1,2,6,23,104,537,…`.

The exact `BigInt` counter jumps along previously computed skyline traces of earlier columns. It does not enumerate low-row packages, individual roots or globally expanded copied blocks. Resource-limit errors are explicit and never replaced by approximate counts.

Import [ARD.ne-rewritten.js](ARD.ne-rewritten.js) into the custom-notation facility of [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Select **ARD**, ID `ard-skyline-v01`; ARD-legacy can coexist under its different ID. Inputs include `A3`, `A3[2][1]`, `Limit[3]`, natural numbers and complete triple lists. Lists are validated and normalized. All three FS interfaces implement the same rule.

The five preserved displays are the column list, counting sequence, full arc diagram, textual adjacency table and graphical adjacency table. Graphs show all retained skyline records, not the omitted original edges. Compact triangular tables retain shaded diagonal indices and a count sequence above them. The script retains the approximate one-second shared checkpoint budget and the original finite drawing/text/size protections.

## Python and Lean

The readable [Python core](ard.py) uses only the standard library. From this directory:

```python
from ard import AnchoredRows, TOP
a = AnchoredRows.seed(3)
print(a[1])
assert a[0] == AnchoredRows.seed(2)
```

The [new Lean project](../../lean/ARD/README.md) proves well-founded expansion, well-ordering of the generated column order and the adjoined top. Its equivalent finite formulation selects the maximum `(k,q,p)`, filters strictly smaller `(k,q)` pairs, adds the moved controller's single predecessor, and normalizes each appended column. On skyline inputs the control is the last record, the filter deletes just that record, and normalization fixes relocated interior columns.

Lean checks these mathematical rules, not the JS/Python compilers. The complete legacy order isomorphism and cross-notation comparisons remain paper results. [NER tests](../../tests/ard_skyline.cjs) and [Python tests](../../tests/test_ard.py) check independent implementations, counts, comparison and full diagrams. See the [validation record](../../VALIDATION.md) for current results. Finite tests are not universal proofs or a fresh interactive browser acceptance test.
