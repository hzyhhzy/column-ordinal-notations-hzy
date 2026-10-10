# BTBMS comparisons and the adjacent-reader target · [中文版](btbms-comparisons.zh-CN.md)

Several high CDMN regions have concrete standard BTBMS carrier candidates. **None of the whole descendant embeddings in this table is complete.** BTBMS uses parent-index display, whose empty column is (0), unlike CDMN's ().

| CDMN source | BTBMS candidate | Proved finite structure |
| --- | --- | --- |
| A=()(1^(1)()) | B=(0)(1^(2,1^(3)),1) | B[n]=E(A[n]); exact positive second-layer simulation |
| K=[][0:W][1:W[]], W=[0:1] | PK=(0)(1^(2,1^(3)))(2^(3,1^(4)),2) | PK[n]=E(K[n]); PK=E(K)[1][0][1] |
| S3=Limit[3]=[][0:[0:[0:1]]] | P3=(0)(1^(2,1^(3)(4))) | P3[n]=E(S3[n+1]) |
| Entire standard CDMN | U=(0)(1^(2,2)) | Every finite seed image E(Sn) is standard below U; descendant closure is open |

K has three outer columns, whereas A has two; A's trailing empty column is inside its row. The [smaller T carrier](depth-and-tbms.md) strengthens earlier lower bounds: T<K<S3, so ordinary TBMS including its external top embeds into K's proper cone. This proves neither K's well-ordering nor an upper bound for K.

## The guard code

E maps each source column to one target column, carrying a strictly increasing address map. On entering a row, BTBMS includes the owner in its visible addresses while CDMN excludes it. The extra owner address is therefore omitted from the map of old source references.

Translate (p,R) to (f(p),E(R)). In an internal column that is empty or whose first real parent is below its owner o, prepend the bare guard (o,empty height). Do not add it when a local parent already leads the column. Add no outermost guards.

This finite, history-independent code preserves raw recursive lexicographic order. At the first difference, previous address maps agree. Local parents remain above the owner and external parents below it. External columns share the same bare guard; empty source columns become proper prefixes containing only that guard. Recursion handles row differences.

This establishes an injective raw syntactic order map, **not standardness of its images**.

## Exact formulas below A

Set \(W_j=[j:1]\), with 1 one empty column, and
\[
C_n=[][0:W_0]\cdots[n-1:W_{n-1}],\qquad C_0=[].
\]
Direct expansion gives
\[
A[n]=C_n\quad(n\ge0),\quad C_n[0]=C_{n-1}[]\quad(n\ge1),
\]
\[
C_1[m]=[][0:m]\quad(m\ge1),\quad
C_n[m]=C_{n-1}[n-1:([n-2:W_{n-2}])^{\frown m}]
\quad(n\ge2,m\ge1).
\]
Concatenation in the last formula leaves the old external references fixed.

The actual BTBMS paths are
~~~text
Limit[3][1][2][1][0][1][2][1][1][1][0]
    = E(A) = (0)(1^(2,1^(3))(2))
E(A)[1][0][1] = B.
~~~
B's bare outer control has empty root and span 1. Each transported seam shifts its parent and both guard layers equally. Hence, for all n≥0,
\[
\boxed{B[n]=E(A[n]).}
\]
For all n,m≥1,
\[
\boxed{E(A[n][m])=B[n][1][1][m-1].}
\]
The first 1 removes the innermost special guard. The second copies across the adjacent containing layer, leaving the correctly encoded seam and a bare stub. The final m−1 supplies the remaining copies. The donor is empty at n=1 and has one record otherwise, meeting the increasing-row hypothesis.

Zero children use finite right-pruning, not the old single-zero identity. For a fixed legal target pruning, take 0 when it retains that target, otherwise 1. On standard BTBMS terms, the owner/first-parent and span invariants prevent overshoot. The finite vector of extra-parent counts along the target's fixed right spine, followed by syntax size, strictly decreases. This terminates the strategy; it is not a well-ordering proof for arbitrary choices. For n=1, [0][0][1] is one correct path.

Thus A and every first/second-layer child have standard order-preserving images, mapping A to B and the others by E. This set is **not downward closed**, so it does not prove A≤B.

## Higher carriers and the missing closure

U=BTBMS Limit[3][1]. Each E(Sn) is a legal recursive right-pruning of a corresponding U child, proving standard seed images below one fixed carrier. P3 is a tighter exact envelope for the positive S3 family. Its formula does not identify the new source zero child with the old one.

A sufficient missing theorem is
\[
E(X)\longrightarrow_{\mathrm{BTBMS}}^*E(X[k])
\]
for every actual source descendant and index. Current local macros do not cover all combinations of cross-scope copying, a nonempty retained shell, unsorted donor rows and side branches. Raw legal nonstandard counterexamples to broader versions exist; they neither refute the standard-source conjecture nor permit removal of its standardness hypothesis.

The inverse guard code also fails to preserve standardness:
~~~text
E(S3)[1][1][1][0] = (0)(1^(2,1^(3)(4^(5))))
decode(...)       = [][0:[0:[][1:1]]].
~~~
The target is standard, while its decoded source lies strictly between S3 and all its children. Finite-reachability equivalence preserves this obstruction under the new zero rule. Cofinality is not equality, and increasing the proposed target cap cannot automatically make a nonstandard image standard.

## Bounded evidence

The saved A experiment checked 33 first-layer identities, 144 positive second-layer identities, 16 zero simulations and 1,802 deeper source edges, with 32,135 native target replays. Of those edges, 1,473 crossed scopes and 10 had non-increasing donors; maximum source depth was 14. There was 1 source resource unknown and 351 size/path skips. See the [original receipt](historical/adjacent-btbms-results.json).

These are historical bounded checks, not a fresh complete packaging replay or an exhaustive initial segment. Even a future complete embedding would require a separate well-ordering result for its target cone before establishing source well-ordering.
