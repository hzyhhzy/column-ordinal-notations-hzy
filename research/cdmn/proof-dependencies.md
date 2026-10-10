# CDMN proof dependencies and standard entries · [中文版](proof-dependencies.zh-CN.md)

The new work separates complete-cone well-ordering, order-type comparisons, finite identities and bounded experiments. All added mathematical results are self-reviewed paper arguments, not additions to the Lean-certified notation inventory.

## Rule version and finite interfaces

The current prefix-zero rule deletes the entire last column at the active copying layer; enclosing recursive layers only replace their active row. Positive indices are unchanged. The earlier deep-zero rule removed an innermost empty column. Individual zero children generally differ.

The [finite-properties paper](../../proofs/paper/cdmn-properties.md) and [definition](../../notations/CDMN/definition.md) specify the current interfaces. The later cleanup argument supplies, in every legal context: finite erasure of the last record while preserving its prefix; lifting of a supplied finite row path; and mutual finite simulation of the two zero rules. Thus reachable domains and orders coincide without assuming global well-ordering.

Cleanup inducts first on the control parent c, then on the remaining row size. A nonempty final row column is reduced recursively. An empty one is handled by [1], width restoration, and removal of donor records whose parents are strictly smaller than c. Returning to the original control reduces its row. This is a finite nested induction, not termination inferred from an unknown lexicographic well-order.

Old path indices cannot consequently be relabeled as new certificates, and old delta is not one current [0]. See the [versioned historical index](historical/README.md).

## The complete-cone paper chain

The existing [fixed countable-row reflection theorem](../../proofs/paper/well-ordering.md) provides finite generated-package representations independently of global CDMN well-ordering. The six imported full Chinese papers then establish:

1. Cumulative power-sum labels, a precise closed row library and protected components.
2. Separated known macros and visible ports, without assigning unknown ranks to macro interiors.
3. Parameter-independent driver induction for every finite type.
4. Coherent families as new proof objects, with row-2 heads only at justified boundaries.
5. Predicates defined first along \(\omega h+k\), then a common endpoint of all finite family layers.
6. Uniform-family transformations and complete mixed-port pairs, yielding R∞.

English companions are explicitly abridged. Historical statements such as an earlier paper's open H are superseded by the later papers; they are not the current boundary. Named experimental tools are source records, not a claim that their whole dependency tree was ported.

## BMS equality

The [full sibling-code paper](papers/s2-equals-bms.md) assumes known ordinary BMS well-ordering and proves
\[
[][0:h]=\mathrm{BMS}(0^h)(1^h)\quad(h\ge1),\qquad
S=()(1^{(1)})=\lim(\mathrm{BMS}).
\]
This is a nodewise cofinality and well-founded-rank argument, not same-index expansion identity. Its local zero-equivalence is covered by the stronger general finite interface above. No higher nested equality follows.

## The TBMS and BTBMS interfaces

The [archived TBMS endpoint-closure manuscript](../srpd-tbms/archive/output/tbms-e0mn-bridge-20260925/RECURSIVE-ENDPOINT-CLOSURE.zh-CN.md) supplies canonical parent tables, source comparability, lower-level endpoint-forest closure and the two nontrivial source-step formulas. Its source well-foundedness comes from earlier SRPD carrying arguments, not CDMN's open global problem.

The [depth and TBMS outline](depth-and-tbms.md) also states its base open-root code, successor completion and finite row-lifting interfaces. It preserves the construction but does not claim to port every historical simulator or to have independently re-audited the entire source chain. Without those interfaces, read the comparison as a conditional theorem. The R∞ complete-cone proof does not depend on that TBMS lower bound.

BTBMS upper comparison uses standard entrances, a raw order code and specific parameterized macros. Its finite pruning strategy requires standard BTBMS totality and the owner/first-parent and span invariants; the [comparison note](btbms-comparisons.md) describes its fixed-target measure. Whole source-descendant closure is **not** assumed as an interface.

## Native standard entrances

With S3=current Limit[3], the current-rule certificates are:
~~~text
S3 → A=()(1^(1)()) : 2,2,1,1,0
A → C2=()(1^(1))(2^(2)) : 2
C2 → T :
1,0,1,1,0,1,2,1,0,0,0,1,2,1,0,1,0,0,0,1,0,1,1,0,1,0,0,0,0,1,0,0
C2 → R∞ :
1,0,1,1,0,1,2,1,0,0,0,1,2,1,0,1,0,0,0,1,0,1,1,0,1,0,0,0,1,2,1,1,0,0,1,0,0,1,1,0
R∞ → F∞ : 0,0
~~~
In the historical papers, U and U[2] mean
\[
U=[][0:W][0:1][2:W[]],\qquad
U[2]=[][0:W][0:1][2:W][3:W].
\]
This is not the BTBMS uniform carrier also called U, nor A[2]. The new index uses the direct seed certificates to avoid ambiguity.

## Unfinished claims

Global CDMN, A and A[2] well-ordering remain open. Their complete upper embeddings into BTBMS, e0MN, SRPD, ARD or wY are unproved. Finite interface-operator experiments beyond R∞ lack a completed paper extension and are not counted as a new frontier. No weakest-axiom claim, KP-plus-uncountable-ordinal audit, or new Lean theorem is supplied.
