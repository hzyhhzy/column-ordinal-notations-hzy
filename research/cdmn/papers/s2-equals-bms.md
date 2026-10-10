# The second CDMN seed and the BMS limit · [中文全文](s2-equals-bms.zh-CN.md)

This is an abridged English companion to the complete Chinese paper, dated October 9, 2026. For the prefix-zero rule it gives self-reviewed paper equalities
\[
|[][0:h]|=|\mathrm{BMS}(0^h)(1^h)|\quad(h\ge1),
\qquad |()(1^{(1)})|=\lim(\mathrm{BMS}).
\]
In particular `()(1^3)` corresponds to the three-row BMS seed BO, not the entire BMS limit. The argument assumes the known well-ordering of ordinary BMS; it does not assume global CDMN well-ordering. It is not Lean-certified or independently referee-reviewed.

## The coding invariant

In the natural-row region, define Fq(j) as the parent of the first record of height greater than q, or no parent. Let vq(j) be its forest depth. The first-parent forest is preorder, and successive record parents retreat along the forest indexed by the maximum preceding height. This permits nonmonotone raw row lists.

For control height h and preceding maximum f, the active BMS row is r=max(f,h−1), not necessarily h−1. Below r, a copied seam retains the old terminal parents; at or above r it inherits the donor's parents. These forest transport identities imply the usual BMS depth increments, with a separate ancestor mask for each row.

Encode each source column by its forest-depth core vector and finite sibling markers. A record whose height h is at most the previous maximum f produces h markers: rows below f retain the core values, row f is the depth of its parent plus one, and higher rows are zero. The terminal core is supplied or repeated according to whether the source node has a child and whether its last record exceeds the previous maximum. These finite endpoint cases are specified completely in the Chinese text.

## Standardness and equality

The sibling code maps each natural-height seed exactly to its finite-row BMS seed. It also maps the formal infinite positive copying word exactly to the corresponding BMS infinite copying word. This does not say the finite nth children are identical: a finite leaf may require a sibling-endpoint correction.

That correction is an actual finite BMS path. Repeated same-width steps reduce a finite bounded tail-coordinate vector; once it has only the first coordinate, a final copy produces the required repeated endpoint. The fixed finite state bound proves termination without running a huge countdown.

These corrections establish standard target images and strict source-step descent. Conversely, every fixed BMS child occurs below a sufficiently long source-child image. Thus the images are cofinal at **every source node**, not only at the seed. Well-founded induction on the known BMS measure, together with exact successor behavior, gives equality of the node ranks. Taking the supremum over all finite row counts gives the BMS-limit equality.

The prefix-zero and deep-zero reachable natural-row domains agree; the later general finite cleanup argument extends this equivalence to arbitrary legal contexts. No equality for higher nested seeds or the entire CDMN system follows.

## Evidence level

The saved checks include 9,000 standard states, 27,000 positive and 9,000 zero checks, plus raw invariant and independent transport checks. Crucially, 7,584 standard endpoint corrections and 86 raw corrections stopped after their preparation budget; these are not complete path successes. The universal finite correction argument is mathematical, not inferred from the bounded runs. See [historical evidence](../historical/README.md) and [dependencies](../proof-dependencies.md).
