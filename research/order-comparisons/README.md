# Order-type comparisons and embeddings · [中文版](README.zh-CN.md)

Collected on **2026-09-20**. This catalogue gathers the existing comparison manuscripts, rather than announcing a new proof audit. Unless stated otherwise, “paper result” means that a manuscript supplies a general argument, **not an end-to-end Lean comparison certificate**. Finite regression counts are supplementary evidence only.

The original-language manuscripts and their mathematical supporting notes are in [proofs](proofs/). Local links have been relocated and private machine paths redacted; historical test commands may refer to scripts not bundled here. Their older status statements are historical, not claims that this repository is still unchanged. [Import provenance](import-manifest.json) records the selected source files and hashes. No PPS4S material is included.

## 1. Conventions and versions

2026-10-06 addition: the [SRPD/TBMS/Y overview at the research pause](../srpd-tbms/continuation/README.md) and [proof guide](../srpd-tbms/continuation/PROOF-ROUTES.md) collect subsequent positive results, including the whole-TBMS D44 carrier, the ω³-row equality, and the historical-premise-dependent Y(S9) lower bound. The September 28 paragraph below is an older baseline, not the latest status. Neither archive layer changes this page's frozen historical import manifest.

2026-09-28 addition: the [bilingual SRPD/TBMS summary](../srpd-tbms/README.md), [final-route material and replay guide](../srpd-tbms/archive/README.md), and [common-segment argument](../../notations/SRPD/correspondence.md). SRPD's strict initial cone corresponds to RPD `1,2`, ARD/ARD2 `1,1,3`, IPD `1,2` and ordinary e0MN `1,3`, with the stated finite-bottom and endpoint-index alignment. The summary records the whole ordinary-TBMS paper bound, the improved special carrier for `()(1^ε₀)` and the open `…6,7,9` candidate. No Lean comparison is added; only actual final-route dependencies are retained, separate from the frozen historical import manifest below.

2026-09-23 addition: the new bilingual [BMS-to-FMP paper](../../proofs/paper/bms-le-fmp-12242444.md) supplies a direct original-FMP proof, with a bundled bounded audit. It is separate from the unchanged historical import manifest.

- “Whole X” means its finite **standard generated domain**, excluding the external top. “Below X(s)” means the standard strict descendant cone specified in the cited manuscript. A counterexample on arbitrary raw inputs is not automatically a standard counterexample.
- $X\hookrightarrow Y$ denotes a strict order embedding. It does not by itself assert an initial image, surjectivity, equality of counts, or commutation with every indexed fundamental-sequence step.
- Equalities below identify the relevant initial-segment order types, with finite bottoms and endpoints handled as in the papers. They are not blanket literal equality of data or of `FS_short`.
- Unless explicitly marked **strong**, e0MN means the ordinary notation by **@test_alpha0**. The [two bundled fast-counting NER files](../../external/README.md) preserve the separate expansion rules. New strong refers specifically to the 2026-09-19 edition based on `strong_e0MN (1).js`, including transport of implicit coefficient 1; it is not the older strong edition.
- ARD and ARD2 mean the repository's current skyline editions. wY means **omega-Y weak magma**, not weak omega-Y. The wY/CWY2 comparisons retain their stated reliance on finite lemmas from the supplied wY manuscript, which is not redistributed here.
- An embedding into a not-yet-proved well-order supplies a well-ordered **copy**, not a well-ordering of the whole target. Ordinal-value inequalities involving such a target are conditional on its well-order interpretation. In particular, this catalogue does not prove global e0MN, ACD or CSD well-ordering, and **ICP is known not to be well-ordered**.

## 2. Whole-system upper bounds in ordinary e0MN

All target terms below are actual standard terms; the cited arguments place the source in their strict descendant cones. None claims a minimal upper bound or equality. The last row is deliberately only an IPD initial segment.

| Source | Ordinary e0MN bound: count display | Exact target list | Paper |
| --- | --- | --- | --- |
| Whole RPD | `1,3,13,2` | `()(1:ω)(2:ω2)(1:1)` | [Tighter RPD bound](proofs/rpd-e0mn-tighter-20260917/RPD-le-e0MN-13132.zh-CN.md) |
| Whole ARD | `1,3,14,1,6,54` | `()(1:ω)(2:ω^2)()(4:ω)(5:ω^2+1)` | [ARD embedding](proofs/ard-e0mn-cover-20260917/ARD-le-e0MN.zh-CN.md) |
| Whole ARD2 | `1,3,14,1,6,185` | `()(1:ω)(2:ω^2)()(4:ω)(5:ω^3+ω+1)` | [ARD2 embedding](proofs/ard2-e0mn-cover-20260917/ARD2-le-e0MN.zh-CN.md) |
| Whole wY / CWY2 | `1,3,14,2` | `()(1:ω)(2:ω^2)(1:1)` | [CWY2/wY embedding](proofs/cwy2-e0mn-cover-20260917/CWY2-wY-le-e0MN.zh-CN.md) |
| IPD below `1,3` | `1,3,11` | `()(1:ω)(2:ω+1)` | [IPD low-segment argument](proofs/ipd-e0mn-20260917/README.zh-CN.md) |

In the first list, `ω2` means $\omega\cdot2$, not $\omega^2$. All these bounds lie below ordinary e0MN `1,4`. The earlier [RPD bound at `1,4`](proofs/rpd-to-e0mn-20260917/RPD-le-e0MN-14.zh-CN.md) is retained as supporting history and is superseded by the tighter row above. Common upper bounds do **not** decide ARD/ARD2 versus wY.

## 3. Exact low-segment correspondences

| Correspondence | Scope / caveat | Paper |
| --- | --- | --- |
| ordinary e0MN `1,3` = RPD `1,2` | Add a leading empty column on the nonzero cone; align the finite bottom separately for ordinal equality. | [Proof](proofs/e0mn13-rpd12-20260919/README.zh-CN.md) |
| new strong e0MN `1,2` ≅ RPD `1,2` | Default indexed FS and counts agree under the stated projection. Finite `FS_short` cutoffs differ. | [Proof](proofs/strong-e0mn-counting-20260919/RPD-12-correspondence.zh-CN.md) |
| ordinary e0MN `1,3` = ARD `1,1,3` | Leading empty-column / bottom correction; the endpoint FS has an index shift. | [Proof](proofs/e0mn-ard-embedding-20260917/README.zh-CN.md) |
| ordinary e0MN `1,3` = IPD `1,2` | Standard-domain quotient/projection, including the bottom boundary. | [Proof](proofs/ipd14-e0mn-20260917/e0MN-13-equals-IPD-12.zh-CN.md) |
| ICP `1,2` ≅ RPD `1,2` | Ancestor-table correspondence of the two seed descendant domains; default indices and counts are preserved. | [Proof](proofs/icp-candidate-20260919/RPD-ICP-flat-correspondence.zh-CN.md) |
| ICP `1,2,4` = RPD `1,2,5` | Bidirectional order embeddings of the designated flat sectors; not a whole-RPD comparison or termwise FS identity. | [Proof](proofs/icp-candidate-20260919/RPD-zero-row-sector-below-ICP-124.zh-CN.md) |
| ACD `1,2,3,5,9,5` = ordinary BMS limit | This particular initial segment is well-ordered; global ACD well-ordering remains open. | [Proof](proofs/new-notation-20260918/ACD-123595-equals-BMS.zh-CN.md) |

The ICP correspondences survive its higher standard infinite chain. Do not assign the **whole** ICP an ordinal order type; see [the counterexample](../../notations/ICP/non-well-founded.zh-CN.md).

## 4. Other lower bounds

| Source | Target | Evidence and boundary |
| --- | --- | --- |
| Whole wY | Current skyline RWD | [Definition and paper](proofs/substantive-wy-20260914/SKYLINE-WORDS.zh-CN.md), [global cover bridge](proofs/substantive-wy-20260914/GLOBAL-COVER-BRIDGE.md), [independent lower-bound audit](proofs/substantive-wy-20260914/LOWERBOUND-INDEPENDENT-AUDIT.md). Gives $\mathrm{wY}\le\mathrm{RWD}$, not strict inequality or a significant strength gain. |
| RPD through `1,2` | ACD through `1,2,4` | [Local embedding](proofs/new-notation-20260918/ACD-RPD-embedding-progress.zh-CN.md), including the stated endpoints. Not the whole RPD. |
| Whole ordinary BMS | CSD below `1,1,2,5,2` | [Tight bound](proofs/csd-20260917/BMS-small-bound.zh-CN.md), with [full embedding construction](proofs/csd-20260917/BMS-embedding.zh-CN.md). No global CSD well-ordering assumption. |
| Whole ordinary BMS | ICP below `1,1,2,4,2` | [Embedding](proofs/icp-candidate-20260919/BMS-below-11242.zh-CN.md). Does not claim that the whole ICP is well-ordered. |
| Whole ordinary BMS | FMP below `1,2,2,4,2,4,4,4` | [Bilingual paper](../../proofs/paper/bms-le-fmp-12242444.md). Original copy-indexed FMP; ordinal interpretation uses the companion ZFC + I3 paper. No equality, minimality or Lean certificate. |
| Whole ordinary BMS | IBLP `initial[0][1]` | **Conditional paper result; see the hypothesis immediately below.** [Manuscript](proofs/iblp-bms-20260918/IBLP-01-BMS-lower-bound.zh-CN.md). |

**IBLP hypothesis:** when any strict legal descendant of $A=\mathrm{initial}[0][1]$ is expanded further, it triggers neither native completion nor marked completion. Completion in the step from $A$ itself to $A[n]$ is still executed by the original rule. This hypothesis is **assumed, not proved here**. Under it the manuscript gives an order embedding of the whole ordinary BMS standard domain into the actual strict descendants of $A$. It proves neither the reverse bound nor equality nor well-ordering of that entire target cone. `[0][1]` is a path from `initial`, not a decimal or a count word.

The archived RWD paper also claims well-ordering in $KP_\omega+\text{there exists an uncountable ordinal}$, with full set induction. That is a paper result, not a new Lean project; its role here is context for the wY lower bound. Old free-RWD no-skip conjectures are not substituted for the current skyline proof.

## 5. Existing repository comparisons and remaining gaps

Previously collected papers already give $1Y\le\mathrm{RPD}$, whole RPD below ARD `1,2`, whole ARD below ARD2 `1,3`, and CWY2 ≅ wY. See [Y→RPD](../ordinal-comparisons-20260914/archive/ipd-upper-bounds/Y-le-RPD-proof.zh-CN.md), [RPD→ARD](../../proofs/paper/rpd-le-ard-a2.md), [ARD→ARD2](../../proofs/paper/ard-le-ard2-13.md), and [CWY2 equivalence](../../proofs/paper/cwy2-equivalence.md). The new archive complements those papers rather than duplicating their certification claims.

Not established by this collection: `Y133 ≤ RPD12`; any proposed whole-system ARD2–wY comparison; a whole-IPD embedding from the low-segment rows above; whole ACD→RPD/ARD2; global ACD or CSD well-ordering; equality or optimality of the e0MN upper bounds; or a proof-theoretic ordinal comparison with Z3. Local count growth, a common axiomatic upper bound and finite tests are not substitutes for embeddings.

## 6. Reading the proof folder

The main links above point directly to the result manuscripts. Supporting files preserve the earlier ACD BMS bounds, the nonstandard BMS row-bound lemma, CSD's fixed-width and local-clock arguments, the RWD skyline/standard-domain audits, the IPD KP tree-rank lemmas used by RWD, and the wY finite-copy audit. These supporting files can contain failed candidates or explicitly unfinished sections; their presence does not upgrade them to additional theorems.

Some dependencies remain external, notably the supplied wY paper and the known BMS theorems specified in the manuscripts. No private source PDF, unbounded search process, or mathematical rule change is part of this import. New definitions are [ACD](../../notations/ACD/definition.md), [CSD](../../notations/CSD/definition.md), and [ICP](../../notations/ICP/definition.md); external e0MN code is credited separately to its inventor.
