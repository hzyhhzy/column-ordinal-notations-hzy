# SRPD versus TBMS and Y: results and proof archive · [中文](README.zh-CN.md)

Collected **2026-10-06**. Research is paused at the user's request. This is an archive of existing work, not a new comparison theorem, notation revision, or Lean proof.

This directory extends the [2026-09-28 archive](../archive/README.md). It preserves the positive arguments and supporting interfaces, without importing chronological `STATUS`/`CONTINUE` notebooks or standalone failed routes. Necessary hypotheses, domain restrictions, and unresolved directions remain explicit.

## Reading route

- [Proof architecture and intermediate results](PROOF-ROUTES.md).
- [Evidence, historical viewers, and verification boundaries](EVIDENCE.md).
- [Complete manuscript catalogue](CATALOGUE.md), grouped by original research topic.
- [Source manifest](manifest.json): original and packaged hashes, omitted sections with original line ranges, and references not packaged here.
- [Earlier runnable archive](../archive/README.md): its 73 imported items and 25 manuscripts remain unchanged.

The long source manuscripts remain in Chinese. The overview, proof guide, and evidence guide are bilingual; this is not a full translation of every historical proof.

## Conventions and status

Write `S(s)` for a **standard SRPD expression in the current implicit-root edition** with displayed count sequence s. Counts do not replace the full parent table. Put

\[
R=\rho(\lim\mathrm{SRPD}),\qquad I_N=S(1,2,4,\ldots,2^{N-1}),
\qquad L=\rho(\mathrm{TBMS\ Limit}).
\]

`I_N` has N visible columns. Ordinary e0MN's M13 presents the corresponding SRPD initial segment, with `SRPD[n+1]=M13[n]` at the endpoints. Do not prepend the obsolete redundant 1. SRPD is not the entire RPD system; see the [common-segment statement](../../../notations/SRPD/correspondence.md).

TBMS means ordinary TBMS with its default fundamental sequence and arbitrary finite recursive row labels, not a strong variant and not merely rows below ε₀. `B_H=()(1^H)` denotes an empty root followed by a constant-parent column of total row height H, using native row segments for composite H. **H is a row height, not the ordinal value of the whole expression.**

`ρ` is the well-founded rank of native fundamental-sequence descent from nonzero expressions, with empty rank zero and the zero self-loop excluded. Ordinal-value language uses the stated standard-domain rank/order-type interpretation; it does not extend to arbitrary handwritten graphs.

| Evidence | What is recorded | What is not established by archiving it |
|---|---|---|
| Paper comparison | An all-parameter argument covering all descendants, citing earlier lemmas | Lean verification or independent end-to-end review |
| Conditional paper bound | A new induction under explicitly listed historical interfaces | Discharge of those premises or completion of the larger target |
| Local interface | A theorem under particular resource, label, or phase assumptions | Coverage of every native future |
| Finite check | A formula, implementation, selected path, or file-identity check | A universal theorem or exact ordinal value |

Even a paper rank equality does not assert equal same-index fundamental sequences. A persistent descent simulation need not be a canonical, history-independent order embedding. No comparison theorem in this continuation has been added to Lean.

## 1. The whole TBMS limit

The smaller fixed carrier currently recorded is

```text
D44 = S(1,2,4,8,4,1,2,9,38,4,12,42,44)
W   = S(1,2,4,8,4,2)
```

The [finite-roof manuscript](papers/output/tbms-srpd-equalities-20260929/FINITE-ROOF-WHOLE-TBMS-LOWER.zh-CN.md) gives

\[
\boxed{L\le\rho(D44)<\rho(W)<R.}
\]

For each finite recursive depth, finite maximal row banks are initialized in a descendant of D44. That same target then handles all subsequent source choices. Taking the supremum over depths gives the non-strict first inequality. The converse is open; neither `L=D44` nor `L<D44` follows from this proof.

The successful compression sequence is: full archives and paid calls → one-row returns → contiguous main columns → weak top templates → **finite maximal banks without an infinite template**. Older wider carriers and the special `B_(ε₀)` bound remain in the baseline archive.

These paper bounds exclude the earlier equalities `W=B_(ω^ω)` and `lim(SRPD)=B_(ε₀)`. The discarded searches for those equalities are not reproduced here.

## 2. TBMS equalities and the next one-sided bound

Define

```text
P = 1,2,4,8,4,1,2,9,38,4
J6 = S(P,6)
J7 = S(P,7)
```

Appending to P means concatenating count columns. The following are historical paper rank equalities, with their stated dependencies, not newly certified results.

| SRPD expression | TBMS expression | Manuscript |
|---|---|---|
| `S(1,2,4,8,4)` | `B_(ω²)` | [First five-column block](papers/output/tbms-e0mn-bridge-20260925/FIRST-FIVE-COLUMN-EQUALITY.zh-CN.md) |
| `S(P,5,12,41,42)` | `()(1^(ω²))(2)` | [Parallel-leaf limit](papers/output/y13425858-srpd-equality-20260929/TBMS-SIBLING-LIMIT-SRPD-EQUALITY.zh-CN.md) |
| `S(P,5,12,42)` | `B_(ω²+1)` | [Full-chain limit](papers/output/tbms-srpd-equalities-20260929/OMEGA2-FULL-CHAIN-EQUALITY.zh-CN.md) |
| `S(P,5,12,43)`, `S(P,5,12,44)` | `B_(ω²+2)`, `B_(ω²+3)` | [Component-root bands](papers/output/tbms-srpd-equalities-20260929/COMPONENT-ROOT-OMEGA-EQUALITY.zh-CN.md) |
| `S(P,5,12,45)` | `B_(ω²+ω+1)` | [Same paper](papers/output/tbms-srpd-equalities-20260929/COMPONENT-ROOT-OMEGA-EQUALITY.zh-CN.md) |
| `S(P,5,12,45,7)=J6[1]` | `B_(ω²·2)` | [Double band](papers/output/tbms-srpd-equalities-20260929/DOUBLE-OMEGA2-ROW-EQUALITY.zh-CN.md) |
| `J6[k]`, k≥1 | `B_(ω²(k+1))` | [Recursive crowns](papers/output/tbms-srpd-equalities-20260929/RECURSIVE-CROWN-OMEGA3-EQUALITY.zh-CN.md) |
| `J6` | `B_(ω³)` | [Same paper](papers/output/tbms-srpd-equalities-20260929/RECURSIVE-CROWN-OMEGA3-EQUALITY.zh-CN.md) |

`B_(ω²·2)` has two row segments in **one column**; it is not the two parallel leaves `()(1^(ω²))(1^(ω²))`.

The [finite-rank bank argument](papers/output/tbms-srpd-equalities-20260929/FINITE-RANK-PORT-LOWER.zh-CN.md) gives only

\[
\rho(B_{\omega^{n+2}})\le\rho(J7[n])\ (n\ge1),\qquad
\rho(B_{\omega^\omega})\le\rho(J7).
\]

No reverse bound for the whole cone of `J7[2]=S(P,6,8)` is recorded. Local return-protocol bounds are not that missing global upper bound. The [symmetric tower family](papers/output/tbms-e0mn-bridge-20260925/SYMMETRIC-TOWER-BOUND.zh-CN.md) remains useful as a carrier, not as a proved equality table.

## 3. Y calibrations

Let

\[
\beta=\rho_Y(1,3,4,2,5,8)=\rho(S(1,2,4,8,4))=\rho(B_{\omega^2}).
\]

| Y node | Recorded result | Manuscript |
|---|---|---|
| `134258`, also `1258` | Value β | [Y/TBMS calibration](papers/output/y-tbms-epsilon0-20260927/Y134258-TBMS-OMEGA2.zh-CN.md), [prefix absorption](papers/output/y1342585-equality-20260929/PREFIX-ABSORPTION.zh-CN.md) |
| `1342583` | Equals `S(P,3)`, value β^ω | [Petal powers](papers/output/y1342583-srpd-equality-20260929/EQUALITY.zh-CN.md) |
| `1342584` | Equals `S(P,4)`, value `sup{β,β^β,β^(β^β),…}` | [Protected powers and weighted forests](papers/output/y1342584-srpd-equality-20260929/EQUALITY.zh-CN.md) |
| `1342585` | Ten-column prefix located; complete equal representative still unknown | [Prefix location](papers/output/y1342585-equality-20260929/SRPD-PREFIX-LOCATION.zh-CN.md), [improved U[5] bound](papers/output/y1342585-equality-20260929/PREFIX-ABSORPTION.zh-CN.md) |
| `1,3,4,2,5,8,9,11` | `≤ B_(ε₀)` | [Forest budget](papers/output/y-tbms-epsilon0-20260927/FOREST-BUDGET-UPPER.zh-CN.md) |
| `1,3,4,2,5,8,10` | `≤ TBMS Limit ≤ D44 < W` | [Recursive ports](papers/output/y-recursive-port-upper-20260927/RECURSIVE-PORT-UPPER.zh-CN.md), then the TBMS carrier |

In old shorthand `a` means the single entry 10. The proposed equality `Y13425858=()(1^(ω²))(1^(ω²))` was once accepted as a **user-supplied working hypothesis**, not independently proved. It cannot turn a TBMS equality into an unconditional Y equality.

Earlier bounds for `133`, `134`, `134257…`, including the smaller-domain order-embedding prototype, are retained in the [catalogue](CATALOGUE.md). Their tighter individual carriers remain informative even after larger global lower bounds were obtained.

## 4. Higher Y lower bounds for all SRPD

Fix `C=(1,3,4,2,5,8,10,4,9,14,16)`. These are **conditional paper results under their listed historical interfaces**, without an independent audit of the entire chain or a Lean comparison.

| Whole Y node/family | Recorded bound | Main paper |
|---|---|---|
| `Y(1,3,4,2,5,8,10,4)` | `< I20` | [Port lifting](papers/output/y134259-owner-returns-20260928/ORDINARY-PORT-LIFT-FINITE-CARRIER.zh-CN.md) |
| `Y(1,3,4,2,5,8,10,4,9,14)` | `< I83` | [Height-one closed roots](papers/output/y134259-owner-returns-20260928/HEIGHT-ONE-SEALED-PORT-BOUND.zh-CN.md) |
| `Y(C)` | `≤R`, finite diagonal carriers for individual children | [Finite nesting depth](papers/output/y134259-owner-returns-20260928/HEIGHT-ONE-SEALED-DEPTH-BOUND.zh-CN.md) |
| `Y(C,6)` | Improved to `< I29` | [Recursive indexed closure](papers/output/srpd-limit-y-lower-20261001/RECURSIVE-INDEXED-CLOSURE.zh-CN.md) |
| `Y(C,6^m)`, m≥1; repetition, not exponentiation | `< I_(3m+26)`; `Y(C,6,7)≤R` | [Finite return levels](papers/output/srpd-limit-y-lower-20261001/FINITE-RECURSIVE-CLOSURE-BOUND.zh-CN.md) |
| `Y(C,6,7,9)` | `< I120` | [Return-tree limit](papers/output/srpd-limit-y-lower-20261001/EPSILON-TREE-RETURN-BOUND.zh-CN.md) |
| `Y(C,6,8)` | Improved to `< I120` | [Feedback closure](papers/output/srpd-limit-y-lower-20261001/FEEDBACK-CLOSURE-FIXED-CARRIER.zh-CN.md) |
| `Y(C,6,8,9)` and subsequent heads, branches, and working leaves | Successive `≤R` bounds | [Intermediate manuscripts](CATALOGUE.md), [proof guide](PROOF-ROUTES.md) |
| `Y(C,6,8,10,12,13,14)` | `≤R` | [Finite generating grades](papers/output/srpd-limit-y-lower-20261001/GRADED-GENERATOR-CLOSURE.zh-CN.md) |
| `S9=Y(C,6,9)` | **`≤R`: highest whole-node result currently recorded** | [Finite structural grades](papers/output/srpd-limit-y-lower-20261001/FINITE-STRUCTURAL-GRADE-CARRIER.zh-CN.md) |

“Whole” quantifies over all fundamental-sequence children and all their legal descendants, not a bounded sample. Different finite carriers for different children yield a supremum bound; they are not automatically one fixed finite carrier.

This does not show `S9≤S(124842)`. The larger candidates

```text
B = Y(1,3,4,2,5,8,10,4,9,14,17,10)
A = Y(1,3,4,2,5,8,10,4,9,14,17,9)
```

remain unresolved: neither direction for B versus R, nor the full comparison of A with `S(124842)`, is completed. No impossibility of embedding is established. Bounds for `Y134259` or `Y1343` by R have not been obtained.

## 5. Last local progress before pausing

The final work does not increase the whole-node lower bound. It establishes resource interfaces:

1. A common capacity condition for every live root, preserved by specified high steps and same-width returns.
2. Maximal-row preparations retaining old controls, with exact external-control registry updates.
3. Preallocating `k+2` private auxiliaries for k successive finite preparations before one unchanged source step.
4. Under available internal/external control points, one compensation pays for an **entire ordinary-only phase**, without charging for every ordinary step.

The missing global theorem is that suitable controls remain available along **every legal alternation of high and ordinary phases**. Finite composability, successful examples, and ordinary-phase closure do not prove B≤R. The [proof guide](PROOF-ROUTES.md) states the formulas and hypotheses explicitly.

Every imported manuscript has an archival banner. Its historical “latest” and “active target” refer to its own stage, not to the paused state here. Original/packaged SHA-256 values and excerpt ranges are preserved. Unpackaged code is identified as a source reference rather than exposed as a broken download link. The [evidence guide](EVIDENCE.md) separates portable checks from historical, non-replayed records.
