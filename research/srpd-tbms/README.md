# SRPD versus TBMS and Y: research summary · [中文版](README.zh-CN.md)

## 2026-10-06: collected results at the research pause

Research is paused. The new [bilingual overview](continuation/README.md), [proof guide](continuation/PROOF-ROUTES.md), [manuscript catalogue](continuation/CATALOGUE.md), and [evidence guide](continuation/EVIDENCE.md) collect subsequent positive TBMS and Y work, excluding chronological notebooks and standalone failed routes.

- The whole-TBMS paper carrier improves to `D44=SRPD(1,2,4,8,4,1,2,9,38,4,12,42,44)`. Only `TBMS Limit≤D44` is established on paper; the converse remains open.
- TBMS equality calibrations reach `SRPD(1,2,4,8,4,1,2,9,38,4,6)=TBMS ()(1^(ω³))`. The larger ω^ω-row node has only a one-sided bound.
- Concrete Y equality papers include `134258`, `1342583`, and `1342584`. The highest whole-node lower-bound record is `Y(1,3,4,2,5,8,10,4,9,14,16,6,9)≤lim(SRPD)`, **conditional on listed historical interfaces, without an independent whole-chain review or Lean comparison**.
- The main candidate ending `17,10` remains unresolved. The last common-floor, finite-preparation, external-registry, and ordinary-phase lemmas are recorded separately, not promoted to a new whole-node bound.

The continuation contains 290 original-language arguments/supporting manuscripts, 7 historical finite receipts, and 3 previously delivered NER files. Manuscript count is not verified-theorem count. The [new manifest](continuation/manifest.json) records source/packaged hashes and excerpt ranges. The original 73-item archive is unchanged; curation is neither a new proof nor a publication.

## 2026-09-28 baseline: two final carrier routes

**The remainder describes the September 28 baseline, not the latest October 6 result.** Read the continuation above for subsequent results and status. This baseline summarizes the two final carrier routes
and their proof architecture, not the complete research history. “Paper result”
means an all-future descent-simulation argument was written; **no Lean
formalization or independent final review is claimed**.
The [final-route guide](archive/README.md) links the required manuscripts,
supporting lemmas, simulators and runtime dependencies. Follow its reading order
to inspect every premise, not just the final paper.
[Source records](source-records.json) and the [manifest](archive/manifest.json)
pin these manuscripts and code snapshots.

## 1. Coordinates and comparison convention

* SRPD uses the [implicit-root edition](../../notations/SRPD/definition.md).
  **Do not prepend the old redundant 1.** Its initial expression S=`[0]` has the
  same strict-descendant finite parent graphs as ordinary e0MN `M13=()(1:ω)`.
  At the endpoints `S[n+1]=M13[n]`; below them every default index agrees directly.
* TBMS means the ordinary system with the default fundamental sequence in
  NER's `BM-like/TBM.ts`, not a strong or short-expansion variant.
* $\rho(A)$ is the well-founded rank of all native steps $A\to A[n]$ for
  nonzero A and $n\ge0$, excluding the zero self-loop. Every source step is
  realized by a **nonempty finite native target descent** in the
  same continuing target state, with no mid-simulation restart from a new seed.
* Such a rank bound is not a delivered history-independent canonical order
  converter or same-index FS isomorphism. A different semantic valuation needs
  its own agreement theorem with this rank.
* Only standard generated domains are used. Raw legal graphs, failed bounded
  searches and count growth do not by themselves establish ordinal comparisons.

SRPD presents a common segment of RPD, ARD, ARD2 and IPD, with endpoints and
finite-bottom adjustments in the [correspondence note](../../notations/SRPD/correspondence.md).
It is not the whole RPD order type.

## 2. Tightest bounds with recorded paper arguments

Abbreviate the following SRPD count words:

```text
P  = 1,2,4,8,4,1,2,9,38,4
W  = 1,2,4,8,4,2
Qw = P,12,42,44,46,47,54,91
V  = P,12,42,44,46,47,54,90,266,1072,4384,16474,56026,173593,495365,1315558,3281173
Cε = P,9,10,17,51
```

These denote actual standard graphs, not arbitrary count strings accepted as
syntax. The bundled [native-path test](../../tests/srpd_tbms_bounds.cjs) reaches
them from `[0]` using the delivered rule.

### 2.1 The whole ordinary TBMS limit

The latest manuscript `WEAK-ARCHIVE-SEED.zh-CN.md` gives

$$\boxed{\rho(\mathrm{TBMS\ Limit})\le\rho(V)<\rho(Q_w)<\rho(W[1])<\rho(W)<\rho(S).}$$

V is a fixed 26-column preparatory state chosen before the recursive depth.
For each finite depth L, paid initialization from that same V builds the row
banks needed for the corresponding TBMS top child, followed by continuing
simulation. Taking suprema gives the common bound. Strictness elsewhere comes
from actual target descent, **not** from pushing strict inequalities through a
supremum. `TBMS Limit<V` is not proved; `TBMS Limit<Qw` is.

Optimality is not proved. Separate smaller-seed searches and obstruction analyses are not packaged here.

### 2.2 A specialized bound for `TBMS ()(1^ε₀)`

Here ε₀ is the **row label** `ε=()(1,1)`, not the value of the whole expression.
The exact source terms are

```text
E = ()(1^()(1,1)) = TBMS Limit[3][1]
J = ()(1^()(1,1),1)
```

Native `J[n]=()(1^ε)(2^ε)…(n^ε)`, in particular `J[1]=E`.
`EPSILON-FIXED-BANK-BOUND.zh-CN.md` establishes

$$\boxed{\rho(E)<\rho(J)\le\rho(C_\varepsilon).}$$

This smaller source class needs no unbounded recursive stack of ceiling
templates. Cumulative row endpoints are ε or standard one-row forests below it.
Its two-row graph fits a persistent finite bank of capacity 4, reducing the
eleventh count to 9. This specialized improvement does not automatically apply
to the entire TBMS system.

## 3. Direct consequences and open scope

The final strict bounds exclude the old conjecture `M13=TBMS ()(1^ε₀)` and
the proposed identification of `W=1,2,4,8,4,2` with the internal TBMS term
`()(1^(ω^ω))`. Both follow from the whole-system bound above; their older
equality-search routes are not needed.

Neither comparison direction between the smaller candidate `P,6,7,9` and E
has been proved. Its search code is excluded, and an unsuccessful bounded
search is not being used as a nonembedding argument.

## 4. Proof architecture and indispensable resources

### 4.1 Capacity and genuine descent

For a target parent graph, $C(p,j)$ is the greatest row at which p is an ancestor
of j. Full reflection moves both parent addresses and rows above the cut and
changes the seams. The proof treats same-copy, cross-copy, strict-external and
seam capacity cases separately. Control exposure, row truncation and tail
deletion must all be realized by finite native descent, not free edge addition
or target reset.

### 4.2 Finite row banks

A level-l finite source label b is represented by target points requiring, for
**every pair including source nonedges**,

$$C(p_i,p_j)\ge2+D_l(\operatorname{Cap}_b(i,j)).$$

At level 0, $D_0(h)=h$; higher positive demands use lower-level endpoint archive
codes. Main positive endpoint codes are archive addresses plus 1. Smaller old
banks may remain in place, so only subcovariance is required, not equality of
every address shift. Source unit copying adds no cumulative endpoints; a limit
refinement first plans registration of every new endpoint. Lower levels are
handled first, with decreasing recursive depth, rather than circularly assuming
the higher source well-ordering being proved.

### 4.3 Paid calls and main-region recovery

Each main point has three helper columns. After the current source index is
known, prepare finitely many call coupons and consume one on each activation.
Only a genuine main source step restores the normal helper configuration.
The work column may inherit the entire active archive; later actual tail
deletion returns to a preserved healthy main helper. This reduces general
access ports to one row while preserving the two-row finite-bank background.

### 4.4 Arbitrary finite depth and the latest compression

A ceiling bank uses $(r,u,v,e)$ with root background 2, internal pair
$C(u,v)\ge H>r$, and $C(u,e),C(v,e)\ge1$. The latter conditions previously
required 2, but cross-copy ports use only $\min(1,h-1,1)=1$, so the extra row is
unnecessary. A five-point mother bank keeps a separate child archive and can
pay to create arbitrarily many finite levels without exhausting the background
one level at a time. Fixed V precedes the depth choice, providing the common
bound for the whole system.

The specialized E proof dispenses with that ceiling entirely: ε has ordinary
two-row graph `[][1,1]`, represented by points `(10,11)` of capacity 4. This finite
maximum bank still persists, since ε retained in earlier source columns may
become active again at later, larger indices.

## 5. Limits of the conclusion

This package retains the arguments needed for the two carrier routes, not
absolute minimality of their counts. General reverse localization remains
unproved, and no history-independent same-index converter is delivered.
Earlier exact low cases, other candidates and failed routes are not premises
of these bounds.

## 6. Verification and packaging scope

The research snapshots contain these finite checks:

| Batch | Completed checks | Explicit limits |
| --- | --- | --- |
| Weakened archive | 14 source/initialization cases, 41 source steps, 6 additional paid local operations; common gate checked with 1, 2, 5, 11 coupons | Depth 5 and 12 cases check initialization only, not arbitrary deep source paths |
| Fixed ε bank | 10 of 12 cases complete; 38 completed source steps overall, 32 in fully completed cases; persistent ε called at 1, 4, 6 | 2 paths stop at the 160,000-column guard; 3 cases are initialization only |

Simulations had per-process 20-second, 512 MiB Node heap and 650 MiB RSS guards,
with at most two simultaneous processes. Peak RSS was approximately 393 MiB for
the weakened archive and 345 MiB for the finite ε bank. All processes exited.
Batches reuse a simulator; their sample counts are not independent proofs.

This package adds a self-contained [target-path check](../../tests/srpd_tbms_bounds.cjs)
and [implementation correspondence check](../../tests/srpd.cjs), recorded in the
[package validation](../../tools/srpd-validation.json). They check the delivered
kernel, standard carriers and displays, not the entire recursive TBMS source
simulation or its universal theorem. In addition, the [final-route material](archive/README.md)
retains 25 required proof/lemma manuscripts, runtime dependencies and 2 route-specific
verification records: 73 imported items. The separate
[post-pruning replay receipt](archive/ARCHIVE-VALIDATION.json) covers 28 current
checks: 26 completed and 2 original width guards. These are not combined with
the historical totals above. Unrelated archival copies were removed; original
research files outside Git remain intact.

Private source PDFs, the full upstream host and unrelated machine caches are not
included. Existing rules, Lean projects and axiom-strength results are unchanged.
