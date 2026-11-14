# Fixed-row BMS upper bounds for BTnSS · [中文](README.zh-CN.md)

The collected paper aims to embed the entire standard **strong BT*(-1)Y-nSS v2** domain, for every finite $n\ge2$, below one fixed standard BMS term. Essential steps are still being completed and rigorously checked; the displayed inequality is not currently a certified completed result. Put

$$
B_r=(0^r)(1^r),\qquad U_r=(0^r)(1^r)(2^r)(3^r).
$$

Then

$$
\boxed{\lim(\mathrm{BTnSS})\le |U_{n+1}|<|B_{n+2}|.}
$$

The endpoint $|B_{n+2}|$ is the supremum of **standard $(n+1)$-row BMS**. The intermediate ceiling is uniform over all source seeds, nesting depths and term sizes: $U_{n+1}=B_{n+2}[3]$ under the frozen short fundamental sequence.

The original manuscript recorded this as a completed, self-reviewed paper proof;
**the present audit no longer unconditionally endorses that completion judgment**.
No counterexample to the main claim has been found, but standard-domain block invariants,
complete encoding transport and concrete coverage remain substantive
verification obligations, not presumed mechanical Lean translation. The manuscript
is preserved as research provenance; consult the independent Lean project for the
current certified scope. No equality, initial image, or equally indexed FS commutation
is asserted. The proposed argument uses finite BTnSS invariants and Hunter's BMS
well-ordering theorem, not the older I3/almost-2-huge interpretation. No minimal
axiomatic theory is claimed.

**Even the BT3SS-only upper bound is not yet complete.** Fixing `d=2` reduces
the intermediate numerical-row conditions to `SB₁`; it does not remove arbitrary
forest nesting, source block-order preservation or target standardness.
Complete-block insertion domination for strict closing ancestors is now proved,
but is not the final inequality between actual blocks.
The four-row raw order embedding and uniform raw ceiling are verified, but do
not yet imply that the BT3SS order type is below the BMS limit. This is not a
refutation of the separate external BT3SS well-ordering proof.

## Reading the proof

2026-10-22: an independent [partial Lean development](../../lean/BTnSSBMS/README.md)
now checks concrete syntax, parent/key machinery, a linear-size encoder bound,
and the conditional coverage-to-standardness argument. The continuation also
checks zero-binding preservation/no fallback, the finite-word last-hole lemma,
and the dimension-parametric seed-expansion identity. The complete executable
source rule now supports 24 kernel-checked finite path certificates. Every
seed-reachable source's entire code now has the **uniform raw ceiling**
`U_(n+1)`. Saved frames have prefix truncation, exact `2*i` heights and real
pointer witnesses; the key-height comparison cases are exhaustive. Actual BMS
parent-chain inclusion, ancestry-based activation, nonnegative differences, and
strict raw descent of defined expansions are also checked. The
[first-diagonal lemma](../../lean/BTnSSBMS/src/BTnSSBMS/BMSBlocks.lean) is now checked
for actual parent tables, complete blocks and rebasing, using only BN and the
lower-row SB conditions. Numerical-legality-based expansion totality, the
complete-block descendant cone, and the exact first-copy/rebase-prefix identity
are also proved. Full recursive scopes and actual saved-binding key-row ancestry
are established. Complete d+2-row legality, including keys/tags, now follows for
finitely numerically legal sources. Standard-domain preservation of these source
conditions and complete encoding order preservation are now connected; coverage and target
standardness remain open. The isolated
project now verifies finite legality of all source diagonal seeds, total legal
deletion/special branches, and preservation by every defined index-zero step.
Low-branch first-head parent transport is connected to the actual `shift`/`delta`.
The subsequent modules check complete arbitrarily nested no-hole material,
construct the first entering state from the actual selected root, and derive
later numerical seams from the previous transported state. Appending the highest
key parent is proved not to alter numerical activation. Computed hole sites and their
transport, arbitrary-depth splicing and the root template's row-zero descendant cone
are now checked. All low-class copy counts are connected in positive classes and in
the zero-class same-forest case, with the initial view and delta constructed from the
actual selected root and the entire result installed back in the original template.
No legality or owner fence of later replicas is assumed. All highest-class copy counts
and first-list replacements are now connected. The initial donor is the original
terminal list minus its last forest; later donors follow from the preceding phase's
transport. Literal `locateRoot`/`spine`/`drop` numerical pieces have their actual scoped
contexts, and the selected stopping column agrees with the template hole. Actual
highest-parent selection excludes open owners and consequently forces a nonempty root
tail, rather than assuming it. The exact marked root piece, original visible root
vector and delta are now identified; actual low-class selection is connected to the
numerical parent table. `expand_positive_low_finiteLegal` proves whole-term finite
legality for every successfully returned positive low-class step of the original
function. The actual highest-key ancestor's numerical interpretation, full marked
donor history and whole high-class assembly are now connected as well.
`expand_high_finiteLegal` proves whole-term finite legality for every successful
highest-class step in positive dimension. The latest continuation proves highest-key
parent existence and low-class terminal leafness. A zero-class root outside its forest
would trigger an earlier special stop, so root and hole share a forest; the complete
zero-class fence and whole assembly now follow. `standard_finiteLegal` proves finite
legality for every standard source, and complete d+2-row encoded legality no longer
needs extra source hypotheses. `expand_total_finiteLegal` supplies an actual legal
result for every positive dimension, finite-legal input, and index;
`standard_expand_total` connects this to the whole seed-reachable domain. Repeated-step
termination, the remaining SB/G block-order conditions,
concrete coverage, and target standardness remain unproved.
[All-branch HW closure](../../lean/BTnSSBMS/src/BTnSSBMS/SourceHWClosure.lean)
now establishes `standard_HW`: every attachment list is hereditarily nonincreasing
on the entire seed-reachable domain in every positive dimension. Low classes
include zero; the highest class uses the exact previous-phase pruned donor,
and strict last-hole decrease preserves comparison with earlier sibling forests.
BN, SB and G are not assumed, and HW is not built into standardness. This closes
one standard-domain invariant, not the remaining block conditions, target
standardness or the upper bound.
[BN](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBN.lean) is now defined using complete
blocks of same-forest heads with the same computed zero-parent, and proved for every
diagonal seed. Terminal deletion and nonincreasing last-attachment changes preserve it.
[Special copying](../../lean/BTnSSBMS/src/BTnSSBMS/BNSpecial.lean) covers the actual
stopping layer and all copy counts; [all index-zero branches](../../lean/BTnSSBMS/src/BTnSSBMS/BNPruning.lean)
are connected to the original FS. [Complete-block transport](../../lean/BTnSSBMS/src/BTnSSBMS/RelocationBlocks.lean)
separately proves that actual numerical copying at a verified transport entry commutes with zero-block truncation.
[A genuine common-entry reduction](../../lean/BTnSSBMS/src/BTnSSBMS/SiblingEntry.lean)
now moves earlier sibling syntax forward without changing it, deriving all parent rows.
[Complete cross-entry comparison](../../lean/BTnSSBMS/src/BTnSSBMS/SiblingComparison.lean)
and actual suffix-entry recovery then establish
[BN for complete ordinary transport](../../lean/BTnSSBMS/src/BTnSSBMS/BNRelocation.lean),
including arbitrary nested attachments. [Root assembly](../../lean/BTnSSBMS/src/BTnSSBMS/BNRootCopy.lean)
includes the actual forced root; the first low-class instance constructs its own transport state.
[The positive-floor splice](../../lean/BTnSSBMS/src/BTnSSBMS/BNSplice.lean) now handles
every new external zero-sibling block at any hole depth. The actual floor and terminal
comparison are derived [for every positive low-class copy](../../lean/BTnSSBMS/src/BTnSSBMS/BNPositiveCopies.lean),
then [assembled into the whole frozen source branch](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNPositive.lean).
`ordinary_positive_expand_BN` covers `0 < cap < d`, including BT3SS's `cap=1` branch,
with no bound on forest depth or copy count.
[Highest-class BN](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNHigh.lean) now connects the strict
seam of the actual previous-phase donor. [Class-zero BN](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNZero.lean)
uses a complete first-root-block identity, retains earlier sibling comparisons and lifts
through the entire outer spine. [All-branch closure](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNClosure.lean)
proves `standard_BN` for all seed-reachable terms in every positive dimension, without
assuming BN in standardness or relying on SB/G.
**Source BN is complete; all target BMS BN/SB, standardness and the full upper bound remain open.**
The [ordinary-copy partial-rebase comparison](../../lean/BTnSSBMS/src/BTnSSBMS/PartialRebaseCopyComparison.lean)
now preserves the full three-way comparison under the literal source copies, including
arbitrarily nested forests and complete root blocks. Exact root-parent correspondence
is constructed for ordinary copied heads, rather than inferred from ancestor preservation.
This does not cover a forced root, a rewritten terminal, or cross-copy SB assembly.
The [owned-donation key lemma](../../lean/BTnSSBMS/src/BTnSSBMS/DonationInternalKey.lean)
also proves a genuine internal column's key strictly below the donor key when the
original upper comparison with the donor-plus-empty-forest key is available.
It uses recursive size only to exclude equality, not as a substitute for key order.
These are local ingredients of the still-open source SB/G closure.
The [source SB definition and seeds](../../lean/BTnSSBMS/src/BTnSSBMS/SourceSB.lean)
now include actual open owners and complete historical blocks. Every diagonal seed
satisfies SB at every applicable level. [Actual outer zero deletion](../../lean/BTnSSBMS/src/BTnSSBMS/SBDeletion.lean)
preserves it by proving the surviving blocks unchanged and updating all recursive
histories. Other expansion branches, and hence standard-domain SB closure, remain open.
[Same-class cross-copy exclusion](../../lean/BTnSSBMS/src/BTnSSBMS/SBCopyAncestry.lean)
now derives the needed source ancestor path from actual target ancestry and the
literal next-phase root parent table. The underlying exact-parent reflection does
not require the exceptional forced root to have ordinary transported parents.
[Exact nested copying](../../lean/BTnSSBMS/src/BTnSSBMS/ExactCopyHole.lean) now
derives ordinary-position exactness at arbitrary-depth actual hole contexts,
while retaining the visible-map prefix and exempting the forced root.
The [reset-gap argument](../../lean/BTnSSBMS/src/BTnSSBMS/ExactCopyBarrierPath.lean)
then forces a cross-copy ancestor through the new root.
[Consecutive-copy exclusion](../../lean/BTnSSBMS/src/BTnSSBMS/SBConsecutiveCopies.lean)
constructs both actual holes and their restart. For `0 < copyClass = testedRow < d`,
it excludes earlier ordinary partners of all represented next-copy visible positions
and the terminal, without assuming the source path, exactness or root-barrier path.
[The roots themselves form lower-row chains](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRootChain.lean).
[Actual hole density](../../lean/BTnSSBMS/src/BTnSSBMS/CopyHoleDensity.lean) now derives
continuous translation and surjectivity over the entire root-to-hole visible interval
from literal copy lengths, strict increase and frontier agreement.
[Finite copy-hole iteration](../../lean/BTnSSBMS/src/BTnSSBMS/CopyHoleRun.lean) constructs
the protected prefixes and root chains for every finite number of original copies.
[Separated-copy exclusion](../../lean/BTnSSBMS/src/BTnSSBMS/SBSeparatedCopies.lean) consequently
covers all actual positions of those intervals across arbitrary finite copy gaps,
still with `0 < copyClass = testedRow < d` and an earlier ordinary partner.
Full scoped-entry enumeration in the final spliced material, earlier forced-root partners,
other tested rows, donation and delayed block changes remain open; full SB closure is not proved.
[Forced-root complete-block rebasing](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunRootBlock.lean)
now proves that, across any positive finite gap of actual copied-hole iterations,
rebasing the earlier unspliced template's complete root block gives the later template's block.
Scopes, fixed prefixes, ancestry and shared parents are derived from the run; all
nested attachments and the whole tail are retained.
[Hole-splice transport](../../lean/BTnSSBMS/src/BTnSSBMS/RelocationSplice.lean) separately
commutes canonical transport with arbitrary terminal replacement at the computed
entering contexts. Unspliced template identities alone cannot supply SB inequalities
between the actual spliced historical blocks; the subsequent whole-run result below does handle forced-root pairs.
[Actual historical-copy rebasing](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunSplicedMaterial.lean)
now identifies the rebase of the complete earlier `copies` result as the later
template spliced with the canonically transported entire remaining run, for
positive low numerical classes and arbitrary finite copy gaps. Replacement
legality and owner separation are extracted from the actual complete result.
[Fixed-phase copy-count monotonicity](../../lean/BTnSSBMS/src/BTnSSBMS/CopyCountOrder.lean)
is also proved. [Whole-run naturality](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunNaturality.lean)
now identifies the transported remainder with the entire phase-shifted run:
hole-map composition, high-parent preservation and the next reset are proved inside
the induction. [Actual run rebasing](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunRebase.lean)
constructs the entering conditions from the real copy-hole iteration, for arbitrary
positive finite gaps. It gives the forced-root SB inequality whenever the later run
has no more copies. This does not prove all source SB pairs, donations or whole-source closure.
The new [actual expansion descent theorem](../../lean/BTnSSBMS/src/BTnSSBMS/SourceDescent.lean)
proves strict source-comparator decrease for every positive dimension, finite-legal
nonempty input, and index, across every actual branch and arbitrary finite depth.
The first low-class copy decreases at the selected coordinate; the highest class
preserves its coordinate vector and strictly prunes its first attachment list.
A nonempty term therefore cannot return to itself by a finite path after one
expansion; its actual raw matrix encoding also strictly decreases.
This supplies a premise of the delayed-change argument, **not complete block-order
preservation, target standardness, or termination of infinite expansion**. Raw
matrix descent is not simulation by actual BMS fundamental-sequence steps.
The continuation also establishes strictly increasing position representatives,
the complete-output numerical-first-difference comparison, and exact agreement
between complete normalized keys and arbitrary-depth finite-legal attachment order.
The same-gap recursive comparison is now proved, including early forest/list exits:
`encode_strict_order` proves strict comparison of the complete actual outputs for
arbitrary-depth finite-legal inputs. `standard_compare` and `standard_injective`
connect exact comparison and injectivity on the whole source standard domain.
This is an order-faithful injection into raw fixed-width matrices, not a substitute
for all block conditions, coverage or target standardness.
The complete encoder now has a computed key-parent classification: parents are
definition columns or self-registering binding representatives. All actual forest
slots are traced through the execution and only save earlier bindings; no slot can
gain strict key-row descendants after later appends. Tag-2 guards are leaves in
that row as well. These facts hold on the whole source standard domain, but are
not yet an exhaustive classification and comparison of target blocks.
The actual first-output trace now classifies numerical columns: source entries
have only tag-zero numerical parents, whereas auxiliaries share one tag-1 or tag-2
parent in every numerical row. Intermediate SB pairs on the whole standard domain
therefore have two source-entry endpoints, and row-zero siblings cannot mix these
types. Source-scope/whole-block correspondence and the rebased inequalities remain.
Source binding provenance is now checked throughout actual execution as well:
each queried latest pointer has a unique visible source origin that is strictly
earlier, on the highest numerical ancestor chain, and not an open forest owner.
Forest entry and exit preserve this statement without leaking local bindings.
Actual partial-rebase entry now constructs the required numerical transport and
preserves complete finite legality. Separate copy and normalization histories
prove exact equality of the rebased root's full key, and comparison is preserved
when two materials undergo one common rebase. The next bridge is now checked:
closed-list transplantation is legal and preserves its full key, transplantation
commutes with numerical transport as complete syntax, and cross-entry ancestor/current
key comparisons are preserved. Canonical transport is proved equal to the original
activation-and-shift copy; both same-copy unchanged attachments and a fixed external
ancestor are covered, with explicit finite entry conditions. Every saved latest binding
is now identified with its actual source attachment at every real query, including
the material's original finite legality and the query's numerical entry. Recomputing
the keys from these materials preserves actual smaller-key filtering, equal-key lookup
and exact first key-row heights, and is connected to the literal copy for unchanged
same-copy lists and fixed external lists. At that stage the connection to the whole
new execution, replacement/cross-copy cases, complete block transport and BN/SB remained.
The latest extension pairs two actual executions under explicit numerical-entry
and initial-frame conditions. Fresh/reuse decisions, latest-position updates,
forest entry and restoration preserve the key/height relation. Mutual recursion
proves that actual appended key/tag rows agree column by column, hence so do output
length increments. Final outer maps, numerical views and all visible-frame pairs
are constructed. The theorem also applies to the frozen activation-and-shift copy.
The intermediate-row partial-rebase root entry is now initialized: old material
keys in the shared prefix stay fixed, the real parent search queries the same
saved frame, and the complete root key agrees. Fresh/reuse agreement and all
after-root visible frame pairs are derived. Each real forest slot is initialized
before recursive transport, covering arbitrary nested forests and the outer tail.
`partial_rebase_encode_control` connects identical actual key/tag output to the
frozen activation copy, with no extra root-query, branch-agreement or initial-frame
pairing hypotheses. Actual first-output snapshots, finite legality, numerical views
and material origins are now recovered across the entire execution. Every visible
source position has its genuine original entry with exact lexical prefixes,
including open owners represented by slots. Thus `standard_visible_partial_rebase_control`
derives historical prefixes and full control transport from actual source root
geometry; shared endpoint parents reflect once that origin is identified.
Numerical fibers now recover the visible source origin of every intermediate
numerical-row SB pair, reflecting ancestry and the shared cut parent rather than
using chronological order as lexical inclusion. Complete control-row transport
therefore applies to all these actual pairs, with equal appended lengths.
Numerical ancestry is equivalent in both directions at the corresponding origins,
and the actual source/target activation thresholds agree. The rebased first
column's low numerical rows take the destination's encoded values; its high rows
retain their original values. Complete internal numerical-row transport is now
combined with the control rows: every intermediate pair's full local output
interval equals the actual phase-one BMS copy in all d+2 rows. Boundaries are
proved separately: each real entry's root block stays inside its lexical
execution, and ancestry-sensitive row-zero translation preserves its exact
length. Thus
[`standard_intermediate_pair_block`](../../lean/BTnSSBMS/src/BTnSSBMS/CompleteBlockTransport.lean)
identifies the **complete actual target blocks** before and after rebasing,
without treating an entire lexical suffix as a block. Complete source-block
boundaries are now proved too: outer truncation retains all attached forests,
and its encoding exactly fills the target root block.
[`standard_intermediate_source_block`](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBlockTransport.lean)
connects the original rule's complete-source-block rebase to the target block.
[`standard_intermediate_block_compare`](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBlockComparison.lean)
then derives equality of their three-valued comparisons in the actual entry
environment, without assuming source SB.
The [closing-block formula](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingBlockEncoding.lean)
also identifies the complete block at every actual restored representative,
including fresh closing P's: remove all output strictly before that representative
from the complete source-block encoding. The remainder is exactly its global
closing block. This does not identify the closing P with the first output or
establish all highest-row comparisons. Source SB preservation on the standard
domain, source G, and the highest rows,
all target BN/SB, concrete coverage and target standardness remain open; the reduction
does not prove that the source comparison is never less.
The new endpoint proofs identify all self-registered representatives with actual
source closing entries, exhaust zero-tag outputs into closings or slots, and
exhaust positive-tag outputs into fresh definitions or their guards. Equality
of the two highest actual parents of a positive-tag output then gives
[`standard_top_pair_classes`](../../lean/BTnSSBMS/src/BTnSSBMS/TopRowEndpointClasses.lean):
every highest tag-row pair is closing/closing or closing/slot on the entire
standard source domain, with the source entries constructed. No source SB/G or
target-standardness premise is assumed. The lower key-row classification and
the two highest-row block inequalities are still open.
For the P/P case, [exact closing origins](../../lean/BTnSSBMS/src/BTnSSBMS/VisibleClosingOrigins.lean)
now recover the genuine non-owner source ancestor and its original closing
position. [Frame extension](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingFrameExtension.lean)
preserves all old keys and pointers literally, appends a nonempty binding list,
and identifies the height difference as twice its length.
[Complete key order](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingKeyOrder.lean) proves
strict key increase. These are actual-recursion theorems without source block-order
premises, but do not yet prove insertion domination for complete blocks.
[Insertion queries](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingQueryInsertion.lean) now
give the three actual closing-frame height regimes, including the strict
old-fresh/new-reused case. [Complete head saving](../../lean/BTnSSBMS/src/BTnSSBMS/InsertionHead.lean)
connects the key splice after real forest returns.
[Query ancestry](../../lean/BTnSSBMS/src/BTnSSBMS/QueryAncestry.lean) and
[reverse recovery](../../lean/BTnSSBMS/src/BTnSSBMS/QueryAncestorRecovery.lean) now
characterize actual query-head key-row activation throughout the standard source
domain: the older representative must be retained in the queried smaller-key
frame. An absent representative cannot receive the insertion shift.
[Rekeyed insertion](../../lean/BTnSSBMS/src/BTnSSBMS/RekeyInsertion.lean) and its
[actual activation bound](../../lean/BTnSSBMS/src/BTnSSBMS/InsertionActivation.lean)
allow genuinely changed complete keys after relocation; their local bounds
still require an activation-gated interval.
[Bounded splices](../../lean/BTnSSBMS/src/BTnSSBMS/KeySplice.lean),
[complete heads](../../lean/BTnSSBMS/src/BTnSSBMS/SplicedSaving.lean) and
[outer execution](../../lean/BTnSSBMS/src/BTnSSBMS/EncoderSpliceTransport.lean)
now prove that saved frames can only remove unmatched keys from one fixed
initial pool, even when fresh/reuse branches or internal output lengths differ.
[Actual closing entry initialization](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingSpliceEntry.lean)
constructs the starting relation from a strict closing-ancestor pair.
[Complete outer-tail transport](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingSpliceTransport.lean)
preserves it at every later visible position, including forest returns and
subsequent external-parent queries. Initial pairing and outer-run splicing
are no longer assumed. [Root gates](../../lean/BTnSSBMS/src/BTnSSBMS/RootedSplice.lean)
now strengthen the relation: every unmatched key is above a retained binding
still pointing to the original root. Actual filtering, saving,
[closing initialization and outer-tail transport](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingRootedTransport.lean),
and [forest-slot entry](../../lean/BTnSSBMS/src/BTnSSBMS/RootedSlots.lean) preserve the gate.
[Query bounds](../../lean/BTnSSBMS/src/BTnSSBMS/RootedQuery.lean) use the actual BMS
activation threshold: inactive roots give equal heights, while equality at the
maximum shift forces all inserted keys to survive and matching fresh/reuse branches.
[Actual first-column comparison](../../lean/BTnSSBMS/src/BTnSSBMS/RootedHeadComparison.lean)
now gives strictness or equality with matching branches.
[Auxiliary alignment](../../lean/BTnSSBMS/src/BTnSSBMS/FreshShift.lean) follows from
computed activation, and [actual closing initialization](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingRowEntry.lean)
constructs the root gate and row differences together.
[Complete-head decisions](../../lean/BTnSSBMS/src/BTnSSBMS/RootedDecision.lean)
extend strict first-column differences through arbitrary continuations, and
cover complete heads when at least one side reuses a definition.
[Complete mutual comparison](../../lean/BTnSSBMS/src/BTnSSBMS/RootedComparison.lean)
now handles fresh/fresh forests and outer tails of arbitrary finite depth,
allowing unequal lengths after strictness and restoring the owner's entering
frame for each sibling forest.
[Actual closing initialization](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingInsertionComparison.lean)
derives all entering conditions; [exact block slices](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingBlockSlice.lean)
connect the output interval to actual BMS rebasing.
[`standard_closing_block_insertion`](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingBlockComparison.lean)
therefore proves that the transported old block tail, encoded at the new closing
entry and including the closing column, is bounded by the actual target rebase
of the old complete block, for all standard closing-ancestor pairs.
The new entry's own block has yet to be bounded by that transported material;
the proved inequality must not be confused with final target SB.
The last verified full build covers 297 modules and 1777 reports, including 127 public theorems
in the forty-nine recent partial-rebase transport, source SB, exact-hole, interval-density, finite-copy,
forced-root block, hole-splice, spliced-material, count-order, seam-transport, hole-map and whole-run modules;
source hashes, dependency order and report completeness have also been checked. These totals
do not certify the main upper bound.
The complete
standard-domain order embedding and displayed ordinal bound are **not yet
Lean theorems**. This does not change the scope of the earlier collection receipt.

- [Full English main paper](upper-bound.md) · [中文主证明](upper-bound.zh-CN.md).
- [Frozen definitions and finite invariants](source-finite/definitions-and-invariants.zh-CN.md): the retained sections 1–3 of the earlier BTnSS paper, with 18 supporting finite-combinatorial manuscripts. The later model-theoretic sections are excluded.
- [Pruned context encoder](lemmas/context-encoder.zh-CN.md): finite output, exact parent table, fixed-context order, and middle-row transport.
- [Owner-entry key decrease](lemmas/owner-entry.zh-CN.md) and [partial-rebase key comparison](lemmas/partial-key-comparison.zh-CN.md).
- [Cross-leaf extension](lemmas/cross-leaf.zh-CN.md), [top-two-row transport](lemmas/top-row-transport.zh-CN.md), and [first-diagonal lemma](lemmas/first-diagonal.zh-CN.md).

The main paper is available in both languages. Supporting manuscripts retain their full Chinese arguments; they are not English translations. Historical completion claims are retained as provenance, not endorsed by the current audit; the proof status above takes precedence.

## Row count and nonstandard matrices

Here $d=n-1$ is the number of source numerical coordinates. The encoder uses $d+2=n+1$ target rows. In particular the intended bound specializes to

$$
\lim(\mathrm{BT3SS})\le |(0000)(1111)(2222)(3333)|<|(00000)(11111)|.
$$

**The BT3SS specialization is not yet a complete proof either.** Fixing $d=2$
reduces the intermediate numerical block conditions to SB₁, but does not bound
attachment depth or remove source block-order preservation and concrete
standardness coverage. Complete-block insertion domination is now proved;
the new entry's own block still requires comparison with the transported
material. Final block order and coverage in the BT3SS-specific argument remain
open. Removing the dimension quantifier does not establish them.
This concerns the BMS upper-bound proof, not a refutation
of a separate BT3SS well-ordering proof.

The distinction between raw matrices and standard terms is essential. A numerically legal $r$-row matrix starting with zero is lexicographically below $B_{r+1}$ after zero padding; this alone does not assign it an ordinal below that bound. The raw legal lexicographic order even contains

$$
(0)(1)>_{\mathrm{lex}}(0)(0)(1)>_{\mathrm{lex}}(0)(0)(0)(1)>_{\mathrm{lex}}\cdots.
$$

That is not asserted to be an FS descent. For the encoded matrices the proposed proof still needs all finite block conditions, then finite coverage and standard BMS well-ordering to establish target standardness. Neither arbitrary raw matrices nor a raw lexicographic bound may be substituted for that step.

## Frozen sources and evidence

The two definitions are pinned to NER revision `c539d8f68c5553da2d681c1251ea443b6b735e62`:

- [strong BT*(-1)Y-nSS v2](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/Minus1_Y_nSS-series/BT_star_Minus1_Y_nSS-v2.ts).
- [BMS source, default BM4 short FS](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/BM.ts).
- Rachel Hunter, [*Well-Orderedness of the Bashicu Matrix System*](https://arxiv.org/abs/2307.04606), for the target well-ordering theorem.

The [manifest](MANIFEST.json) records original and collected hashes, the exact excerpt range, editorial changes and frozen rule hashes. It imports 26 mathematical manuscripts and one [historical audit receipt](verification.json), unchanged except for LF line endings. This addition redistributes no private source PDF, upstream implementation, or old experiment scripts; it adds no notation kernel or Lean project. Historical script filenames and the receipt's original `repository_changes` field describe the earlier research run, not this publication.

The receipt distinguishes standard-path samples from raw numeric/finite-invariant samples, caps and a timed-out run. Batches overlap. These are finite error-finding checks, not a proof of universal correctness. To check the **collected files**, links and hashes, run from the repository root:

```sh
node research/btnss-bms/tools/validate.cjs
```

The validator is not a mathematical proof checker. The collector is provided for provenance and requires the original workspace as an explicit argument; it is not needed to read or validate a fresh clone.
