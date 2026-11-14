# BTnSS → fixed-row BMS: partial Lean development · [中文](README.zh-CN.md)

[Paper](../../research/btnss-bms/upper-bound.md) · [Build receipt](VERIFICATION.json)

**The complete upper-bound theorem is not proved or formalized yet.** Complete
block transport, standard-domain invariants and concrete coverage in the original
argument still require mathematical proofs, not merely Lean translation. This
independent Lean 4.33.1 project checks concrete components of the published argument. It
does not turn the missing encoding, finite-invariant, or standardness lemmas
into axioms. None of the seven existing notation projects is changed.

**Restricting to BT3SS (`d=2`) does not complete this BMS upper-bound proof.**
It reduces the intermediate numerical-row conditions to `SB₁`, but attached
forests still have arbitrary nesting depth. Although insertion domination for
strict closing-ancestor pairs is now proved, it does not establish
the remaining SB/G block-order preservation, concrete coverage or target standardness.
Source BN is now proved on the whole standard domain by `standard_BN`; those other
obligations remain. The verified four-row raw order embedding and uniform raw
ceiling do not replace them. This concerns our BT3SS-to-BMS comparison argument,
not a refutation of the separate external BT3SS well-ordering proof.

The intended theorem is, for source numerical dimension `d = n - 1`,

\[
\lim(\mathrm{BTnSS})\le |U_{d+2}|<|B_{d+3}|,
\qquad U_r=(0^r)(1^r)(2^r)(3^r).
\]

## Kernel-checked components

- [Syntax](src/BTnSSBMS/Syntax.lean): finite recursive columns and lists of
  attached forests, diagonal seeds, comparison, and faithful equality tests.
  An empty attached forest remains a slot; it is not an absent attachment.
- [Parents](src/BTnSSBMS/Parents.lean): finite lower-parent searches, scope
  restoration, parent indices strictly earlier than the current column,
  annotation erasure, and preservation of node/slot counts. Appending an actually
  computed label preserves context validity, so the search follows stored parents
  without triggering its malformed-context guard.
- [Parent-chain inclusion](src/BTnSSBMS/ParentChains.lean),
  [activation semantics](src/BTnSSBMS/Activation.lean), and
  [coordinate differences](src/BTnSSBMS/ParentValues.lean): computed high-row
  ancestry implies every lower-row ancestry. The actual BMS activation threshold
  means precisely bounded row ancestry. Root-to-endpoint readings strictly
  increase, so the copy's Nat subtraction recovers the genuine difference.
  These facts hold for arbitrary raw matrices, without assuming standardness.
- [Search geometry](src/BTnSSBMS/SearchGeometry.lean): prefix locality, lower
  bounds on skipped ancestors, and the exact consecutive-interval description
  of the row-zero descendant cone.
- [Row record chains](src/BTnSSBMS/RowGeometry.lean): higher-row ancestry is
  characterized by a coordinate barrier on lower-row paths. Searching for an
  ancestor's value plus one from any of its same-row descendants returns exactly
  that ancestor. [Parent transport](src/BTnSSBMS/NumericalTransport.lean) uses this
  to identify the first d computed parents of an emitted head, beyond pointer bounds.
- [Scope restoration](src/BTnSSBMS/NumericalScope.lean): `source_numerical_view`
  proves that the complete real encoding preserves numerical ancestry for every
  finite input satisfying `ForestSeparated`. **All nested forest calls and outer
  scope restoration are included**, rather than assumed as recursive premises.
  This literal finite condition requires each attached forest's outer columns
  to have row-zero values above their owner, recursively throughout the input.
  [Path stretching](src/BTnSSBMS/ViewExtension.lean),
  [auxiliary parents](src/BTnSSBMS/AuxiliaryParents.lean),
  [forest fences](src/BTnSSBMS/ForestFence.lean), and
  [slot/closing-column scope](src/BTnSSBMS/ForestScope.lean) supply the actual D,
  H, slot and closing-P cases.
  `NumericalView` now also requires strictly increasing position representatives.
  Real append, forest entry/exit, first-copy entry and seam reset preserve this
  stronger invariant; ancestry preservation alone is not treated as injectivity.
- [Numerical unit steps](src/BTnSSBMS/NumericalUnits.lean): under the same finite
  condition, `source_unitSteps` proves that **every actual output column** is
  zero without a parent and parent-plus-one otherwise in its first d rows.
  No source unit-step hypothesis or finite depth/size bound is used.
  These two modules only handle the first d rows; the key/tag rows are covered
  by the complete legality result below. `SourceFiniteClosure` now supplies
  `ForestSeparated` throughout the source standard domain.
- [Saved-binding ancestry](src/BTnSSBMS/KeyScope.lean): `source_framesAncestral`
  proves that each saved binding's latest position and existing definition are
  actual key-row ancestors of the carrying column throughout complete recursion.
  [Ancestor cuts](src/BTnSSBMS/FrameAncestry.lean),
  [definition/reuse entries](src/BTnSSBMS/KeyEntries.lean), and
  [forest key scopes](src/BTnSSBMS/KeyForestScope.lean) identify computed parents
  of new D, reused P, H, slots and closing P via the actual
  [higher-row search](src/BTnSSBMS/KeyParentGeometry.lean).
- [Complete output legality](src/BTnSSBMS/FullLegality.lean):
  `source_numericallyLegal` proves unit legality in **all d+2 rows of every output
  column**, including keys and tags, and totality of any single BMS expansion of
  that encoded matrix. Its finite source premises are forest separation and an
  actual highest numerical parent for every column with attachments.
  [Source finite legality](src/BTnSSBMS/SourceLegality.lean) derives both premises
  from the paper's ordinary finite conditions: width, numerical unit increments,
  positive owners, and forest separation. Thus `finiteLegal_source_numericallyLegal`
  does not assume target parents, target legality, or recursive preservation.
  All-branch source preservation is now connected below. **Numerical legality
  still does not establish BMS standardness, BN/SB, or order preservation.**
- [Numerical legality](src/BTnSSBMS/NumericalLegality.lean): the finite actual-table
  condition "zero without a parent, parent plus one otherwise" implies that
  `BMS.expand?` always returns a result. **Preservation of this condition on all
  standard source/target expansions is not asserted here.**
- [First diagonal](src/BTnSSBMS/BMSBlocks.lean): concrete complete row-zero blocks
  coincide with descendant cones. On numerically legal matrices, BN together with
  `SB₁,...,SB_(k−1)` and a strict row-k descendant forces the block's second column
  to be root plus one in its first k+1 coordinates. The theorem is connected to
  actual whole-block and ancestor-sensitive rebase comparisons and **does not use
  `SB_k`**. Its [row-reduction proof](src/BTnSSBMS/FirstDiagonal.lean) is separate.
- [Copy/rebase correspondence](src/BTnSSBMS/CopyRebase.lean): under fixed width and
  the stated cut-length condition, the actual first BMS copy equals the corresponding
  prefix of the whole rebased block. At an actual selected parent, containment of
  the copied interval follows from ancestry, without an extra assumption.
  This is a universal identity, not a sample check;
  it does not yet establish the complete last-hole covering argument.
- [Source expansion](src/BTnSSBMS/SourceFS.lean): numerical and highest-key parents,
  stopping layers, the special forest branch, activation, copies, previous-phase
  donation, finite paths, and seed reachability. There are no resource thresholds
  in the definitions. A missing root on malformed input returns `none` rather
  than silently becoming zero. `SourceTotality` now proves standard-domain totality;
  **universal correspondence with the frozen external implementation and block
  invariants remain open.**
- [Source deletion and special cases](src/BTnSSBMS/SourcePruning.lean): the actual
  zero-leaf deletion and special branch selected by the real stopping layer are
  total and preserve finite legality, for arbitrary dimensions, indices and
  nesting depths. Each repeated forest is checked in its original owner context;
  internal columns of an earlier replica are never visible in a later replica.
- [Ordinary first-copy heads](src/BTnSSBMS/SourceCopyHead.lean): for any low branch
  `b<d` and actual numerical root, the rule's literal `shift` and `delta` expressions
  yield a head whose computed parents inherit the terminal below b and the old
  root from b upward. Unit increments are preserved; actual ancestry justifies
  the natural-number differences. This module handles the head; the following
  modules handle whole interiors and later numerical seams.
- [Copy histories](src/BTnSSBMS/CopyHistory.lean) and
  [whole interiors](src/BTnSSBMS/CopyBody.lean): histories mean actual bounded
  source ancestry; literal shifted values equal represented-parent-plus-one,
  so recomputed target parents are correct. `copied_finiteLegal` and its forest
  companion preserve finite legality and owner separation through arbitrary
  nested ordinary material, restoring scope on forest exit. `copied` is only
  a composition of the existing annotation, activation and shift operations;
  it is proved equal to the actual no-hole `ascendReplace` branch.
- [Actual copy entry](src/BTnSSBMS/CopyEntry.lean): `first_copy_shiftView` constructs
  the first low-branch entering state from the selected root, original delta,
  and original context, **without assuming the entering transport state**.
  `first_copy_finiteLegal` connects this to a complete root with arbitrary nested
  ordinary material.
- [Later numerical seams](src/BTnSSBMS/CopySeam.lean): when transport has reached
  the original terminal's entering context, `ShiftView.restart` constructs the
  next root and reset view using the original delta and `phase+1`. Earlier
  representatives remain fixed; lower-row stretched paths and higher-row old
  parents are checked. [Annotation compatibility](src/BTnSSBMS/CopyAnnotation.lean)
  proves that the highest key parent appended by the actual `Source.parents`
  cannot change numerical activation when `cap≤d`.
- [Last-hole splicing](src/BTnSSBMS/CopySplice.lean) and
  [hole-context transport](src/BTnSSBMS/CopyHole.lean) compute the actual terminal
  site and owner context, identify structural splicing with `ascendReplace`, and
  carry the numerical view to that computed site. Structural induction handles
  arbitrary nesting and restores every outer scope. The
  [root template](src/BTnSSBMS/CopyRoot.lean) derives the outer material's row-zero
  lower bound from the terminal's actual ancestor path, rather than assuming it.
- [Iterated low-class copies](src/BTnSSBMS/CopyIteration.lean):
  `copies_low_finiteLegal` inducts on the actual `copies` count. It covers `0<b<d`
  at arbitrary hole depths, and `b=0` when root and hole are in the same forest.
  Each next entering view, the entire replacement's legality and its owner fence
  are constructed within the induction, not supplied as replacement hypotheses.
  `initial_copies_low_finiteLegal` constructs the initial view and literal delta
  from the selected numerical root. `rooted_low_expansion_finiteLegal` installs
  all copies back into the original root template, including the zero-phase splice.
  Actual marks, delta and whole-term assembly are now connected for positive
  low classes by the theorem below. The zero-class modules further below now supply
  its full outer-owner fence and exclusion of cross-forest cases by the stopping rule.
- [Highest-class donation seams](src/BTnSSBMS/CopyDonation.lean): the new root at
  `phase+1` equals the virtual terminal vector at `phase`. Consequently, the whole
  previous-phase donated forest is legal and owner-separated in its actual new
  owner context, with arbitrary nesting. The next ordinary root view is also
  constructed. [Donation material](src/BTnSSBMS/DonationMaterial.lean) identifies
  the donor with the terminal list minus its last forest, proves uniqueness of
  correct activation histories, and proves the first donor's zero-shift identity.
  [Highest-class iteration](src/BTnSSBMS/DonationIteration.lean) proves legality of
  the actual `copies` at every finite count, including each first-list replacement.
  Initial entry and donation are constructed from the original template, and later
  donors from the preceding actual transport state, before splicing back into the
  root template. The whole high-class modules below now connect these template
  theorems to the original `expand?`, deriving the numerical ancestor, actual donor
  history, and outer splice within the proof.
- [Actual root search](src/BTnSSBMS/SourceRootSearch.lean), the
  [scoped spine](src/BTnSSBMS/SourceSpine.lean), and the
  [stopping hole](src/BTnSSBMS/SourceSpineHole.lean) connect literal
  `locateRoot`/`spine`/`drop` selections to a nonempty finite-legal numerical root
  template. Its entering-context length is exactly the absolute root index;
  closed forests do not leak into that context. The selected layer's last column
  is the computed copy hole, whose context is unchanged when the root prefix is dropped.
- [Highest-parent scope](src/BTnSSBMS/SourceTopScope.lean) and
  [actual highest-class selection](src/BTnSSBMS/SourceTopSelection.lean) prove that
  every actual highest key parent is earlier and outside the whole open-owner list,
  for every finite source. `selected_top_root_tail` connects this to the selected
  stopping layer, `highestParent` and `locateRoot`, and proves that the root suffix
  has a nonempty tail, **without assuming non-ownership or tail nonemptiness**.
  These modules handle successful searches; `SourceTotality` below establishes
  that every required lookup succeeds on finite-legal positive-dimensional inputs.
- [Annotated spine](src/BTnSSBMS/SourceAnnotatedSpine.lean) and
  [actual marked pieces](src/BTnSSBMS/SourceMarkedSpine.lean):
  `actual_marked_root_piece` identifies the literal `mark/spine/drop` material with
  the iterative-copy template, including every nested forest and activation mark.
  Pre-root history is exactly zero, not merely erased by a projection.
  [Parent-prefix truncation](src/BTnSSBMS/SourceParentPrefix.lean) recovers the entire
  numerical annotation after removing the appended highest-parent fields. Thus
  an actual low-class selection is the computed terminal's actual numerical parent.
- [Root-to-terminal geometry](src/BTnSSBMS/SourceRootHole.lean) and
  [original difference vectors](src/BTnSSBMS/SourceRootCoordinates.lean) compose
  scoped layer lookups and identify the template hole with the whole-source terminal.
  The frozen visible-column lookup reads exactly the template's first vector;
  no substitute delta is supplied to the copy theorem.
- [Whole positive low-class preservation](src/BTnSSBMS/SourceLowAssembly.lean):
  `expand_positive_low_finiteLegal` proves finite legality of the **whole output**
  for every successful actual `expand?` step selected in `0<b<d`. Root selection,
  marking, all replicas and the full outer splice are joined. The owner fence
  follows from the first copy's row-zero value equalling the original terminal;
  it is not a replacement-material assumption. **This module does not prove success
  or handle zero class; highest class is handled by the next group of modules.**
- [Numerical ancestry of the highest parent](src/BTnSSBMS/SourceTopAncestry.lean):
  `selected_top_numerical_ancestor` proves that the actual highest key parent is a
  highest-numerical-row ancestor in the stopping column's original numerical context,
  for every finite source in positive dimension. Appended parent fields are truncated
  and forest scopes restored explicitly; neither standardness nor the ancestor path
  is an input assumption.
- [Actual donor history](src/BTnSSBMS/SourceMarkedHistory.lean): the literal marking
  history matches numerical ancestry before, at, and after the root. Closed forests
  do not enter the outer history. `actual_marked_top_donation` identifies the actual
  terminal donor with the material used by the iteration theorem, including all
  activation marks, not merely after erasure.
- [Whole highest-class preservation](src/BTnSSBMS/SourceHighAssembly.lean):
  `expand_high_finiteLegal` proves finite legality of the **whole output** of every
  successful actual `expand?` step with `b=d>0`. The actual ancestor, non-owner root
  suffix, initial and later donations, arbitrary copy count, outer splice and owner
  fence are all connected. Zero class and lookup totality are handled below;
  block-order invariants remain unproved.
- [Highest-parent existence](src/BTnSSBMS/SourceTopExistence.lean) and
  [low-class leaves](src/BTnSSBMS/SourceLowLeaf.lean): every column with a nonempty
  attachment list in a positive-dimensional finite-legal source has an actual
  highest key parent. A zero-valued point on the highest numerical chain has
  empty key and cannot be an open owner, so the search cannot lose its root.
  Consequently all low-class stopping columns are leaves, including dimension one;
  leafness is not an added source restriction.
- [Zero-class geometry](src/BTnSSBMS/SourceZeroGeometry.lean) and
  [first-stop selection](src/BTnSSBMS/SourceZeroSelection.lean): all higher coordinates
  of a zero-class stopping leaf vanish. If its root were outside the current forest,
  separation and unit increments would force that root to be the owner and trigger
  the original special test one layer earlier. Thus the literal root and hole must
  be in the same forest.
- [Whole zero-class preservation](src/BTnSSBMS/SourceZeroAssembly.lean):
  `expand_zero_class_finiteLegal` joins all actual zero-class replicas and the outer
  splice. The owner fence uses the original same-forest root's lower bound, rather
  than incorrectly claiming the new head equals the terminal.
- [All-branch finite closure](src/BTnSSBMS/SourceFiniteClosure.lean):
  `expand_finiteLegal` covers every successful actual expansion.
  `standard_finiteLegal` extends this along real finite paths from all diagonal seeds.
  `Encoder.standard_numericallyLegal` therefore establishes complete d+2-row encoded
  legality on the whole source standard domain, with no additional source separation
  or unit-step assumption.
- [Stopping totality](src/BTnSSBMS/SourceStopTotality.lean) and
  [full expansion totality](src/BTnSSBMS/SourceTotality.lean): a first stop exists and
  does not accidentally select an empty forest on nonempty input. Every nonzero
  stopping column has a parent; the root lies in the visible prefix, and annotation
  and marking preserve all needed positions. `expand_total_finiteLegal` supplies
  an actual result and its legality for every positive dimension, finite-legal input,
  and index. `standard_expand_total` connects this to the entire seed-reachable domain.
  **These are single-step totality and finite closure, not termination of repeated
  expansion or the BN/HW/SB/G block-order invariants.**
- [Last-position comparison](src/BTnSSBMS/SourceLastOrder.lean),
  [actual top parents of leaves](src/BTnSSBMS/SourceLeafParents.lean), and
  [first-copy descent](src/BTnSSBMS/SourceCopyDescent.lean) now join the
  [actual expansion descent theorem](src/BTnSSBMS/SourceDescent.lean).
  `expand_lt` proves strict decrease in the source recursive comparator for every
  positive dimension, finite-legal nonempty input, and index, without block-order
  assumptions. Low classes first differ at their selected numerical coordinate;
  the highest class preserves its first coordinate vector but strictly prunes
  the first attachment list. Actual root selection, special copies, and arbitrary
  nesting of the terminal splice are covered. `no_return_after_step` excludes
  a finite return to a nonempty starting term after one expansion, and
  `standard_expansion_lt` transfers strict descent to the raw matrix encoding.
  **This supplies the strict-change premise of the paper's delayed-change
  argument, not complete block preservation, BMS expansion simulation, target
  standardness, or well-foundedness. No finite cycles does not exclude an infinite
  descent.**
- [Forest order](src/BTnSSBMS/SourceHW.lean),
  [last-hole splicing](src/BTnSSBMS/HWSplice.lean), and
  [actual transport](src/BTnSSBMS/HWTransport.lean) define and preserve HW:
  every attachment list is nonincreasing in the source comparator, hereditarily
  throughout its forests. This predicate is not added to the definition of standardness.
  [Low-class iteration](src/BTnSSBMS/HWLowCopies.lean) includes class zero and
  constructs each later copy's entering state at the actual transported terminal.
  [Highest-class iteration](src/BTnSSBMS/HWHighCopies.lean) identifies the next
  donor with the current virtual terminal's list minus its last slot, keeping
  previous-phase transport distinct from the current phase. A strictly smaller
  last-hole replacement stays below earlier forests in the same owner's list.
  [All-branch assembly](src/BTnSSBMS/SourceHWClosure.lean) proves `expand_HW` for
  actual deletion, special and every ordinary branch. `standard_HW` establishes
  HW for every seed-reachable term in every positive dimension, with no depth
  or path-length limit. **This standard-domain invariant is closed without
  assuming BN, SB or G. It does not establish those remaining conditions,
  concrete coverage, or the main upper bound.**
- [Source complete-block order](src/BTnSSBMS/SourceBN.lean) now defines BN on
  pairs in the same forest with the same actually computed zero-parent, including
  the parentless case. The compared objects are complete zero-blocks. Attachment
  forests restart independently at their owner context; BN is not built into standardness.
  [Block truncation order](src/BTnSSBMS/SourceBlockOrder.lean) and
  [sibling geometry](src/BTnSSBMS/SourceSiblingGeometry.lean) show that sibling heads
  have the same first coordinate, so the earlier block closes before the later head.
  BN holds for every diagonal seed in every positive dimension.
  [Terminal deletion](src/BTnSSBMS/BNDeletion.lean) and
  [nonincreasing last-list changes](src/BTnSSBMS/BNLastChange.lean) preserve the genuine
  whole-block inequality. [Special copying](src/BTnSSBMS/BNSpecial.lean) covers the
  algorithm's actual stopping depth, arbitrary nesting and all copy counts.
  [Index-zero closure](src/BTnSSBMS/BNPruning.lean) additionally handles actual
  last-spine pruning in every successful ordinary branch at index zero.
  **All branches are now connected below: `standard_BN` proves BN on the entire source
  standard domain. This is not target BMS BN or target standardness.**
- [Numerical complete-block transport](src/BTnSSBMS/RelocationBlocks.lean) uses a
  verified numerical transport entry to prove both directions of the zero-block cutoff test, giving `relocate_rootBlock` and,
  through the frozen activation-and-shift copy, `copied_rootBlock`. These are exact
  finite syntax equalities including every nested attachment, not merely head-value
  identities or arbitrary prefix comparisons. Their use at different entries and
  at the forced root is supplied by the following results; none proves cross-copy BN alone.
- [Sibling entry](src/BTnSSBMS/SiblingEntry.lean) moves an earlier head forward
  across a context gap when its computed zero-parent stays the same. All higher
  parents, unit steps, the new numerical view and full finite legality are derived.
  [Sibling relocation](src/BTnSSBMS/SiblingRelocation.lean) proves an exact commuting
  square for the complete syntax, including arbitrary nested forests.
  [Sibling comparison](src/BTnSSBMS/SiblingComparison.lean) reflects equality of
  actual target zero-parents back to source parents and proves exact complete-block
  comparison at different entering contexts, also for the frozen numerical copy.
  [Suffix entries](src/BTnSSBMS/RelocationSuffix.lean) recover each compared pair's
  actual contexts and position map from the complete recursive transport.
  [BN transport](src/BTnSSBMS/BNRelocation.lean) consequently proves `relocate_BN`
  and `copied_BN`, recursively including every attachment, in every positive dimension.
  [Forced-root assembly](src/BTnSSBMS/BNRootCopy.lean) includes the actual new copy root;
  `initial_selected_root_copied_BN` constructs the first low-class entry from the
  selected parent, with no extra transport-state premise. This result handles the ordinary
  copy before terminal-hole replacement; the following results add the positive low-class seams.
- [Terminal splice geometry](src/BTnSSBMS/TerminalSplice.lean) classifies surviving old heads
  and new replacement heads at their actual entering contexts, retaining complete block boundaries.
  [Zero-floor geometry](src/BTnSSBMS/ZeroFloor.lean) proves that a floor-fenced replacement head
  with an external zero-parent must have the floor value and the first replacement head's parent.
  [Outer BN splicing](src/BTnSSBMS/BNSpliceZero.lean) bounds each new external sibling block
  by that first block and then by the old terminal; earlier blocks remain unchanged.
  [Arbitrary-depth BN splicing](src/BTnSSBMS/BNSplice.lean) uses only the actual hole context,
  not a replacement-validity hypothesis at every possible context.
  [Positive low-class iteration](src/BTnSSBMS/BNPositiveCopies.lean) constructs the real seam
  at every copy, proving BN for every copy count and arbitrary forest depth.
  [Whole-source assembly](src/BTnSSBMS/SourceBNPositive.lean) locates the actual root and
  terminal in the frozen FS: `ordinary_positive_expand_BN` proves BN preservation for
  the full ordinary branch whenever `0 < cap < d`. For BT3SS this includes `cap=1`.
- [Actual donation transport](src/BTnSSBMS/BNDonation.lean) extracts the terminal
  attachments in their computed hole context and proves first-list replacement when
  every later outer head is strictly above the root. [Highest-class copies](src/BTnSSBMS/BNHighCopies.lean)
  reconstruct each phase's transport: its donor is exactly the current virtual terminal's
  attachment list minus the last forest, giving a strict seam. [Whole high-class assembly](src/BTnSSBMS/SourceBNHigh.lean)
  connects the actual root selection, marks and outer splice.
- [Class-zero complete-block shape](src/BTnSSBMS/ZeroCopyShape.lean) identifies the
  entire first root block of every nonempty copy iteration with the pruned original
  template. [Zero-class splicing](src/BTnSSBMS/BNZeroSplice.lean) and
  [arbitrary copy counts](src/BTnSSBMS/BNZeroCopies.lean) use this equality to handle
  repeated equal roots, rather than applying the positive-floor lemma incorrectly.
  [The earlier prefix](src/BTnSSBMS/BNPrefixSplice.lean), [whole stopping forest](src/BTnSSBMS/BNZeroForest.lean),
  [outer spine lift](src/BTnSSBMS/BNSpineLift.lean) and [actual zero-class branch](src/BTnSSBMS/SourceBNZero.lean)
  retain all comparisons with siblings before the root and reassemble arbitrary outer depth.
- [All-branch BN closure](src/BTnSSBMS/SourceBNClosure.lean) proves `expand_BN` for
  every frozen branch and `standard_BN` for every seed-reachable term in every positive
  dimension, without bounds on copy count or forest depth. BN is not assumed in the
  definition of standardness, and the proof does not assume SB/G.
  **Source BN is complete; source SB/G, all target BN/SB, concrete coverage and the
  complete upper bound remain open.**
- [Exact copied positions](src/BTnSSBMS/ExactNumericalPosition.lean) distinguish exact
  parent correspondence from mere ancestor preservation. [Actual suffix entries](src/BTnSSBMS/ExactRelocationEntries.lean)
  construct this stronger witness for ordinary newly copied heads, not for an arbitrary
  forced copy root. [Partial heads](src/BTnSSBMS/PartialRebaseHead.lean),
  [whole materials](src/BTnSSBMS/PartialRebaseMaterial.lean) and their
  [commuting square](src/BTnSSBMS/PartialRebaseNaturality.lean) derive partial-rebase
  compatibility through arbitrary nested forests and the complete outer tail.
  [Complete-block comparison](src/BTnSSBMS/PartialRebaseBlockComparison.lean) and
  [root-material legality](src/BTnSSBMS/RelocatedRootMaterial.lean) then connect this
  to [the literal frozen copies](src/BTnSSBMS/PartialRebaseCopyComparison.lean):
  `copied_partial_block_compare` preserves the entire comparison result, without
  assuming equality of independently rebased materials. This addresses ordinary
  same-copy SB transport, not terminal rewrites, forced roots or cross-copy assembly.
- [Immediate key extension](src/BTnSSBMS/KeyEmptyExtension.lean) and
  [the owned-donation boundary](src/BTnSSBMS/DonationInternalKey.lean) show that a
  column genuinely inside a donor has key strictly below the donor's key **provided**
  its key is already at most the donor key followed by one empty forest.
  Full recursive node counts exclude both equalities; size alone is not used to
  order keys. The premise must still be obtained from the original SB comparison,
  and this local result is not a complete highest-class SB closure proof.
- [The source SB predicate](src/BTnSSBMS/SourceSB.lean) retains the complete
  remaining material of each currently visible ancestor, including open forest
  owners. `seed_SB` proves every diagonal seed satisfies every applicable SB level,
  for all dimensions and depths; this is not a reachable-domain closure theorem.
  [Historical block contexts](src/BTnSSBMS/SBBlockContext.lean) identify these stored
  materials with their actual parent-prefix entries and prove their rebases legal.
  [History extensionality](src/BTnSSBMS/SBHistory.lean) proves only the complete
  blocks matter, not the arbitrary tails after their cutoffs. It includes recursive
  forest entry and restoration. [Outer zero deletion](src/BTnSSBMS/SBDeletion.lean)
  uses unchanged surviving blocks and explicitly updated histories to prove
  `expand_outer_zero_SB` for the literal frozen branch, at every SB level.
  Positive-terminal changes, special repetition and ordinary-copy branches remain open.
- [Cross-phase parent barriers](src/BTnSSBMS/SBCrossPhase.lean) derive shared-parent
  exclusions from the actual search, not an assumed parent table. When the copy
  class equals the tested SB row, [the literal next-phase root](src/BTnSSBMS/SBCopyBarrier.lean)
  supplies the smaller-coordinate barrier against earlier ordinary path entries.
  [Exact ancestry reflection](src/BTnSSBMS/ExactAncestryReflection.lean) only requires
  exact parents above the exceptional forced root. [The seam connection](src/BTnSSBMS/SBCopyAncestry.lean)
  then reflects an actual target ancestor path into the source, removing the manually
  supplied source-path premise from this exclusion.
- [Exact nested hole traversal](src/BTnSSBMS/ExactCopyHole.lean) now constructs
  exact parents for all ordinary visible positions at the actual copied terminal
  hole, at arbitrary finite forest depth. It preserves the incoming visible-map
  prefix and explicitly exempts the forced root; no exact-at-hole premise is
  required when starting at that root.
  [The actual hole barrier](src/BTnSSBMS/SBCopyHoleBarrier.lean) therefore removes
  the earlier manually supplied exactness assumption.
- [The reset-gap lemma](src/BTnSSBMS/ExactCopyBarrierPath.lean) proves that an
  ancestor from the intervening old-copy gap must pass through the restarted
  root: exact ordinary parents can only point to represented source positions,
  and represented fixed-prefix positions precede the gap.
  [Consecutive actual copies](src/BTnSSBMS/SBConsecutiveCopies.lean) construct
  both nested hole contexts and their real restart, then apply this fact to
  derive the intervening-root path. When `0 < copyClass = testedRow < d`, an
  earlier ordinary visible position cannot be an SB partner of any represented
  visible position in the next copy, including its forced root, or of its terminal.
  The theorem returns the scoped numerical maps, not arbitrary position lists;
  it assumes none of the source-path, exact-parent, or barrier-path conclusions.
  [The arbitrary-position barrier](src/BTnSSBMS/SBCopyBarrierPosition.lean)
  also handles an endpoint equal to the new root.
  [Successive-root ancestry](src/BTnSSBMS/CopyRootChain.lean) separately proves
  that the previous root is an ancestor of the next root on every row below
  the copy class. The following results extend the same-class ordinary-partner
  exclusion; they are not full SB closure.
- [Literal hole spans](src/BTnSSBMS/CopyHoleSpan.lean) prove that source and copied
  hole traversals add exactly the same number of visible positions, even through
  nested forests. Closed sibling forests restore the entering context.
  [Numerical-view density](src/BTnSSBMS/NumericalViewDensity.lean) uses strict
  increase and the common frontier to prove that matching interval lengths force
  a continuous translation. [Actual hole density](src/BTnSSBMS/CopyHoleDensity.lean)
  supplies the real span and root point: every position in the target root-to-hole
  interval has a source preimage, with no surjectivity premise.
  [Whole consecutive intervals](src/BTnSSBMS/SBConsecutiveIntervals.lean) therefore
  replace the earlier represented-position restriction by actual integer bounds.
- [Finite copy-hole iteration](src/BTnSSBMS/CopyHoleRun.lean) observes the original
  copied-template/hole recursion. For every finite count it constructs the next
  entering scope, unchanged pre-root position map, protected initial head and
  lower-row chain from the first root to the last. This observer does not change
  expansion and is not a new standard-domain definition.
  [Later gap paths](src/BTnSSBMS/CopyRunBarrierPath.lean) and
  [separated-copy exclusion](src/BTnSSBMS/SBSeparatedCopies.lean) then exclude
  same-class SB pairs between every earlier ordinary position on that hole's
  visible interval and every position from a later root through its terminal,
  across an arbitrary finite number of intervening copies. Actual hole results,
  exact parents, interval preimages and the intervening root paths are derived.
  This still does not enumerate all entries of the final spliced material or
  prove its full SB invariant. Earlier forced-root partners, other tested rows,
  donated forests and delayed terminal-block comparisons remain open.
- [Copy-run geometry](src/BTnSSBMS/CopyRunGeometry.lean) proves exact visible-length
  growth and stability of the copy-class and higher root parents for every finite run.
  [Forced-root reset](src/BTnSSBMS/RootCopyReset.lean) and
  [complete template rebasing](src/BTnSSBMS/RootCopyMaterial.lean) handle the mixed head,
  all attachments and the entire outer tail. [Root-block truncation](src/BTnSSBMS/RootCopyBlock.lean)
  commutes with copying. Consequently,
  [`copyHoleAfter_root_rebaseBlock`](src/BTnSSBMS/CopyRunRootBlock.lean) proves that,
  across any positive finite gap of actual copied-hole iterations, rebasing the
  earlier unspliced template's complete root block gives the later template's block.
  Scopes, fixed prefixes, lower ancestry and shared higher parents are derived from
  the actual run, not additional assumed conclusions.
  [Hole-splice transport](src/BTnSSBMS/RelocationSplice.lean) also constructs the
  entering contexts and map along the actual hole path, and proves that canonical
  numerical transport commutes with arbitrary replacement, at arbitrary forest depth.
  **The final SB inequality between forced roots in spliced material is still open.**
  An unspliced template is not the historical complete block already containing later copies.
- [Rooted transport](src/BTnSSBMS/RootedRelocation.lean) and
  [rebasing after replacement](src/BTnSSBMS/RebaseSplice.lean) now commute the actual
  SB rebase with replacement at its computed hole, retaining the complete root block.
  [Forced-copy splicing](src/BTnSSBMS/RootCopySplice.lean) instantiates this identity
  across arbitrary positive finite gaps of the actual copy-hole run.
  [Inverse legality extraction](src/BTnSSBMS/SpliceExtraction.lean) obtains the
  replacement's entering legality and owner fence from the complete spliced result.
  Consequently [the actual historical-material theorem](src/BTnSSBMS/CopyRunSplicedMaterial.lean)
  applies to the frozen `copies` result itself, not an unspliced substitute:
  in positive low numerical classes, the rebased earlier block is exactly the
  later template spliced with the canonically transported entire remaining copy run.
  Replacement legality is derived, and neither depth nor copy count is bounded.
  [Copy-count monotonicity](src/BTnSSBMS/CopyCountOrder.lean) also proves that fewer
  ordinary copies at a fixed phase give a no-larger term and complete root block.
  [The mixed-head lemma](src/BTnSSBMS/CopySeamNaturality.lean) transports the next
  seam's head under an explicit high-parent exactness condition; low parents may differ.
  [Actual hole-map squares](src/BTnSSBMS/CopyHoleSquare.lean) now derive composition
  from the dense visible intervals and the entering maps. [Material and mixed-head
  naturality](src/BTnSSBMS/CopyMaterialNaturality.lean), together with
  [seam coherence](src/BTnSSBMS/CopySeamSquare.lean), preserve the required high parents
  and reset-map equation. [Whole-run naturality](src/BTnSSBMS/CopyRunNaturality.lean)
  proves the phase-shifted identity by induction on the actual `copies` count,
  including all terminal replacements. [Actual run rebasing](src/BTnSSBMS/CopyRunRebase.lean)
  constructs its entering conditions from `copyHoleAfter`: for any positive finite
  gap, rebasing a complete earlier run gives the complete root block of the same
  number of copies at the later phase. Count monotonicity then proves the SB inequality
  between these forced roots when the later run has no more copies.
  **This pair class is now proved; full source SB preservation is not.** Other
  endpoint classes, other relative cut levels, donations and whole-source assembly
  still require their own arguments.
- [Source seeds](src/BTnSSBMS/SourceSeeds.lean): all real diagonal seeds in every
  positive dimension satisfy finite legality. Their complete d+2-row encoded
  legality follows, without a seed-size bound or finite sample argument.
- [Index-zero expansion](src/BTnSSBMS/SourceZero.lean): erasing the highest-parent
  annotations and activation marks recovers the source. Actual hole replacement
  with an empty tail and zero shift equals deletion at the chosen depth.
  `expand_zero_index_finiteLegal` consequently proves preservation for **every
  defined [0] expansion in every branch**, including ordinary copies and donation.
  That earlier module alone does not exclude `none` in ordinary branches; the
  totality result above now excludes it on finite-legal positive-dimensional inputs.
- [Keys](src/BTnSSBMS/Keys.lean), [decoding](src/BTnSSBMS/Decoding.lean), and
  [key equality](src/BTnSSBMS/KeyEquality.lean): complete normalized keys use
  **signed integer differences**. At a common base, equal complete keys recover
  the same entire numerical attachment, even with different activation histories.
  This also holds for equality as returned by the actual key comparator.
- [Encoder](src/BTnSSBMS/Encoder.lean): the executable pruned context encoder
  `Encoder.fromSource`; its recursion terminates, every output column has exactly
  `d + 2` rows, and output length is at most `3 * N + F` for every finite input.
  Encoding extends rather than overwrites the existing output and its saved frames.
  These statements do **not** prove numeric legality or order preservation.
- [Environment](src/BTnSSBMS/Environment.lean): zero-key bindings remain available
  throughout actual recursive execution. `source_noFallback` proves that the
  empty-base default is never used by an encoding started from the empty context,
  for every finite raw input, not just sampled standard terms.
- [Key order](src/BTnSSBMS/KeyOrder.lean), [frame order](src/BTnSSBMS/FrameOrder.lean),
  and [exact heights](src/BTnSSBMS/FrameHeight.lean): the actual key comparator is
  asymmetric and transitive; every saved frame is strictly increasing in both key
  and height. The smaller-key filter and the cut including an equal key are prefixes.
  `source_framesDense` proves that binding `i` has height **exactly `2*i`**.
  These invariants hold throughout actual recursion on every finite input, without
  assuming source standardness or relying on finite tests.
- [Binding references](src/BTnSSBMS/FrameReferences.lean): each saved definition
  and latest-position pointer refers to a real column in the output prefix at
  the moment the frame is saved, with the correct height and tag. Definitions
  strictly precede latest representatives. This rules out dangling or forward
  references. That module alone does not identify computed parents; the later
  key-scope proof connects it to actual ancestor chains and parent searches.
- [Key-height cases](src/BTnSSBMS/KeyLevels.lean): first emitted heights are
  monotone in key order, and strictly ordered whenever either key is already
  bound. Different keys tie **exactly when both are fresh and their whole smaller
  binding prefixes agree**. This case requires recursive forest comparison,
  now supplied by the complete order proof below.
- [Numerical first difference](src/BTnSSBMS/NumericalOrder.lean): at a common
  numerical entry, the first different coordinate orders computed parents on one
  record chain. Strictly increasing representatives transfer the strict comparison.
  `encode_lt_of_numerical_heads` connects this to the **complete actual output**,
  regardless of the attachments or continuation material.
- [Complete key normalization order](src/BTnSSBMS/KeyNormalizationOrder.lean):
  activation flags agree before the first difference and cannot change from active
  to inactive at that difference. Signed subtraction preserves the within-flag
  comparison. `ofColumn_annotate_compare` proves **exact agreement** of complete
  key and source attachment comparison for arbitrary-depth finite-legal forests
  at a common owner entry. History correctness is maintained through actual
  annotation and restored on forest exit, not assumed identical at all positions.
- [Encoded head order](src/BTnSSBMS/EncoderHeadOrder.lean): a strictly smaller first
  key height decides the complete output. `encode_attachment_compare_cases` joins
  source attachment order, complete key comparison, maintained frames and actual
  output: either the output is already strictly smaller, or both keys are fresh
  with exactly the same smaller-binding environment. The same-gap case is now
  connected to the mutual proof below.
- [Forest comparison boundaries](src/BTnSSBMS/EncoderBoundary.lean): actual row-zero
  search and numerical representatives put the next unfinished internal column
  strictly above its owner's representative. A strict first-column difference
  survives arbitrary suffixes, separately from an order caused just by ending.
  [Whole-column splitting](src/BTnSSBMS/EncoderHeadState.lean) decomposes the real
  encoder at its closing column. [Exit fences](src/BTnSSBMS/EncoderOrderScope.lean)
  verify the actual following-slot and closing-column bounds without assuming
  recursive order preservation.
- [Complete strict order](src/BTnSSBMS/EncoderStrictOrder.lean): `encode_strict_order`
  proves strict order of the **complete actual encoding** for every positive
  dimension and finite-legal input pair at a common legal entry. The mutual proof
  covers fresh keys in the same gap, arbitrary nested forests, early forest/list
  endings, and equal-head outer tails. Actual delimiter bounds control different
  continuations; a bare prefix comparison is not used in their place.
- [Source-standard comparison](src/BTnSSBMS/SourceEncodingOrder.lean):
  `standard_compare` joins finite-legal closure to the full comparison proof:
  the source comparator and actual encoded-matrix comparator agree exactly on
  the entire source standard domain. `standard_injective` excludes collisions.
  **This is an order-faithful injection into raw fixed-width matrices, not yet
  an embedding into standard BMS terms or a proof of the ordinal bound.**
- [Last hole](src/BTnSSBMS/LastHole.lean): the finite-word argument and a quantitative
  version. If `F` has a fixed positive length increment and delays common-prefix
  differences accordingly, its iterates `W₀=[]`, `Wₙ₊₁=F(Wₙ)` satisfy
  `F(Y) ≥ Y → W_(length Y + 1) ≥ Y`. Strict monotonicity gives the paper's full
  equivalence. Raw word order is not assumed well-founded. **The actual BMS
  copy branches have not yet been proved to instantiate this interface.**
- [BMS short expansion](src/BTnSSBMS/BMS.lean): fixed-width parent tables, activation,
  copies, and the seed-expansion formula for every dimension and index. The
  general algorithm yields `U_r = B_(r+1)[3]` after an explicit zero-row projection;
  that formula is not built in as a special expansion rule.
- [Actual expansion descent](src/BTnSSBMS/BMSDescent.lean): `BMS.expand_lt`
  proves strict raw lexicographic descent for every defined, nonempty, fixed-width
  short expansion, by analyzing the first copy rather than assuming a descent
  model. **Raw matrix order is not well-founded. This is neither the BMS
  well-ordering theorem nor a proof that all required roots exist.**
- [Source head](src/BTnSSBMS/SourceHead.lean) and [uniform ceiling](src/BTnSSBMS/Ceiling.lean):
  the actual deletion, special, and copy branches preserve the initial zero leaf;
  finite-path induction extends this to all seed-reachable sources.
  `standard_source_below_ceiling` proves that **every such complete encoding** is
  strictly below the same `U_(d+2)` in raw matrix order. This is no longer merely
  conditional on a four-column head. **The raw bound does not imply standardness;
  order preservation is now proved independently, while BMS standardness remains
  open.** The [order module](src/BTnSSBMS/Order.lean)
  also proves the raw fixed-width chain `0^(k+1),1 < 0^k,1`; it is not a
  standard BMS expansion counterexample.
- [Coverage](src/BTnSSBMS/Coverage.lean): **given** the stated finite covering
  property and expansion well-foundedness on the standard target domain only,
  there is a finite expansion path to the target, so the target is standard.
  This is an explicit conditional lemma, not an assertion that encoded matrices
  already satisfy its premises.

- [Self-registering representatives](src/BTnSSBMS/BindingAnchors.lean) prove that
  every saved latest pointer names a column that registered its own position;
  later appends cannot change this fact. [Key-parent types](src/BTnSSBMS/KeyParentTypes.lean)
  show that every computed key-row parent in the complete encoder is either a
  definition column or such a representative, across arbitrary nesting and exits.
  [Forest-slot leaves](src/BTnSSBMS/ForestSlotLeaves.lean) trace all actual slots
  through the unchanged encoder. Each slot only saves earlier bindings, so it
  never becomes either parent type. `standard_slot_no_strict_key_descendant`
  proves slot leafhood on the entire source standard domain; tag-2 guards have
  no strict key-row descendants either. This supplies one target block-classification
  fact, **not exhaustive block classification or target BN/SB**.

- [Numerical column types](src/BTnSSBMS/NumericalKinds.lean) and the
  [actual first-output trace](src/BTnSSBMS/EncoderHeadTypes.lean) classify the entire
  encoder: a source column's first output (new D or reused P) only has tag-zero
  numerical parents; every auxiliary column has one common tag-1 or tag-2 parent
  in all numerical rows. Closing P is not confused with a first output.
  `standard_intermediate_pair_heads` proves that both endpoints of every SB pair
  with `0<j<d` are actual source entries. `standard_sibling_pair_types` excludes
  row-zero siblings mixing entries and auxiliary columns; auxiliary siblings
  share all numerical parents. These hold on the whole source standard domain.
  **Source-scope/block correspondence, rebasing and the whole-block BN/SB
  inequalities do not yet follow from these endpoint reductions.**

- [Source origins of bindings](src/BTnSSBMS/BindingSources.lean) and
  [whole-execution provenance](src/BTnSSBMS/EncoderBindingSources.lean) now track
  the visible source scope and its open forest owners separately from target
  positions. `standard_readsSources` proves that every saved latest pointer read
  during the actual encoder comes from a strictly earlier, visible non-owner on
  the highest numerical source ancestor chain. Entry adds the current owner to
  the protected list; exit restores the previous list and discards child-local
  bindings. `inherited_source_unique` proves uniqueness of the source origin.
  `standard_binding_sources` also joins provenance and the numerical view for
  the complete outer output. These are arbitrary-depth theorems, not sampled
  executions or an assumed inverse to numerical ancestry transport.
  **They do not yet identify complete rebased source/target blocks or prove BN/SB.**

- [Actual partial-rebase entry](src/BTnSSBMS/PartialRebaseEntry.lean) constructs
  the numerical transport state for an intermediate-row comparison pair: the
  endpoints share their cut-row parent, while the old root is a lower-row ancestor
  of the new position. The new head takes lower parents from the new position and
  higher parents from the old root. The literal difference vector and complete
  finite legality of the rebased material are derived, not entry assumptions.
  This geometry is distinct from an ordinary FS copy's root selection.
- [Complete-key transport](src/BTnSSBMS/CopyKeyTransport.lean) separately tracks
  the capped copy history and the full-dimensional normalization history. It proves
  that the actual recomputed key of the rebased root is exactly its original key,
  including every nested forest. It does not assert that all internal column keys
  remain unchanged. [Common-rebase comparison](src/BTnSSBMS/PartialRebaseComparison.lean)
  then preserves all three comparison outcomes for arbitrary finite-legal materials
  transported from one common entry; the real partial-rebase entry is constructed.
  This common-entry result is distinct from the cross-entry result below; neither
  by itself supplies complete encoder/block transport or target BN/SB.
- [Closed-forest transplantation](src/BTnSSBMS/ClosedForestTransplant.lean) now
  constructs an earlier highest-numerical-row ancestor's attachment at the current
  column. Actual parent searches, owner separation and every nested forest remain
  legal, and the complete relative key is exactly preserved. This reduces a
  comparison between keys from different prefixes to a literal comparison of two
  finite-legal lists at one entry; it does not assert that the transplant is standard.
- [Canonical numerical transport](src/BTnSSBMS/NumericalRelocation.lean) reconstructs
  a coordinate from its represented parent. `relocate_eq_copied` and its forest
  companion prove equality with the original activation-and-shift operations on
  finite-legal material. It is an auxiliary proof device, **not a changed FS**.
  [Composition](src/BTnSSBMS/RelocationComposition.lean),
  [exact comparison](src/BTnSSBMS/RelocationOrder.lean), and
  [finite legality](src/BTnSSBMS/RelocationLegality.lean) cover complete arbitrary-depth
  material with restored forest scopes. [Transplant naturality](src/BTnSSBMS/TransplantNaturality.lean)
  proves that transplantation and numerical transport commute as **whole syntax**,
  by deriving equality of the two composed position maps.
- [Cross-entry key transport](src/BTnSSBMS/CrossEntryKeyTransport.lean) consequently
  proves preservation of all three comparison outcomes between an ancestor key and
  a current key, each computed in its own original prefix. The
  [literal-copy connection](src/BTnSSBMS/CopyKeyComparison.lean) derives the earlier
  entry by restriction of the current copy state. `copied_ancestor_key_compare`
  covers two unchanged attachments in one copy; `copied_external_ancestor_key_compare`
  covers a fixed external ancestor, with explicit unchanged-prefix/position conditions.
  No endpoint-key equality or comparison preservation is assumed.
  These local material theorems are now connected to actual saved-binding payloads
  by the following modules; they do not by themselves prove exhaustive block transport.
- [Saved attachment material](src/BTnSSBMS/BindingMaterials.lean) distinguishes a
  binding's old definition pointer from its latest source representative. Both fresh
  and reused bindings have the exact complete key of the latest column's actual
  attachment list; reuse is justified by the encoder's real equality test.
  [Execution-wide material tracing](src/BTnSSBMS/EncoderBindingMaterials.lean)
  carries these original lists and their finite legality through every actual query.
  Sibling forests restart from the same whole owner list, and exits restore the old
  material context. `standard_readsMaterials` includes the real numerical entry and
  current legality, for every query on every standard source, without depth bounds.
- [Query transport](src/BTnSSBMS/QueryMaterialTransport.lean) recomputes keys from
  those saved materials, proves every comparison preserved, and derives commutation
  of the actual `smaller` and `equal` operations. The exact first key-row height is
  preserved as well, including fresh gaps. [Literal-copy query transport](src/BTnSSBMS/QueryCopyTransport.lean)
  proves that same-copy old keys are those of the actual copied lists, fixed-external
  keys stay unchanged, and the current query uses the frozen activation-and-shift copy.
  The following modules now preserve the key/height correspondence through actual
  execution; this is still not exhaustive matrix/block transport.
- [Real frame pairing](src/BTnSSBMS/FrameCoupling.lean),
  [material persistence](src/BTnSSBMS/MaterialStability.lean), and
  [scoped pairing](src/BTnSSBMS/ScopedFrameCoupling.lean) compare keys and heights
  in the two actual states without identifying absolute definition/latest pointers.
  Older materials persist through extension; saving a new binding changes its
  material origin to the current column. [Real queries](src/BTnSSBMS/CoupledQuery.lean)
  use the highest numerical parent actually computed after relocation. The fresh/reuse
  decision, smaller-key list and first height follow from material comparison, not
  a supplied branch-agreement premise.
  [Saving and closing](src/BTnSSBMS/CoupledSaving.lean) handle both actual `headState`
  branches, restoring the entry environment after arbitrary forests and saving the
  new latest position without leaking forest-local bindings.
- [Whole-execution control transport](src/BTnSSBMS/EncoderControlTransport.lean)
  now proves by mutual recursion that, under explicit numerical-entry, real-material
  and entry-frame-pairing conditions, the two actual encodings append **identical
  key/tag rows column by column**, for arbitrary forest depth and outer length.
  The [trace](src/BTnSSBMS/ControlTrace.lean) reads the last two rows of the actual
  matrix, so output-length increments agree as well; no idealized executor replaces
  the real output. [Final outer frames](src/BTnSSBMS/EncoderFrameTransport.lean)
  constructs the final maps, both actual numerical views, and all final visible-frame
  pairs rather than assuming the final-state relation.
  [Literal copy](src/BTnSSBMS/CopyControlTransport.lean) connects the theorem to the
  frozen activation-and-shift operation using their proved equality.
  The intermediate-row root initialization is now constructed by the concrete
  entry results below; other entry classes still need separate treatment.
- [Fixed-prefix material](src/BTnSSBMS/FixedPrefixMaterials.lean) proves that a
  longer corridor leaves every old binding's complete material key unchanged,
  without falsely treating prefix inclusion as a frontier-preserving numerical view.
  [Actual root queries](src/BTnSSBMS/PartialRebaseQuery.lean) derive the same saved
  frame and complete query key from intermediate-row parent geometry, hence the
  same fresh/reuse decision. [Fixed-prefix saving](src/BTnSSBMS/FixedPrefixCoupling.lean)
  and [actual root coupling](src/BTnSSBMS/PartialRebaseCoupling.lean) construct all
  visible frame pairs after the root, including its new latest-source origin.
  [Forests and tails](src/BTnSSBMS/FixedPrefixControl.lean) initialize each real slot
  before invoking recursive transport and restore both outer scopes on exit.
  [Actual partial-rebase execution](src/BTnSSBMS/PartialRebaseControl.lean) therefore
  proves **identical appended key/tag rows for the root, arbitrary nested forests,
  and outer tail**, for the original activation copy. Its inputs are finite legal
  material, actual parent geometry, numerical views, and historical state/visible
  prefix relations; root-query equality, branch agreement and entry-frame pairing
  are no longer additional hypotheses.
  **The inverse-ancestry result below now extracts those snapshots for every
  intermediate numerical-row pair. Ordinary complete-block transport for these
  pairs is proved below; the remaining source SB/G invariants,
  the highest two row classes and target BN/SB remain.
  This is not standard-domain coverage or the full upper bound.**
- [Actual source snapshots](src/BTnSSBMS/EncoderEntries.lean) record the source
  context, full remaining input, visible positions and real entering state;
  their positions project exactly to the existing first-output trace.
  [Soundness](src/BTnSSBMS/EntrySoundness.lean) and
  [execution inclusion](src/BTnSSBMS/EntryExecution.lean) give finite legality,
  numerical views, material origins, and actual state/result prefixes for every
  recorded call, including both endpoints of every intermediate-row SB pair.
  Chronology alone gives state prefixes, not lexical prefixes.
  [Visible origins](src/BTnSSBMS/EntryOrigins.lean) and their
  [full-execution preservation](src/BTnSSBMS/EncoderEntryOrigins.lean) separately
  recover each visible source position's real original entry. Its source, visible
  and material lists are exactly the appropriate prefixes. Open owners represented
  by slots are included, without confusing slots or closing representatives with
  first outputs. [Actual-entry rebasing](src/BTnSSBMS/EntryRebaseControl.lean)
  therefore derives complete control-row transport from actual source root geometry,
  with no additional historical-prefix or entering-legality hypotheses.
  [Actual endpoint parents](src/BTnSSBMS/EntryParentGeometry.lean) also reflect
  shared numerical parents to the source once the genuine visible origin is known.
  Visible-origin recovery and inverse ancestry are now supplied by the next item;
  full-block correspondence and BN/SB remain open.
- [Numerical fibers](src/BTnSSBMS/EntryFibers.lean) follow the actual parent paths
  from a first output to its current representative, excluding any other source
  head on the auxiliary portion. [Visible fibers](src/BTnSSBMS/VisibleEntryFibers.lean)
  and [their complete execution](src/BTnSSBMS/EncoderEntryFibers.lean) preserve this
  through arbitrary nested forest entry, exit, reuse and closing, also establishing
  tag-zero visible representatives. [Origin order](src/BTnSSBMS/EntryOriginOrder.lean)
  proves strictly ordered first positions without presupposing trace injectivity.
  [Inverse ancestry](src/BTnSSBMS/EntryAncestry.lean) contracts these auxiliary paths
  and recurses on a strictly smaller source parent. Every actual intermediate-row
  SB pair therefore supplies a genuine visible source root, source ancestor path
  and shared cut-row parent. [Actual-pair transport](src/BTnSSBMS/TargetPairControl.lean)
  connects the complete key/tag transport with no caller-supplied source geometry,
  old entry or historical prefixes; the actual control suffixes and appended
  lengths agree. [Ancestry and activation](src/BTnSSBMS/EntryActivation.lean)
  establish both directions of numerical ancestry and equality of the actual
  BMS threshold with the source query threshold at these entries.
  [First-column values](src/BTnSSBMS/EntryRebaseNumerics.lean) verify that the
  original activation copy sets the root's low numerical rows to the destination's
  encoded values and retains its high rows, without identifying source coordinates
  with encoded coordinates.
  These first-column results alone do not identify a lexical suffix with a
  complete BMS block. Internal transport and actual boundaries are proved next.
- [Row-rebase traces](src/BTnSSBMS/RowRebaseTrace.lean) and
  [visible values](src/BTnSSBMS/RowRebaseValues.lean) follow increments determined
  by the actual parent table. [Complete numerical execution](src/BTnSSBMS/EncoderRowTransport.lean)
  proves transport of every internal output column by mutual recursion, including
  guards, slots, arbitrary nested forests and closes, without assuming internal
  transport. [Fixed-prefix roots](src/BTnSSBMS/FixedPrefixRows.lean) and
  [the original copy](src/BTnSSBMS/PartialRebaseRows.lean) initialize from actual
  source geometry and connect to the frozen activation copy.
  [Matrix transport](src/BTnSSBMS/RebaseMatrixTransport.lean) combines this with
  the control rows: `standard_intermediate_pair_copy` proves that **all d+2 rows**
  of each complete local output interval equal the actual BMS phase-one copy,
  for every intermediate numerical-row pair. The interval initially ends at the
  lexical execution boundary, not at an assumed block boundary.
- [Low exits](src/BTnSSBMS/BlockCutoff.lean) and
  [entry-block closure](src/BTnSSBMS/EntryBlockClosure.lean) prove that each source
  entry's complete row-zero block stays inside its local execution. The next
  sibling slot or enclosing close prevents escape. This covers every nested
  entry of every standard source, with no assumed endpoint or BN/SB condition.
  `standard_entry_block_ends_before` also uses actual inverse ancestry: a later
  visible source column at or below the old root's zeroth value has its first
  output outside the old target block, giving a genuine outer-truncation bound.
  [Rebased boundaries](src/BTnSSBMS/RebaseBlockBoundary.lean) separately prove
  exact root-block length preservation under the actual ancestry-sensitive
  row-zero shift, excluding the first outside column after rebasing.
  [Complete-block transport](src/BTnSSBMS/CompleteBlockTransport.lean) then proves
  `standard_intermediate_pair_block`: for every actual target pair at
  `0<cut<d`, relocating the corresponding source material by the frozen rule and
  re-encoding produces an **actual complete BMS block equal to the BMS rebase of
  the original complete block**. Source roots, snapshots, cutoffs and transport
  are derived, not supplied by the caller.
  This equality alone does not establish the block inequality. The following
  results identify the complete source block and connect its comparison.
- [Complete source blocks](src/BTnSSBMS/SourceBlocks.lean) truncate only the outer
  tail and retain all attachments. [Cutoff boundaries](src/BTnSSBMS/SourceBlockCutoff.lean)
  and [block encoding](src/BTnSSBMS/SourceBlockEncoding.lean) prove that the entire
  added encoding of this truncation is exactly the actual target root block,
  including every internal forest and closing column before the cutoff.
  [Source-block transport](src/BTnSSBMS/SourceBlockTransport.lean) connects that
  endpoint to the frozen partial rebase: `standard_intermediate_source_block`
  gives the exact complete-source-block encoding for every actual ordinary-row
  target pair. [Entry comparison](src/BTnSSBMS/EntryOrder.lean) derives zero-binding
  availability, ordered frames and dense heights at every actual entry; the
  destination's comparison hypotheses are not assumed.
  [Whole-block comparison](src/BTnSSBMS/SourceBlockComparison.lean) then proves
  `standard_intermediate_block_compare`: the three-valued comparison of the
  target rebase with the destination block **equals the comparison of the
  rebased complete source block with the destination complete source block**,
  at arbitrary finite nesting depth.
  **This is not source SB preservation. One must still prove that the source
  comparison is never less, and handle the highest rows, coverage and target standardness.**
- [Descendant-block boundaries](src/BTnSSBMS/DescendantBlocks.lean) prove that a
  row-zero descendant's complete block cannot extend beyond its ancestor's block,
  and that a block wholly contained in an actual execution prefix can be computed
  there without change. [Closing blocks](src/BTnSSBMS/ClosingBlockEncoding.lean)
  apply this to restored representatives, without identifying a fresh closing P
  with the source column's first output. `standard_entry_closing_source_block`
  gives an exact formula for every actual entry of every standard source: encode
  its complete source block, then remove everything strictly before its closing
  representative. The remaining word is exactly the global closing block.
  This removes the definition and attachment output while retaining the closing
  column and its entire block tail, and includes the one-column reuse case.
  Closing-block rebase transport and inequalities require separate proofs;
  they do not follow from the boundary formula.
- [Closing-representative origins](src/BTnSSBMS/ClosingEntryOrigins.lean) prove on
  the entire finite source language that self-registered representatives are
  exactly closing positions of actual source entries. The proof covers fresh
  and reused keys, arbitrarily nested forests and enclosing exits, without
  traversing attachments skipped by reuse. Inherited slot pointers cannot
  register the slot itself. [Zero-tag classes](src/BTnSSBMS/ZeroEndpointClasses.lean)
  exhaust all zero-tag outputs into closing representatives or actual slots;
  [positive-tag origins](src/BTnSSBMS/PositiveEndpointOrigins.lean) exhaust positive
  outputs into fresh definitions or their immediately following guards, with
  actual entries and failed-lookup witnesses.
  [Highest tag-row endpoints](src/BTnSSBMS/TopRowEndpointClasses.lean) then prove
  `standard_top_pair_classes` for the entire standard source domain: a strict
  key-ancestor pair sharing a tag parent has a closing representative on the left
  and either a closing representative or a slot on the right. A positive-tag
  column has the same existing parent in both highest rows, ruling it out of
  such a pair. Neither source SB/G nor target standardness is assumed.
  **The highest tag-row endpoint classification is complete; its two block
  inequalities and the lower key-row classification remain open.**
- [Ancestor binding recovery](src/BTnSSBMS/FrameAncestorRecovery.lean) combines
  exact even binding heights with uniqueness on the actual parent chain to
  recover the earlier closing representative in the later one's saved frame.
  [Closing source ancestry](src/BTnSSBMS/ClosingAncestorSources.lean) then locates
  its genuinely visible, non-owner highest numerical source ancestor.
  [Frame persistence](src/BTnSSBMS/FramePersistence.lean) proves, for the entire
  finite encoder, that every binding's latest position stores exactly the frame
  prefix ending at that binding, including all keys and both pointers.
  [Closing frame extension](src/BTnSSBMS/ClosingFrameExtension.lean) consequently
  proves `standard_closing_frame_extension`: a strict key ancestor's whole frame
  survives literally, a nonempty binding list is appended, and the height
  difference is twice its length. [Visible closing origins](src/BTnSSBMS/VisibleClosingOrigins.lean)
  distinguish non-owner closing representatives from open-owner slots and yield
  `standard_closing_pair_origin`, with the genuine old source entry, its original
  closing position and the non-owner source path. [Complete key order](src/BTnSSBMS/ClosingKeyOrder.lean)
  proves strict increase of the entries' complete keys along that actual path.
  **This closes the highest-row P/P source correspondence and environment
  extension, not the insertion-domination inequality for transported blocks.**
- [Insertion query arithmetic](src/BTnSSBMS/FrameInsertion.lean) proves an exact
  height balance for real fresh/reused lookups, allowing an arbitrary shared
  high-key tail and unequal pointers. Inserting r keys raises the first height
  by at most 2r, strictly less unless the query is above every inserted key.
  This includes an old fresh query becoming a reuse from the inserted interval.
  [Filtering and saving](src/BTnSSBMS/InsertionSaving.lean) preserve the key splice;
  queries below the interval remove it and queries above retain it intact.
  [Actual closing queries](src/BTnSSBMS/ClosingQueryInsertion.lean) derive the
  interval from a real standard closing chain. `standard_closing_query_cases`
  proves no change below the old key, the exact actual height shift above the
  new key, and a strict upper bound for queries not above the new key.
  [Complete head operations](src/BTnSSBMS/InsertionHead.lean) connect the saved
  key-list relation to actual definitions/reuses and forest returns; a strict
  first-column decision survives arbitrary trailing material.
  **These local query results alone do not handle complete-block domination
  through external re-entry and nested forests; the full recursion and actual
  block connection appear below.**
- [Query ancestry](src/BTnSSBMS/QueryAncestry.lean) proves, for every actual
  query in the standard source domain, that a saved binding's latest position
  is a key-row ancestor of the first output exactly when its key is strictly
  smaller than the query key. Equality reuses the definition, not the old
  representative. This is connected to the frozen BMS activation threshold.
  [Reverse recovery](src/BTnSSBMS/QueryAncestorRecovery.lean) recovers any older
  closing representative on that ancestor chain from the query's retained
  smaller-key frame. Absence from the actual queried frame therefore implies
  no key-row activation, including queries through nested/external parents.
  [Rekeyed insertion](src/BTnSSBMS/RekeyInsertion.lean) derives the three height
  regimes after actual source-payload relocation, without identifying the old
  and new complete keys syntactically or postulating a context-free key map.
  [Actual activation bound](src/BTnSSBMS/InsertionActivation.lean) joins those
  calculations to the original BMS threshold: `standard_relocated_query_height_bound`
  adds the insertion increment only where the original key row is active.
  **This local bound still requires an activation-gated insertion interval;
  the outer-frame preservation below does not automatically give that stronger condition.**
- [Bounded key splices](src/BTnSSBMS/KeySplice.lean) allow recomputed complete keys
  and unequal heights. Filtering and saving create no new unmatched keys: the
  survivors form a sublist of one fixed initial pool.
  [Visible-frame splices](src/BTnSSBMS/SplicedFrames.lean) retain the actual saved
  frame at each visible parent, including external-parent re-entry.
  [Complete-head preservation](src/BTnSSBMS/SplicedSaving.lean) allows different
  fresh/reuse branches and different intervening forest lengths; the restored
  closing frames still satisfy the splice relation.
  [Outer execution](src/BTnSSBMS/EncoderSpliceTransport.lean) constructs the final
  numerical views, material provenance and splices at every visible position.
  [Closing-root rekeying](src/BTnSSBMS/ClosingRekey.lean) proves that a real
  ancestor-root transplant preserves its complete key and all older saved keys.
  [Actual entry initialization](src/BTnSSBMS/ClosingSpliceEntry.lean) derives the
  initial pairing and insertion pool from a strict closing-ancestor pair in the
  standard domain, rather than assuming them.
  [`standard_closing_tail_spliced`](src/BTnSSBMS/ClosingSpliceTransport.lean)
  joins this initialization to the complete outer tail. Every final saved frame's
  unmatched keys come from the later root's actual extra bindings.
  **These ungated splice theorems do not themselves compare skipped or replayed
  internal forest columns or justify selective height shifts.**
- [Original-root gates](src/BTnSSBMS/RootedSplice.lean) strengthen the relation:
  every unmatched key is strictly above an old binding whose latest position
  is still the original root. Retaining the inserted key under actual filtering
  forces that binding to survive, by transitivity. Saving does not update the
  retained old bindings. [Visible frames](src/BTnSSBMS/RootedFrames.lean) and
  [complete heads](src/BTnSSBMS/RootedSaving.lean) preserve this stronger invariant.
  [Actual closing initialization](src/BTnSSBMS/ClosingRootedEntry.lean) constructs
  its gate and insertion pool from a standard closing-ancestor pair.
  [Outer execution](src/BTnSSBMS/EncoderRootedTransport.lean) and
  [`standard_closing_tail_rooted`](src/BTnSSBMS/ClosingRootedTransport.lean)
  propagate it through the entire outer tail, without assuming the initial
  gate or the final saved-frame relation.
  [Activation-sensitive queries](src/BTnSSBMS/RootedQuery.lean) give **equal**
  query heights when the original BMS threshold does not activate the root;
  only an active root permits twice the initial pool length as an increment.
  Equality at that maximum shift forces all insertions to survive and both
  queries to take the same fresh/reuse branch. Branch agreement is not assumed.
  [Forest-slot entry](src/BTnSSBMS/RootedSlots.lean) preserves the gate when both
  runs enter corresponding slots, using genuinely filtered frames. Slots use the owner's entering frame,
  not the local frame left by a previous sibling, and output lengths may differ.
  It does not assert that arbitrary complete runs visit the same forests;
  branch alignment must be connected along the part before a strict difference.
  **These preservation and first-height results alone do not establish
  complete-block insertion domination.**
- [Actual auxiliary activation](src/BTnSSBMS/KeyRowRebase.lean) identifies the
  shifts of guards, forest slots and closing columns from computed BMS parent
  chains. [Query first columns](src/BTnSSBMS/RootedHeadComparison.lean) yield
  either a strict first-column difference or exact equality with matching
  fresh/reuse branches, without assuming equal output lengths or branch choices.
  [Shifted outputs](src/BTnSSBMS/ShiftedOutput.lean) equal the corresponding
  frozen `BMS.copy` segment, distinguishing the activation root from the segment's
  starting position. [Comparison composition](src/BTnSSBMS/ShiftComparison.lean)
  permits unequal lengths. [Fresh-head auxiliaries](src/BTnSSBMS/FreshShift.lean)
  derive the full-row alignment conditions for guards, slots and closing columns
  from equal first columns; this does not skip the intervening forest comparison.
  [Concrete numerical initialization](src/BTnSSBMS/ClosingRowEntry.lean) constructs
  the root gate and actual row-difference vector together from a standard closing
  ancestor pair; its key-row difference is twice the number of new bindings.
  [Complete-head decisions](src/BTnSSBMS/RootedDecision.lean) show that a strict
  first-column difference survives arbitrary continuations, and extend the query
  decision to the whole head whenever at least one side reuses a definition.
  The remaining fresh/fresh comparison is now discharged below.
- [Complete output comparison](src/BTnSSBMS/RootedComparison.lean) mutually
  recurses over forests and outer tails of arbitrary finite depth. Until a strict
  difference appears it restores numerical values, frames and actual activation;
  afterward branches and output lengths may differ. Each sibling forest uses
  its owner's entering frame, not the previous sibling's final local frame.
  [Standard closing initialization](src/BTnSSBMS/ClosingInsertionComparison.lean)
  derives every entering condition from actual strict closing-ancestor pairs,
  providing comparison for arbitrary finite legal material at the old entry.
  [Exact block slices](src/BTnSSBMS/ClosingBlockSlice.lean) connect the actual
  source-block cutoff, root column, row differences and complete `BMS.rebase`
  interval. [Whole-block insertion domination](src/BTnSSBMS/ClosingBlockComparison.lean)
  then proves `standard_closing_block_insertion` for every such pair in the
  standard source domain: the transported old block tail, encoded at the new
  closing entry and including that closing column, is no greater than the actual
  target rebase of the old complete block.
  **Its left side is transported old material, not the new entry's own block.
  Bounding the latter by the former still requires source block-order invariants;
  the theorem is not highest-row SB or target standardness.**

The last completed full-build [audit](src/BTnSSBMS/Audit.lean) covers 297 modules and 1777 public declarations:
1681 general lemmas and proof-bearing constructions, 72 closed equalities, and 24 finite reachability certificates. Private helper lemmas are
checked through their callers. See the receipt and [audit log](verification/Audit.log)
for actual axiom reports. The build rejects admitted proofs, additional axioms,
and native-evaluation proof shortcuts.
The forty-nine recent partial-rebase transport, source SB, exact-hole,
interval-density, finite-copy, forced-root block, hole-splice, spliced-material,
count-order, seam-transport, map-square and whole-copy-run modules (127 public theorems)
are included in the complete build; source hashes, dependency order and axiom reports have been
independently checked. This does not
certify the complete upper-bound theorem.

## Finite executable correspondence

[Fixtures](src/BTnSSBMS/Fixtures.lean) contain 24 inputs, in dimensions 1, 2, 3
and 5, with expected lower parents and encoded matrices from the frozen research
implementation. All 48 equalities are checked with proof-producing `decide_cbv`.
The new [source path module](src/BTnSSBMS/SourceFixtures.lean) additionally checks
the 24 path computations with the complete Lean expansion and derives their
24 reachability certificates. Thus paths are no longer only external metadata.
This is **not** a theorem of correspondence for all legal reachable terms or a
proof of all standard-domain block invariants.

[Fixture metadata](fixtures.json) records paths and the reference encoder hash.
The optional [read-only generator](tools/oracle-fixtures.cjs) accepts the old
research directory explicitly and emits JSON; the normal build needs neither
that directory nor the upstream JavaScript. Original implementations are not
redistributed in this project. Rule provenance is in the
[paper manifest](../../research/btnss-bms/MANIFEST.json).

## What remains before the main theorem can be claimed

1. For the executable source FS, prove universal correspondence with the frozen
   external implementation.
   Prove intermediate SB, the highest G condition, and cross-leaf extension.
   Seed finite legality, deletion/special branches, all defined index-zero steps,
   and actual low-branch first-head parent transport are now checked. Whole
   no-hole material, the actual first entry, later numerical seams, computed hole
   transport and arbitrary-depth splicing are also checked. Positive low-class
   iterations and zero-class same-forest iterations, installed back into their
   original root template, now include the replacement's owner fence. The
   highest-class iterations, each first-list replacement, and initial and later
   donations are checked as well. Actual numerical root and hole contexts are
   extracted; actual highest-class selection yields a nonempty root tail, rather
   than assuming non-ownership. The original `mark`/`spine`/`drop` root piece,
   visible root vector and literal delta are now identified exactly. Successful
   positive low-class and highest-class steps have whole-term `expand?` preservation,
   not just a rooted-template result. The actual highest-key ancestor's numerical
   interpretation, full marked donor history, and whole high-class splice are complete.
   Zero-class same-forest selection, outer fencing and whole assembly are now joined;
   lookup totality for all ordinary branches is also proved. `standard_finiteLegal`
   and `standard_expand_total` close finite legality and single-step totality on the
   whole source standard domain. `standard_HW` now separately proves hereditary
   nonincrease of every attachment list, using actual source descent, copying
   transport and highest-class donation. Finite legality and HW do not replace
   the remaining SB/G or cross-leaf block-order invariants.
   BN is proved for all seeds, terminal deletion, special branches and every index-zero
   branch. Common-entry reduction and exact cross-entry sibling-block comparison now
   give complete ordinary-copy BN, including arbitrary attachments and the actual
   forced root of the first low-class copy. Positive low-class terminal-hole replacement
   and every new cross-copy zero-sibling comparison are now proved: the floor fence
   forces an external-parent head to have the virtual terminal's zero-value, so its
   complete block is bounded by the replacement's first block and then by that terminal.
   The theorem covers arbitrary depth, every copy count and actual whole-source assembly,
   not just an extracted template. Highest-class donation now closes through the strict
   seam of the actual previous-phase donor. Class zero closes through the entire
   first-root-block identity, all earlier sibling comparisons and the outer spine lift,
   without being incorrectly folded into the positive-floor lemma. `standard_BN`
   proves BN on the entire source standard domain; it does not replace SB/G or coverage.
2. Complete source/target correspondence and transport for the remaining block
   classes, including the highest rows. Ordinary intermediate-row whole-block
   correspondence and exact comparison reduction are now proved.
   Zero-binding availability, unreachability of `base []`, key/height order, prefix
   truncation, the exact `2*i` height convention, concrete pointer witnesses, and
   fresh-key-gap classification are proved. Computed lower parents, full recursive
   scope restoration and numerical unit steps are proved. Saved bindings now lie
   on actual key-row ancestor chains; higher-row searches for definition, reuse
   and auxiliary cases are connected, and complete d+2-row legality follows for
   finitely legal sources, now including every standard source. Still required:
   full upper-row block classification and complete rebasing transport.
   Source ancestry/non-ownership of every queried latest representative is now
   proved throughout actual execution, with open-owner entry/exit and unique
   visible source origins. Actual partial-rebase entry, complete rebased root-key
   equality and exact comparison under a common rebase are now proved as well.
   Complete forest transplantation, its commutation with numerical relocation,
   and cross-entry comparison of the actual copied attachment keys are now proved,
   including the fixed-external-ancestor case under explicit finite prefix conditions.
   Every saved latest binding is now identified with its actual source attachment,
   including that attachment's original finite-legal entry. This holds at all real
   queries, with the numerical entry/current legality certified there as well.
   On the frame explicitly recomputed from these materials, `smaller`, `equal` and
   the exact first key-row height commute with transport, also for the literal copy.
   Under explicit entry-frame pairing, the whole actual execution now preserves
   that relation, appends identical key/tag rows and has the same output-length
   increment, including arbitrary nested forests and restored outer tails.
   Final outer maps and actual saved frames are constructed, not assumed.
   The intermediate-row partial-rebase entry is now initialized from actual root
   geometry and historical prefix snapshots. Its complete actual root/forest/tail
   key/tag transport is connected to the original copy without assuming root-query
   equality, branch agreement or initial frame pairing. Snapshots for every
   intermediate numerical-row pair are now recovered, and ordinary transport of
   every numerical and control row is connected. Attachments changed by holes or
   donation replacement and comparisons across different copies are not covered
   by the unchanged-attachment theorem.
   `partial_rebase_encode_control` now handles the actual root query and saving
   separately and starts recursive transport from the after-root view. Its two
   numerical views, finite legality and material origins are now recovered for all
   actual entry snapshots. Every visible source position has its original entry,
   including open owners. `standard_visible_partial_rebase_control` derives the
   historical prefixes and full control transport from actual source root geometry.
   `standard_intermediate_pair_source` now derives genuine source visibility,
   ancestry and the shared parent from target ancestor paths, not merely from
   chronological order. `standard_intermediate_pair_control` applies complete
   control transport to all such actual pairs. `standard_intermediate_pair_threshold`
   verifies actual numerical activation, and `standard_intermediate_pair_first_numeric`
   verifies every numerical row of the rebased first column.
   `standard_intermediate_pair_copy` now covers every internal column and row.
   `standard_entry_block_closed` keeps the complete root block within its local
   execution, and `RowRebaseTrace.block_length` proves the exact rebased boundary.
   `standard_intermediate_pair_block` is consequently an equality of complete
   actual target blocks, not an arbitrary cropping of lexical output.
   The outer source truncation and all its internal output are now connected:
   `standard_entry_source_block` identifies complete source and target blocks,
   and `standard_intermediate_source_block` connects the actual source-block
   rebase with the complete target rebase. `standard_intermediate_block_compare`
   derives equality of their comparison outcomes from actual entry environments,
   without an assumed source SB inequality or destination comparison environment.
   Next comes preservation of source SB on the whole standard domain, the other
   block classes, and concrete coverage. Ordinary intermediate-row boundaries,
   transport and exact comparison are no longer open obligations.
   The highest two rows may use a new definition's closing P, not an `entries`
   first output. `standard_entry_closing_block_closed` now keeps each such block
   within its local execution, and `standard_entry_closing_source_block` gives
   its exact whole-block formula after removing the definition and attachment
   output. `source_selfLatest_iff_closing_entry` now tracks all self-registered
   closing representatives; the origins of positive-tag columns and equality of
   their two highest parents are also proved for the actual execution.
   `standard_top_pair_classes` consequently exhausts highest tag-row endpoints
   into closing/closing or closing/slot pairs, constructing the source entries
   rather than assuming them. The lower key-row endpoint classification
   and both highest-row inequalities remain open. Insertion domination for
   strict closing ancestors is now proved, but does not yet bound the new
   entry's own block; neither a boundary formula nor endpoint classification
   supplies that comparison.
   The strict-key P/P case now has its actual non-owner source root, original
   closing entry, literal preservation of the old frame, exact number of added
   bindings and strict complete-key increase. Strict query-height comparison
   inside the inserted interval, exact heights outside it, and the saved-key
   relation after a complete head are now proved. For every actual source entry,
   query-head key-row activation is now equivalent to retaining the older
   representative in the queried smaller-key frame; an absent representative
   cannot receive the insertion shift. The local height bound also allows
   genuinely recomputed keys after relocation. The initial splice at an actual
   closing pair and its preservation through the complete outer tail are now
   proved, including restored complete heads and later external-parent queries.
   Unmatched keys stay within the initial pool. The activation-sensitive root
   gate is now preserved by filtering, saving, complete-head restoration, outer
   execution and forest-slot entry, and initialized at real closing-ancestor
   pairs. `standard_rooted_query_height` uses the original BMS threshold to prove
   equal query heights when the root is inactive; a global `2*pool.length`
   allowance is not used in that case. `equal_shift_forces_full` proves that
   equality at the maximum shift requires every initial insertion to survive
   below the query. First-height parity forces matching fresh/reuse branches.
   Numerical alignment of actual query first columns, auxiliary activation, and
   preservation of a strict first-column difference through arbitrary continuations
   are now proved. Actual closing pairs also initialize the root gate and row
   differences together. Complete-head comparison is available when at least one
   side reuses a definition. The fresh/fresh forest–outer mutual comparison is
   now complete at arbitrary finite depth, with unequal lengths allowed after
   strictness. All initial conditions come from actual standard closing pairs.
   Exact source-block cutoffs and `BMS.rebase` now yield
   `standard_closing_block_insertion`: transported old material is bounded by
   the old target block's rebase. Next comes comparison of the new entry's own
   block with that transported material and preservation of the highest source
   block-order condition. This one proved inequality is not final target SB.
   Row-zero siblings cannot mix source entries with auxiliary columns; their
   full-block correspondence still has to be established. Absence of strict key-row
   descendants of all actual slots and guards is now proved on the whole source
   standard domain. These source
   and block arguments are the next work, not re-proving pointer or target unit legality.
   Complete fixed-entry strict order is now proved, including the previously open
   same-gap forest bodies, early exit boundaries and equal-head tail induction.
   Exact comparison and injectivity on the source standard domain are connected.
   These are no longer open obligations, but do not replace target block conditions,
   rebasing transport or target standardness.
3. Prove BN/SB for encoded targets, connect last-hole contexts to actual copies,
   and establish the *concrete* finite BMS coverage lemma. The general first-diagonal
   theorem, complete-block descendant characterization, and first-copy/rebase-prefix
   identity are proved; neither the encoded-target hypotheses nor every copy seam
   follows automatically from them.
   Instantiate `Coverage.standard_of_coverage` using a verified BMS definition
   and a constructed well-foundedness theorem, not an assumed descent system.
4. Connect target normalization/standardness and construct the actual standard-domain
   order embedding and ordinal inequality. The **uniform raw ceiling on the source
   standard domain** and the general seed-expansion projection identity are proved.

These are substantial remaining mathematical formalization obligations. A
successful build of this project is not a certificate for the displayed main
inequality, nor a proof-theoretic analysis of its weakest axiomatic theory.

## Build

Only the Lean 4.33.1 distribution is needed; there are no Mathlib or external
BMS imports yet.

```sh
cd lean/BTnSSBMS
lake build
lake env python build.py --publish
```

Alternatively pass `--lean /absolute/path/to/lean` to `build.py`. The bounded
builder compiles every listed module freshly with one compiler thread, a
2048 MiB compiler limit and a 120-second timeout per module, then verifies the
complete list of requested axiom reports. These limits constrain the build,
not the mathematical definitions. The compiler is reaped on timeout.

Outputs stay in this project's ignored `.build/`; `--publish` writes its
path-free `VERIFICATION.json` and audit log. The independent Lake build uses
only this project's `.lake/`. No shared or existing project receipt is rewritten.
