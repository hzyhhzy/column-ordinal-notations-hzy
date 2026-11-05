# Lean: the conditional BMS bound for q(5) · [中文](README.zh-CN.md)

This independent Lean 4.33.1 project proves

$$
q(5)\downarrow\ \Longrightarrow\ q(5)>F_{\Lambda+\omega+1}(3),
\qquad \Lambda=\lim(\mathrm{BMS}).
$$

The final theorem uses the **original numerical BM4 rules**, with an exact, all-index conversion to parent coordinates. The proof also supplies a terminating finite FGH evaluation and proves its value unique.

## Exact theorem and conventions

[`q5_original_bms_bound`](LaverLowerBounds/OriginalBMSBound.lean) states:

```lean
theorem q5_original_bms_bound (family : BinaryFamily) (m : Nat)
    (hm : Q5At family m) :
    ∃ y, NumericBMS.OmegaSuccessorEval 3 y ∧ y < m
```

- `BinaryFamily` supplies a table on `Fin (2^n)` for each `n`, satisfying left self-distributivity and `a * 1 = a + 1` modulo the size. Period, projection and capped-action laws are derived, not additional structure fields.
- `Q5At family m` says that `m` is the first table-order parameter whose first-row period reaches at least `32`. The stronger [`threshold_original_bms_bound`](LaverLowerBounds/OriginalBMSBound.lean) only needs the period threshold at `m`, without minimality.
- Numerical BM4 is defined in [`Reference.lean`](YesMetaZFC/BMS/Reference.lean). Index `0` deletes the last column; positive index `n` appends `n` copies to the retained stem, then trims zero bottom rows.
- `F_0(x)=x+1`; a successor iterates its predecessor `x+1` times; a limit takes its `x`-th fundamental-sequence term.
- `Lambda[x]` is the `(x+1)`-row seed `(0…0)(1…1)` and `(Lambda+omega)[x]=Lambda+(x+1)`.

`OmegaSuccessorEval` is an inductively defined **actual finite evaluation relation**. The existential conclusion gives its value and termination under the finite-period hypothesis; it is not an arbitrary total function satisfying a growth assumption.

## Foundations and limits of certification

The final theorem's axiom audit is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no custom axiom, `sorry`, `native_decide`, I3 hypothesis, global BMS well-ordering hypothesis, or unproved counting/comparison interface in the final theorem. The project does not prove that I3 implies the existence of `q(5)`, or independently construct every finite Laver table; it quantifies over every `BinaryFamily` satisfying the defining equations.

This is a direct mathematical theorem in **ordinary Lean foundations**. It does **not** encode ZFC's object language and construct a syntactic ZFC derivation. The intended ZFC argument uses natural numbers, finite tables/lists and classical set constructions, but that separate metatheoretic translation is not claimed as machine checked. The imported `YesMetaZFC` namespace contains finite BM4 combinatorics here, not an internal-ZFC certificate.

The input is **3**. The ordinal level is `Lambda+omega+1`; the larger inputs and tower/IBLP conclusions in the [paper collection](../README.md) are not certified by this theorem.

## Proof map

1. [`FiniteTable`](LaverLowerBounds/FiniteTable.lean), [`FinitePeriods`](LaverLowerBounds/FinitePeriods.lean), [`Signature`](LaverLowerBounds/Signature.lean), and [`FiniteCapped`](LaverLowerBounds/FiniteCapped.lean) derive the finite algebraic laws. `LowProducts` provides kernel-checked finite `A_9` product certificates.
2. [`finite_feedback_stops`](LaverLowerBounds/FiniteFeedbackBudget.lean) constructs an actual terminating fixed-`[1]` descent of a concrete three-column parent matrix, with count below `m`. The capped endpoint is never used as an unsaturated strict-growth point.
3. Ancestor covers, row/width trade, `W`, and `Sigma` compile variable-index FGH computations into finite descent budgets. [`triple_realizes_fgh`](LaverLowerBounds/DiagonalFGH.lean) proves both actual evaluation and the exponential count estimate.
4. [`Numerical`](LaverLowerBounds/Numerical.lean) and [`UpperHierarchyEvaluation`](LaverLowerBounds/UpperHierarchyEvaluation.lean) assemble successor iteration, diagonalization and the final successor, yielding [`threshold_fgh_bound`](LaverLowerBounds/FiniteFGHBound.lean).
5. [`NumericCopyParents`](LaverLowerBounds/NumericCopyParents.lean) derives exact direct-parent formulas from Hunter's ancestor-copy lemma. [`encode_expand`](LaverLowerBounds/NumericExpansionFidelity.lean) proves `encode(A[n]) = encode(A)[n]` for **every valid numerical matrix and every index**, including zero-row trimming. [`NumericSeedsAndKinds`](LaverLowerBounds/NumericSeedsAndKinds.lean) and [`NumericFGH`](LaverLowerBounds/NumericFGH.lean) transfer seeds, successor/limit classification and finite FGH evaluation in both directions.

Two auxiliary counting functions have explicit defaults outside their terminating domains. Every finite-table application supplies an actual stopping witness, and every base FGH call in the final evaluation is realized. The final theorem therefore uses no fictitious default evaluation.

## Rebuild

Install the toolchain pinned in `lean-toolchain`, then run from this directory:

```sh
python -B build.py --record
```

Alternatively, pass `--lean-bin /path/to/lean/bin`. On Windows, `build.ps1` wraps the same command and accepts `-LeanBin`, `-Python` and `-Record`. Standard `lake build` is also configured; the resource-bounded audit command above is the recorded verification method.

The builder uses only Python's standard library and Lean/Std. It recompiles the complete local import closure sequentially, with **one compiler thread, 2048 MB and 60 seconds per module**. On timeout it terminates its own process tree. It checks the pinned Lean version, source stability, placeholder output, and final theorem axiom reports. No large hierarchy value or large Laver table is calculated.

The published [verification receipt](verification/VERIFICATION.json) pins every compiled module by SHA-256 after LF normalization; the [complete build log](verification/build.txt) records the fresh **152-module** build. `.build/` and `.lake/` contain local caches and are excluded from Git. `generate_low_data.py` is an optional finite proof-source generator; generated equalities still require kernel checking.

## Provenance

The mathematical Lean files are unchanged from the completed research snapshot, apart from line-ending normalization. [PROVENANCE.json](PROVENANCE.json) records source and package hashes. The eight numerical BM4 dependency modules and their upstream authorship are documented in [VENDORED.md](YesMetaZFC/VENDORED.md). Their abstract well-ordering/set-theoretic interfaces are not imported.
