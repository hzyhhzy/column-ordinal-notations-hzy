# ARD2 skyline: independent Lean project · [中文版](README.zh-CN.md)

Current ARD2 uses the simplified skyline rule. This project owns **7 modules**, with an exact proof-source closure of **57 modules**. Its explicit [ARD2-legacy](../ARD2-legacy/README.md) dependency supplies the existing finite-demand semantics; [shared](../shared/README.md) remains the common foundation. No unrelated notation's mathematical source changes.

Main entry: [ARD2SkylineFinal.lean](src/ARD2SkylineFinal.lean). Main theorem: `OrdinalFormal.ARD2Skyline.standard_with_top_strictWellOrder`. It has no remaining reflection, representation, accessibility or well-ordering assumption.

## Mathematical scope

- [Core](src/ARD2SkylineCore.lean): skyline normalization, moved-controller predecessor with seam-child borrow ceiling, source-block expansion and singleton seeds.
- [Bridge](src/ARD2SkylineBridge.lean): equal widths and actual columnwise inclusion in the legacy output on the same input; semantic representations restrict along that inclusion.
- [Structure](src/ARD2SkylineStructure.lean): validity, sortedness, full-column prefix property, nested seeds and strict column-order descent. Only source parents remain unmoved: row/root SELF may rebind.
- [Domain](src/ARD2SkylineDomain.lean): actual finite generation, external top and column comparison; no accessibility subtype in standardness.
- [Semantic descent](src/ARD2SkylineSemanticWellFounded.lean) and [standard order](src/ARD2SkylineOrderReduction.lean): discharge the general reductions.
- [Final](src/ARD2SkylineFinal.lean): instantiate the actual legacy demand relation, bounded splice and initial supply, and check small examples by kernel reduction.

The finite executable formulation chooses a maximum controller and filters strict lower priorities. On skyline columns this is exactly the final record and its deletion. Every appended column is normalized. The source cut column is moved by the next block, correctly rebinding both SELF coordinates. This is the [new small rule](../../notations/ARD2/definition.md), not a renamed old theorem.

The [full skyline isomorphism](../../proofs/paper/ard2-well-ordering.md), local-count preservation, cross-notation comparisons and derivability inside weak KP are **paper results**, not additional Lean claims. Nor is this compiler-level certification of Python/JS.

## Build and receipt

Use Lean 4.33.1 and the pinned dependencies described in the [central guide](../README.md). From this directory:

```sh
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048 --publish
python build.py --check-only
python build.py --check-receipt
```

The [published receipt](VERIFICATION.json), dated 2026-09-17, passed **57 modules / 182 axiom reports**: seven new modules freshly compiled and 50 source/fingerprint-checked legacy/shared modules reused. All reports use only subsets of `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`. Compilation is serial with one compiler thread, at most 2048 MiB per compiler and 120 seconds per module; the verifier cleans up its own timed-out process tree. Prepared pinned dependencies were used; a fresh network bootstrap or full Mathlib source build is not claimed.

`sources.json` and exact Lake globs own only these seven modules. Historical module names such as `ARD2Core` belong to **ARD2-legacy**, retaining namespace `OrdinalFormal.ARD2`; new theorems use `OrdinalFormal.ARD2Skyline`. An unrelated new notation does not invalidate this project's receipt.
