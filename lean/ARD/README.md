# ARD skyline: independent Lean project · [中文版](README.zh-CN.md)

Current ARD uses the simplified skyline rule. This project owns **7 modules**, with an exact closure of **56 modules**. Its explicit dependency on [ARD-legacy](../ARD-legacy/README.md) supplies the previously proved finite-demand semantics; [shared](../shared/README.md) remains the common foundation. No private source of another notation is changed or copied into this project.

Main entry: [ARDSkylineFinal.lean](src/ARDSkylineFinal.lean). Main theorem: `OrdinalFormal.ARDSkyline.standard_with_top_strictWellOrder`. It has no remaining reflection, representation, accessibility or well-ordering assumption.

## What was checked

- [Core](src/ARDSkylineCore.lean): finite skyline normalization, moved-controller predecessor, source-block expansion and singleton seeds.
- [Bridge](src/ARDSkylineBridge.lean): on the same input, every new output edge belongs to the corresponding legacy output column, and widths agree. Semantic representations restrict along this proved inclusion.
- [Structure](src/ARDSkylineStructure.lean): validity, sortedness, exact prefix property, seed nesting and strict column-comparison decrease.
- [Domain](src/ARDSkylineDomain.lean): standardness is finite generation, not an accessibility subtype; the external top is explicit.
- [Semantic descent](src/ARDSkylineSemanticWellFounded.lean) and [standard order](src/ARDSkylineOrderReduction.lean): discharge the general reductions.
- [Final](src/ARDSkylineFinal.lean): instantiate every semantic assumption using the actual legacy demand relation and initial supply.

The finite formulation takes a maximum controller and a strict lower-pair filter. On skyline columns these are the final record and its deletion. Every appended column is normalized; relocated skyline source columns are unchanged by this normalization. This is the same mathematical small rule documented in the [definition](../../notations/ARD/definition.md), not the old full-package expansion with a renamed final theorem.

The full legacy skyline isomorphism, `ARD(1,2) ≥ RPD ≥ 1Y`, and derivability inside the weak KP object theory are **paper results**, not additional Lean claims. Nor is this compiler-level verification of JS or Python.

## Build and receipt

Use Lean 4.33.1 and the pinned dependencies described in the [central guide](../README.md). From this directory:

```sh
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048 --publish
python build.py --check-only
python build.py --check-receipt
```

The [published receipt](VERIFICATION.json), dated 2026-09-16, records **56 modules / 178 axiom reports**: seven newly compiled modules and 49 explicitly reused, freshly revalidated legacy/shared modules. Reported axioms are subsets of `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx` or additional axiom appears.

The bounded verifier uses one compiler thread/process, at most 2048 MiB per compiler and 120 seconds per module; it cleans up its own timed-out child process tree. Normal Lake builds and network bootstrapping are separate. This run used prepared pinned dependencies, not a fresh Mathlib source build or network bootstrap.

[sources.json](sources.json) and the exact Lake globs own only the seven skyline modules. Old module names such as `ARDCore` belong to the explicit **ARD-legacy** backend and retain their historical namespace `OrdinalFormal.ARD`; new theorems are in `OrdinalFormal.ARDSkyline`. An unrelated new notation does not invalidate this project's receipt.
