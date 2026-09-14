# LRD: independent Lean project · [中文版](README.zh-CN.md)

This project owns **10 Lean source modules**. Its exact proof-source closure contains **41 modules**, including only the shared modules it actually imports. It does not depend on another notation's private project.

Main entry: [FiniteDemandLRDFinal.lean](src/FiniteDemandLRDFinal.lean). Main theorem: `OrdinalFormal.LRDFinal.standard_isWellOrder`. The full theorem scope and the distinction between ordinary Lean and the paper's weak set theory are explained in the [central guide](../README.md).

## Build this notation only

From this directory, with Lean 4.33.1 with its bundled Lake and Python 3.10+:

```sh
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048
```

The normal Lake build and the additional bounded verifier are separate checks. For a prepared offline dependency environment, see the central guide. To inspect sources without compiling or downloading:

```sh
python build.py --check-only
```

For subsequent verification, `lake env python build.py --resume` reuses only artifacts whose source, dependency and verification fingerprints still match. Bounded-verifier outputs belong to this project's own `.build/` (normal Lake outputs use `.lake/build/`); a new sibling notation does not change this project's source manifest or require its recompilation. This project does not fetch or compile BMS.

## Maintenance boundary

- Keep private proof sources in `src/`, and declare only those modules in this project's `lakefile.lean`.
- [sources.json](sources.json) records this project's exact transitive source closure, including the needed files in [shared](../shared/README.md).
- Do not edit another notation's sources, lockfile or receipt to add a new notation. The optional aggregate project and repository index are separate.
- If an actually used shared lemma changes, recheck its consumers. Shared source is maintained in one place; it is not an excuse to copy private dependencies between projects.

Module names and all mathematical source bytes were preserved when the original combined project was split.

## Verified snapshot

The [independent-project receipt](VERIFICATION.json), dated 2026-09-14, records **41 modules and 110 axiom reports** passing: 10 modules compiled from source in this run, 31 reused from the newly verified shared foundation. Reported axioms are only ordinary Lean's `propext`, `Classical.choice`, `Quot.sound`, or subsets; this is not a weak-KP object-theory formalization.
