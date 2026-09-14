# Shared Lean foundation · [中文版](README.zh-CN.md)

This project owns **35 modules** used by two or more notation projects, together with their shared dependencies. It depends on the pinned Mathlib environment, not on any notation's private project or BMS. Source is stored once in `src/`.

Some module names retain historical RPD, LRD or ARD prefixes. Their reusable definitions and lemmas were already imported by several notations; the split deliberately preserves complete source files, module names and proof terms. These names do not create a dependency on the RPD/LRD/ARD leaf projects.

Each leaf's `sources.json` includes only the shared modules in its own actual import closure. A new leaf can use this package without changing any existing leaf's configuration.

From this directory:

```sh
python build.py --check-only
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048
```

Bounded-verifier outputs stay in this project's `.build/`; normal Lake outputs use `.lake/build/`. The [central guide](../README.md) explains offline verification, caching, proof scope and how to add a notation. Actual modifications to a shared dependency require rechecking its consumers; adding unrelated private code does not.

## Verified snapshot

The [independent-project receipt](VERIFICATION.json), dated 2026-09-14, records **35 modules and 93 axiom reports** passing: 35 modules compiled from source in this run, 0 reused from the newly verified shared foundation. Reported axioms are only ordinary Lean's `propext`, `Classical.choice`, `Quot.sound`, or subsets; this is not a weak-KP object-theory formalization.
