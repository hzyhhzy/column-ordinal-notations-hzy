# Archived runtime dependencies: provenance and licensing boundary · [中文](README.zh-CN.md)

These are the minimal upstream snapshots needed to replay the SRPD / ordinary TBMS research. They are not original code of this repository and are not automatically relicensed with it. See the [complete manifest](../manifest.json) for per-file hashes.

## Ordinary TBMS from NER

From [SmileLee-lyx/ne-rewritten](https://github.com/SmileLee-lyx/ne-rewritten), pinned at commit `c539d8f68c5553da2d681c1251ea443b6b735e62`:

- [TBM.ts](ne-rewritten/src/notations/BM-like/TBM.ts): ordinary TBMS native rules, using the default fundamental sequences.
- [utils.ts](ne-rewritten/src/utils.ts) and [notation_utils.ts](ne-rewritten/src/notations/notation_utils.ts): runtime dependencies.

The three CommonJS text modules in `compiled/` were compiled from the corresponding sources with TypeScript **6.0.3**, targeting ES2023. These are readable, pinned text files rather than binaries; readers do not need a TypeScript installation. The loader retains its VM timeouts without changing the fundamental-sequence algorithm.

## Other original implementations

- [hypcos/1-Y.js](hypcos/1-Y.js): from [hypcos/notation-explorer](https://github.com/hypcos/notation-explorer), commit `51ffbe3e89f5dd5c307d59bb9b70243f6d05962c`; original credits, including Naruyoko, are retained. Y-related helpers still present in the final simulator's import closure read this snapshot; it does not add another Y-comparison route.
The ordinary-e0MN runtime adapters under `output/e0mn-counting-20260917/` retain the `@test_alpha0` credit. They are not strong e0MN. This directory no longer duplicates the unused original UI script or BMS modules used only by excluded side tests.

## Licensing boundary

This packaging records provenance and attribution but **does not establish redistribution permission for third-party code**. Attribution, accessible source, and hashes are not licenses. Third-party files are not covered by a license for this repository's original files. Upstream licensing or authorization still needs confirmation before public redistribution. This operation organized the local repository only; it did not commit or push.

See the [archive guide](../README.md) for the distinction between mathematical arguments and runtime snapshots.
