# External notation expanders · [中文版](README.zh-CN.md)

**e0MN and strong e0MN were invented by @test_alpha0, not by this repository's author or its AI-assisted notation-design work.** They are collected here for convenience when reading the [comparison catalogue](../research/order-comparisons/README.md).

| Notation | Standalone NER script | Pinned edition |
| --- | --- | --- |
| Ordinary e0MN | [Fast-counting JS](e0MN/e0MN-fast-counting.ne-rewritten.js) | 2026-09-17 optimized counting edition, based on the supplied `e0MN(美化版).js` |
| strong e0MN | [Fast-counting JS](strong-e0MN/strong-e0MN-fast-counting.ne-rewritten.js) | 2026-09-19 edition based on `strong_e0MN (1).js`, including transport of implicit coefficient 1 |

Both files retain `Made by test_alpha0`. The local additions are exact count displays and acceleration; this collection does not take credit for the underlying notation. The strong edition is **not** the older `strong_e0MN.js` variant. Ordinary and strong expansion rules are not interchangeable, and default `FS` is not silently identified with `FS_short`.

Import either complete file into NE Rewritten's custom-notation facility. They have distinct registration IDs and retain original notation, row-height-difference and mountain views, with a count-sequence display. Counts use BigInt; addresses and CNF coefficients retain the original safe-integer Number semantics. Resource exhaustion means the implementation did not finish, not that the mathematical countdown is infinite.

As requested, this directory contains no new textual mathematical definition or Python port. It does not assert global well-ordering. Attribution is not a license grant: no redistribution license for the supplied originals was established during this import. Preserve their credit and confirm permission before public redistribution; see [source notes](../SOURCES.md). No commit or push is part of this packaging step.
