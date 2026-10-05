# Evidence, historical viewers, and verification boundaries · [中文](EVIDENCE.zh-CN.md)

[Overview](README.md). Archival validation does not resume the paused mathematical research.

The [curation receipt](ARCHIVE-VALIDATION.json) records successful identity/inventory checks for 300 imported items and syntax checks for 3 viewers. Including entry pages, 304 Markdown files and 2,945 relative file links passed. The unchanged 73-item baseline passed integrity verification; all 6 smoke cases reproduced historical semantics and all children exited. This is not mathematical certification.

## Two archive layers

The original `../archive/` keeps its exact 73-item inventory, including 25 manuscripts and the runtime dependencies for its replay commands. Its contents, hashes, and historical receipts are unchanged.

Here, `papers/` retains later positive manuscripts and supporting proof excerpts. The [catalogue](CATALOGUE.md) lists them individually; manuscript count is not theorem count. Selected experimental/history sections are omitted, with original headings, line ranges, and before/after SHA-256 values in [the manifest](manifest.json). Mathematical scope, conditional premises, and open directions remain. Unpackaged scripts and side references are explicitly labeled source records.

This is **not a runnable mirror of the entire historical experiment workspace**. Commands inside long manuscripts may require unpackaged research scripts. The three standalone viewers and the earlier portable archive are the explicit exceptions.

## Fixed copies of delivered viewers

Import these through “自定义记号” (custom notation) in [NER](https://smilelee-lyx.github.io/ne-rewritten/). They do not replace the repository's current notation implementations.

| File | Actual behavior | Scope |
|---|---|---|
| [Y → M13](explorers/Y-to-M13-order-embedding.ne-rewritten.js) | Expands Y and displays a canonical M image, with a strict-order paper argument on its stated domain | Top `Y(1,3,4,2,5,7,12,3)`, not the latest S9 |
| [M13 ≥ Y lower-bound viewer](explorers/M13-with-Y-lower-bound.ne-rewritten.js) | Expands M and displays the greatest available established Y label | May repeat or skip labels; not an inverse embedding or equality calculator |
| [TBMS ≤ SRPD](explorers/TBMS-le-SRPD.ne-rewritten.js) | Expands default TBMS below `B_(ε₀)` with a persistent SRPD simulation | Not all TBMS; history-dependent, not globally order-preserving between arbitrary displayed images |

The TBMS viewer also has a reseeded view. It independently chooses a cover for the current source expression and may be smaller, but need not descend persistently along the click history. Symmetric initial carriers are not an equality table. The [original TBMS guide](papers/output/srpd-tbms-explorer-20260927/README.zh-CN.md) and [Y→M guide](papers/output/y-m13-order-embedding-20260920/README.zh-CN.md) are preserved.

Existing guards and over-limit behavior are unchanged. Counts are displays, not proofs. No all-cone NER compiler for the latest S9 paper argument is available. This collection checks JS syntax and identity, not a new browser UI run or an unbounded path.

## What finite records establish

The JSON files below are historical receipts, not mathematical certificates rerun during curation. `complete: true` means the finite check completed; finite depth limits, stopped trajectories, and unprocessed queues still apply.

| Receipt | Finite check | Not a substitute for |
|---|---|---|
| [Recursive crowns](evidence/output/tbms-srpd-equalities-20260929/RECURSIVE-VERIFICATION.json) | Multiple-Q lower interface, recursive interpreter, directed transports, persistent row profiles | The all-k, all-descendant forest induction |
| [Finite roof](evidence/output/tbms-srpd-equalities-20260929/FINITE-ROOF-VERIFICATION.json) | D44 formulas, bank capacities, selected continuing paths; includes a bounded probe with unprocessed queue entries | Full-L simulation, much less a reverse upper bound |
| [Maximal-row preparation](evidence/output/srpd-limit-y-lower-20261001/MAXIMAL-HEIGHT-ARCHIVES-DIAGNOSTIC-1.json) | 6,786 selected capacity pairs unchanged; retained old control reused | Perpetual control availability |
| [External amplification](evidence/output/srpd-limit-y-lower-20261001/EXTERNAL-DAMAGED-RESERVE-DIAGNOSTIC-1.json) | A successful amplification of a spent interior reserve from an earlier point | Timely amplification on every history |
| [External registry](evidence/output/srpd-limit-y-lower-20261001/EXTERNAL-CONTROL-REGISTRY-DIAGNOSTIC-1.json) | Successive controls 11, 10, 5; 74 control snapshots | An all-path supply invariant |
| [Buffered plans](evidence/output/srpd-limit-y-lower-20261001/BUFFERED-PREPARATION-PLANS-DIAGNOSTIC-1.json) | Two/three preparations followed by exactly one intended source step; maximum target width 5,327 | B's complete descendant cone |
| [Independent small-target tables](evidence/output/srpd-limit-y-lower-20261001/BUFFERED-PUMPS-INDEPENDENT-VERIFICATION-1.json) | 12 cases, 90 FS operations, 594 same-width downs, 570 normalization macros; maximum width 267 | A numerical-Y all-path test; not every macro was brute-force replayed |

The highest complete S9 bound remains a conditional paper result. Neither these receipts nor a file-identity audit certify its foundational chain. Omission of failed logs does not imply all historical experiments succeeded.

## Verification from the repository root

For this collection:

```powershell
node --max-old-space-size=256 research/srpd-tbms/continuation/verify.cjs
```

The read-only checker verifies the exact imported inventory, LF-normalized hashes, JSON parsing, syntax of the three viewers, and relative file links in this directory's Markdown. It performs no expansions, network requests, writes, or background work. It does **not** verify mathematics or the semantics of heading anchors.

Add `--entry-points` to check the seven updated repository entry pages as well.

For the unchanged baseline:

```powershell
python -B research/srpd-tbms/archive/verify_archive.py
python -B research/srpd-tbms/archive/run_checks.py --suite smoke
```

That existing runner executes children sequentially, with a 30-second outer limit and 512 MiB Node heap, retaining the simulators' width, step, and RSS guards. It kills and reaps timed-out children. These are replay capabilities, not scheduled research. The longer `current` suite and its two known width-guard cases are documented in the [baseline guide](../archive/README.md).
