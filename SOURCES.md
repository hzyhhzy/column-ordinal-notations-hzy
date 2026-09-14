# Sources, versions and licenses · [中文版](SOURCES.zh-CN.md)

This package is the 2026-09-14 source snapshot for [column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). Source and proof boundaries are part of the package, not claims removed for presentation.

## Notation implementations

LRD and Ω-LRD3 remain byte-identical to their selected working versions. RPD and ARD now add text and triangular-table adjacency displays and updated registration metadata. Each embeds its entire previously published script from commit `542d47a` unchanged (verified after line-ending normalization); expansion, comparison, existing displays and original resource guards are preserved. The new views have their own complete-output guards. The hashes below pin the delivered bytes.

| Script | SHA-256 |
| --- | --- |
| `notations/RPD/RPD-mountain.ne-rewritten.js` | `447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026` |
| `notations/LRD/LRD.ne-rewritten.js` | `394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1` |
| `notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js` | `fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab` |
| `notations/ARD/ARD-arcs.ne-rewritten.js` | `ab4f05ef1fb65b6308e710cbbc98c173310f9c3073ce3a57082863af708841d6` |
| `notations/IPD/IPD.ne-rewritten.js` | `acc1a1c2ae260da9be7d13e14ac17d84a92679f82efe97aa85cd0e3b072f6011` |
| `notations/ARD2/ARD2.ne-rewritten.js` | `34d9239cee3871fb2908452022b9831c9d687f19c910745725f36231f8016907` |

RPD is the current column-comparison version with mountain and adjacency displays, not the earlier history-ordered notation. Its browser menu name is `RDP`; the notation and file names remain RPD. LRD uses its fixed ordinal polynomial rows. Ω-LRD3 uses the inclusive packet through index `b` and its single-column seed tower. No other Ω-LRD implementation is included.

ARD means *Anchored Row Diagrams*. It uses earlier-column addresses as row anchors and moves all four edge coordinates. The selected standalone browser script is the arc-view version, including circled/capsule root labels; its mathematical rules and resource guards were not changed for this addition. Its Python module retains the readable `AnchoredRows` class and maximum-root compression. The earlier mountain-only ARD renderer is not included as a duplicate implementation.

IPD means *Iterated Profile Diagrams*. Its zero-start JS and readable Python are byte-identical to the proved reference versions. `notations/IPD/ipd.py` has SHA-256 `12d3f08fd38fc51aa78b9972bae2d5e02fc8efc09de085a9b1752880948ebab1`. It relocates ROOT/SELF references inside all nested heads, retains list/count/complete-tree displays, and uses identical `FS`, `FS_alter` and `FS_short` rules. Frozen historical comments are superseded by the current paper. No experimental TPD or wY comparison draft is included.

ARD2 is the full-context variant of Anchored Row Diagrams. The new readable `ARD2` Python class and NER script use both row and root SELF coordinates and generate roots through the seam itself. They retain exact list/count/arc/text-adjacency/table-adjacency displays; the local counter is specific to the two-SELF rule, not the old ARD shortcut. Neither older notation sources nor their rules were changed.

The Python files expose independent standard-library mathematical cores. RPD and LRD were adapted from existing simple cores; Ω-LRD3 was packaged from its rules and independently checked against the earlier finite-tuple reference in `tests/omega3_tuple_reference.py`. These implementations do not contain truncation rules or decide standard-domain membership. Bounded tests are evidence about implementation agreement, not a universal interpreter-equivalence theorem or a substitute for well-ordering proofs.

The host application is [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Its source, user data, and browser state are not copied into this package. Test registration stubs do not constitute a new full browser-integration test.

## Proof sources

The joint paper is a full bilingual presentation of the four-system weak-KP argument, not merely a translated abstract. Its source-manuscript reference is *A Short Proof of 1-Y Well-Ordering in KP with ω₁* (the user-supplied simplified manuscript). The manuscript is **not redistributed**; its identifying hash and the public background references are in the [paper bibliography](proofs/paper/well-ordering.md). Readers do not need a path on the original author's computer.

The separate [ARD paper](proofs/paper/ard-well-ordering.md) extends the finite-demand method to dynamic row references. It includes the guarded relation, closed-height supply, four-coordinate splice, standard-domain argument and weak-theory axiom accounting. Both language versions are full papers. The ordinary Lean implementation constructs the required relation and initial supply rather than taking them as assumptions. The finite-union specification and compressed/full-root comparison bridges are explicit additional theorems, not claims inferred from interpreter tests.

The [IPD paper](proofs/paper/ipd-well-ordering.md) includes the complete direct KP tree-rank argument, bounded recursion, both elementary-height and explicit Bad/Ext witness-closure routes, the actual whole-graph splice and transfer of a set rank out of L. The [correspondence audit](proofs/paper/ipd-fidelity.md) distinguishes the ordinary-Lean mathematical algorithm from the paper source-language and exact JS-pruning proofs. The 40 IPD modules use their existing `IPD...` import names; source normalization is recorded in the manifest. Existing proof modules remain unchanged.

The [ARD2 paper](proofs/paper/ard2-well-ordering.md) gives the bounded pair-priority recursion, four top predicates, pointed-pair endpoint agreement, strong supply, the actual two-SELF splice, and an absolute set rank. Its 21 new Lean modules construct the real relation and witness closure; the joint seven-system audit additionally imports the compressed/full-root bridge. Ordinary Lean is not an object-language KP proof or a proof that ARD2 is larger than ARD or IPD.

The finite Y geometry is pinned to [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d), revision `1689b21131b488ec2ba2515bd630360371a2389d`. The package preserves the inherited-ancestry Y definition and explicitly does not claim global equivalence with Naruyoko's original JavaScript. The ordinary Lean proof and the restricted-axiom paper proof have different verification scopes.

The exact Lean import closure and normalized source hashes are in [lean/sources.json](lean/sources.json); dependency pins, changes made only to release copies, and the final theorem index are in [lean/README.md](lean/README.md).

## License boundary

- No public license has yet been chosen for this project's original notation code, Python code, papers, or packaging tools. Publishing a repository does not by itself grant an open-source license.
- The 161 unchanged bundled Y modules retain upstream Apache-2.0. A copy is included at [lean/licenses/1Y-Apache-2.0.txt](lean/licenses/1Y-Apache-2.0.txt), and source notices are preserved.
- The separate [BMS repository](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d) has no `LICENSE` or `NOTICE` file in the inspected pinned tree. Its source is **not vendored**; the build fetches the pinned dependency. Do not redistribute it under an inferred license.
- Mathlib and document-rendering packages are external dependencies with their own licenses. Their installed packages, fonts, and compiled caches are not release source files.

No project-wide license has yet been selected. Public availability is not a blanket license grant: preserve the third-party notices above, and review licensing before redistributing additional source material.
