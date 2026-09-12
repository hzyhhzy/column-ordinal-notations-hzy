# Sources, versions and licenses · [中文版](SOURCES.zh-CN.md)

This package is the 2026-09-13 source snapshot for [column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). Source and proof boundaries are part of the package, not claims removed for presentation.

## Notation implementations

The NER scripts are byte-identical copies of the selected working versions. No expansion, comparison, display mode, or resource guard was changed when packaging them.

| Script | SHA-256 |
| --- | --- |
| `notations/RPD/RPD-mountain.ne-rewritten.js` | `a679d2a0e081729f628cebc694379925233acab4c96bfb6d05ea8f83f1c1c24b` |
| `notations/LRD/LRD.ne-rewritten.js` | `394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1` |
| `notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js` | `fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab` |

RPD is the current column-comparison, mountain-display version, not the earlier history-ordered notation. LRD uses its fixed ordinal polynomial rows. Ω-LRD3 uses the inclusive packet through index `b` and its single-column seed tower. No other Ω-LRD implementation is included.

The Python files expose independent standard-library mathematical cores. RPD and LRD were adapted from existing simple cores; Ω-LRD3 was packaged from its rules and independently checked against the earlier finite-tuple reference in `tests/omega3_tuple_reference.py`. These implementations do not contain truncation rules or decide standard-domain membership. Bounded tests are evidence about implementation agreement, not a universal interpreter-equivalence theorem or a substitute for well-ordering proofs.

The host application is [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Its source, user data, and browser state are not copied into this package. Test registration stubs do not constitute a new full browser-integration test.

## Proof sources

The joint paper is a full bilingual presentation of the four-system weak-KP argument, not merely a translated abstract. Its source-manuscript reference is *A Short Proof of 1-Y Well-Ordering in KP with ω₁* (the user-supplied simplified manuscript). The manuscript is **not redistributed**; its identifying hash and the public background references are in the [paper bibliography](proofs/paper/well-ordering.md). Readers do not need a path on the original author's computer.

The finite Y geometry is pinned to [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d), revision `1689b21131b488ec2ba2515bd630360371a2389d`. The package preserves the inherited-ancestry Y definition and explicitly does not claim global equivalence with Naruyoko's original JavaScript. The ordinary Lean proof and the restricted-axiom paper proof have different verification scopes.

The exact Lean import closure and normalized source hashes are in [lean/sources.json](lean/sources.json); dependency pins, changes made only to release copies, and the final theorem index are in [lean/README.md](lean/README.md).

## License boundary

- No public license has yet been chosen for this project's original notation code, Python code, papers, or packaging tools. Publishing a repository does not by itself grant an open-source license.
- The 161 unchanged bundled Y modules retain upstream Apache-2.0. A copy is included at [lean/licenses/1Y-Apache-2.0.txt](lean/licenses/1Y-Apache-2.0.txt), and source notices are preserved.
- The separate [BMS repository](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d) has no `LICENSE` or `NOTICE` file in the inspected pinned tree. Its source is **not vendored**; the build fetches the pinned dependency. Do not redistribute it under an inferred license.
- Mathlib and document-rendering packages are external dependencies with their own licenses. Their installed packages, fonts, and compiled caches are not release source files.

No project-wide license has yet been selected. Public availability is not a blanket license grant: preserve the third-party notices above, and review licensing before redistributing additional source material.
