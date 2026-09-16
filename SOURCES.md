# Sources, versions and licenses · [中文版](SOURCES.zh-CN.md)

## CWY-family addition (2026-09-17)

The three NER files are byte-identical copies of the selected local releases:

| Script | SHA-256 |
| --- | --- |
| `notations/CWY/wY-CWY.ne-rewritten.js` | `c2c1c3c9f83d7b69588e95b53503e6d42c86c092aac170c2db6ffce2d5ca61f5` |
| `notations/CWY2/CWY2.ne-rewritten.js` | `02b4f334f4c84d5c088a740d0f0a33fee1e1821105bb1dc8baf9228ca0a1a3ee` |
| `notations/Omega-CWY/Omega-CWY.ne-rewritten.js` | `4750912d8fb926c05f49476ba5408bb7a51e444849509411bf4e377423429414` |

CWY's file retains original wY expansion and adds the root-stretched CWY view; it is not an implementation of the shifted-seed, finite-bound CWY rule. The two included standard-library Python modules implement that mathematical version. CWY2's direct core and optional geometry views are distinct: expansion does not reconstruct a mountain. Its frozen “equivalence pending” comments predate the included [equivalence manuscript](proofs/paper/cwy2-equivalence.md). Ω-CWY retains the approved D[b+1] rule, three views, partial exact count prefixes and complete diagrams; its readable modules and local-only builder reproduce the bundle exactly. It has no whole-domain well-ordering theorem.

CWY and CWY2 contain source adapted from [ne-rewritten](https://github.com/smilelee-lyx/ne-rewritten/tree/c539d8f68c5553da2d681c1251ea443b6b735e62), local base revision `c539d8f68c5553da2d681c1251ea443b6b735e62`, particularly `src/notations/Y/Omega_Y.ts`, `src/notations/draw_mountain_util.ts`, and utilities. The working source had local adapter changes; the bundle hashes, not a claim of an untouched upstream checkout, pin these artifacts. Original wY credit remains Yukito/Naruyoko as recorded by NER. The old build-path comments identify historical provenance, not public build instructions. No full host application, user data, browser state, dependencies or private research checkout is included.

**Redistribution caution:** the inspected upstream tree has no LICENSE, COPYING or NOTICE file, and its package manifest declares no license. Retaining attribution is not a license grant. These requested local artifacts include upstream-derived code; verify permission or an applicable license before public redistribution. This integration does not select a license or push anything.

The CWY definition packages the existing highest-profile, root-stretch and internal-bound paper arguments. The CWY2 paper packages the existing termwise equivalence proof and its explicit finite-lemma dependencies on the user-supplied *Well-foundedness of the Weak-Magma omega-Y System in KP with an Uncountable Ordinal* (`omega-Y-Weak-Magma-KP.pdf`). That private manuscript is not redistributed, newly independently audited in full, or relabeled as a Lean certificate. Ω-CWY includes only its existing rule and local-fragment arguments. None adds to the seven Lean-certified systems.

2026-09-16 update: default ARD is the skyline simplification; the old kernel remains in ARD-legacy. The new Python and seven private Lean modules are newly authored; its well-ordering closure has 56 modules. Earlier unchanged-core ARD notes below refer to ARD-legacy. Current rules and proof scope are in [ARD](notations/ARD/definition.md).


This package is the 2026-09-14 source snapshot for [column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). Source and proof boundaries are part of the package, not claims removed for presentation.

## Notation implementations

LRD and Ω-LRD3 remain byte-identical to their selected working versions. RPD and ARD now add text and triangular-table adjacency displays and updated registration metadata. Each embeds its entire previously published script from commit `542d47a` unchanged (verified after line-ending normalization); expansion, comparison, existing displays and original resource guards are preserved. The new views have their own complete-output guards. The hashes below pin the delivered bytes.

| Script | SHA-256 |
| --- | --- |
| `notations/RPD/RPD-mountain.ne-rewritten.js` | `447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026` |
| `notations/LRD/LRD.ne-rewritten.js` | `394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1` |
| `notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js` | `fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab` |
| `notations/ARD-legacy/ARD-arcs.ne-rewritten.js` | `1b80215f80c7797c1891e0c197c4ca8470cd43e9ed86d68cfb7b2b760e8d7930` |
| `notations/ARD/ARD.ne-rewritten.js` | `7cf745079c90e0f127b06c50c8082f81c16600aa9a76fb712f50cfa8d2b955b0` |
| `notations/IPD/IPD.ne-rewritten.js` | `acc1a1c2ae260da9be7d13e14ac17d84a92679f82efe97aa85cd0e3b072f6011` |
| `notations/ARD2/ARD2.ne-rewritten.js` | `e0d4eb14056ee54a6d4a8d2475241469ba33f07d38c406cfa9b20c648407380d` |
| `notations/SPD/SPD.ne-rewritten.js` | `d693c23564a766ecbbe3072cd200632c49b490d47d18428e1310ea438e85f266` |

RPD is the current column-comparison version with mountain and adjacency displays, not the earlier history-ordered notation. Its browser menu name is `RDP`; the notation and file names remain RPD. LRD uses its fixed ordinal polynomial rows. Ω-LRD3 uses the inclusive packet through index `b` and its single-column seed tower. No other Ω-LRD implementation is included.

ARD means *Anchored Row Diagrams*. It uses earlier-column addresses as row anchors and moves all four edge coordinates. The selected standalone browser script is the arc-view version, including circled/capsule root labels; its mathematical rules and resource guards were not changed for this addition. Its Python module retains the readable `AnchoredRows` class and maximum-root compression. The earlier mountain-only ARD renderer is not included as a duplicate implementation.

IPD means *Iterated Profile Diagrams*. Its zero-start JS and readable Python are byte-identical to the proved reference versions. `notations/IPD/ipd.py` has SHA-256 `12d3f08fd38fc51aa78b9972bae2d5e02fc8efc09de085a9b1752880948ebab1`. It relocates ROOT/SELF references inside all nested heads, retains list/count/complete-tree displays, and uses identical `FS`, `FS_alter` and `FS_short` rules. Frozen historical comments are superseded by the current paper. No experimental TPD or wY comparison draft is included.

ARD2 is the full-context variant of Anchored Row Diagrams. The new readable `ARD2` Python class and NER script use both row and root SELF coordinates and generate roots through the seam itself. They retain exact list/count/arc/text-adjacency/table-adjacency displays; the local counter is specific to the two-SELF rule, not the old ARD shortcut. Neither older notation sources nor their rules were changed. During the Lean subproject reorganization, two explanatory source paths in the NER script and one docstring path in Python were updated; the mathematical and rendering algorithms were not changed. ARD2's implementation files are therefore not byte-identical to commit `e2bdd08`. The Python file now has SHA-256 `05a9b14d9897db8e64e2c907eb3d3e326e6768600e1c7fcb27cd336990fb2e68`; the other five notation implementations and the twenty earlier PDFs remain byte-identical to that commit.

SPD means *Slot Profile Diagrams*. The fixed 2026-09-14 version uses four-integer relations, highest visible head fibers, LATENT low packages, a strictly guarded connector, typed carry only after the first block, and complete pure-source copies. The shared recursive heads are derived from actual earlier columns, not supplied as additional tree fields. Neither the experimental refresh/splice variants nor the non-strict connector variant is included. The standalone JS changes only its introductory documentation link relative to the fixed research version; its rules, two displays and resource guards are unchanged.

The SPD Python core and separate standard-count decoder are byte-identical to that fixed version. Their SHA-256 values are `c3f72538aa71f8b4f43cf593d00731bfff38cafa3705462d1736de203591b826` (`spd.py`) and `34e8a7a26a225c3d2dbd837baad3805fd02436b071faa356852524e5d0fdf075` (`spd_count_decode.py`). The decoder can decide standard membership when its budget suffices; it never treats a timeout as a negative answer. The published tests use a self-contained tuple oracle, not imports from a private research directory. All six earlier notation implementations and all seven Lean projects are unchanged by this addition.

The Python files expose independent standard-library mathematical cores. RPD and LRD were adapted from existing simple cores; Ω-LRD3 was packaged from its rules and independently checked against the earlier finite-tuple reference in `tests/omega3_tuple_reference.py`. Those three implementations do not contain truncation rules or decide standard-domain membership. Bounded tests are evidence about implementation agreement, not a universal interpreter-equivalence theorem or a substitute for well-ordering proofs.

The host application is [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Apart from the specifically disclosed CWY/CWY2 derived snippets above, its application source, user data, and browser state are not copied into this package. Test registration stubs do not constitute a new full browser-integration test.

## Proof sources

The joint paper is a full bilingual presentation of the four-system weak-KP argument, not merely a translated abstract. Its source-manuscript reference is *A Short Proof of 1-Y Well-Ordering in KP with ω₁* (the user-supplied simplified manuscript). The manuscript is **not redistributed**; its identifying hash and the public background references are in the [paper bibliography](proofs/paper/well-ordering.md). Readers do not need a path on the original author's computer.

The separate [ARD paper](proofs/paper/ard-well-ordering.md) extends the finite-demand method to dynamic row references. It includes the guarded relation, closed-height supply, four-coordinate splice, standard-domain argument and weak-theory axiom accounting. Both language versions are full papers. The ordinary Lean implementation constructs the required relation and initial supply rather than taking them as assumptions. The finite-union specification and compressed/full-root comparison bridges are explicit additional theorems, not claims inferred from interpreter tests.

The [IPD paper](proofs/paper/ipd-well-ordering.md) includes the complete direct KP tree-rank argument, bounded recursion, both elementary-height and explicit Bad/Ext witness-closure routes, the actual whole-graph splice and transfer of a set rank out of L. The [correspondence audit](proofs/paper/ipd-fidelity.md) distinguishes the ordinary-Lean mathematical algorithm from the paper source-language and exact JS-pruning proofs. The 40 IPD modules use their existing `IPD...` import names; source normalization is recorded in the manifest. Existing proof modules remain unchanged.

The [ARD2 paper](proofs/paper/ard2-well-ordering.md) gives the bounded pair-priority recursion, four top predicates, pointed-pair endpoint agreement, strong supply, the actual two-SELF splice, and an absolute set rank. Its 21 new Lean modules construct the real relation and witness closure; the joint seven-system audit additionally imports the compressed/full-root bridge. Ordinary Lean is not an object-language KP proof or a proof that ARD2 is larger than ARD or IPD.

The finite Y geometry is pinned to [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d), revision `1689b21131b488ec2ba2515bd630360371a2389d`. The package preserves the inherited-ancestry Y definition and explicitly does not claim global equivalence with Naruyoko's original JavaScript. The ordinary Lean proof and the restricted-axiom paper proof have different verification scopes.

The seven Lean proofs now have independent subprojects in the same repository. Their exact source-import manifests are [Y](lean/Y/sources.json) (189 modules), [RPD](lean/RPD/sources.json) (36), [LRD](lean/LRD/sources.json) (41), [Ω-LRD3](lean/Omega-LRD3/sources.json) (44), [ARD](lean/ARD/sources.json) (50), [IPD](lean/IPD/sources.json) (55), and [ARD2](lean/ARD2/sources.json) (51). These are complete per-project closures, including shared dependencies and the extra compressed-root or tree-comparison entry points where applicable, not seven copies of the aggregate closure. Only Y includes the 12 pinned external BMS modules.

The [shared package](lean/shared/sources.json) owns 35 source modules. Its physical source files are reused without duplication; each notation imports only its required subset. Some shared filenames retain historical RPD/LRD/ARD prefixes because those files contain reused finite lemmas alongside their original declarations. File prefixes are therefore not a project-ownership rule. The [layout manifest](lean/layout.json) records each module's owner and repository-relative file; `source` in a source record remains provenance, while `file` identifies the current bundled location.

The [aggregate manifest](lean/sources.json) still covers all 322 modules, and `lean/src` retains only the four joint audit entries. Relocating 306 source files did not change any of the 310 bundled Lean files' bytes or module names. The 161 upstream Y modules are now under `lean/Y/src`; the external BMS sources remain unbundled. Normalized source hashes and original upstream records are preserved. Dependency pins, verification status and the final theorem index are in [lean/README.md](lean/README.md).

The bilingual [SPD manuscript](proofs/paper/spd-well-ordering.md) consolidates the fixed rule's local-rank interface, positive new-parent clause, endpoint agreement and closed-height supply, exact connector splice, minimum-last-label rank, and standard-cone argument. It refers to the included IPD paper for the existing KP rank and witness-closure machinery. **There is no SPD Lean formalization or kernel receipt.** This paper-level addition does not enlarge the scope of the seven-system Lean audit and does not claim an order-type comparison with ARD, ARD2, wY or the whole IPD notation.

## License boundary

- No public license has yet been chosen for this project's original notation code, Python code, papers, or packaging tools. Publishing a repository does not by itself grant an open-source license.
- The 161 unchanged bundled Y modules retain upstream Apache-2.0. A copy is included at [lean/licenses/1Y-Apache-2.0.txt](lean/licenses/1Y-Apache-2.0.txt), and source notices are preserved.
- The separate [BMS repository](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d) has no `LICENSE` or `NOTICE` file in the inspected pinned tree. Its source is **not vendored**; the build fetches the pinned dependency. Do not redistribute it under an inferred license.
- Mathlib and document-rendering packages are external dependencies with their own licenses. Their installed packages, fonts, and compiled caches are not release source files.

No project-wide license has yet been selected. Public availability is not a blanket license grant: preserve the third-party notices above, and review licensing before redistributing additional source material.
