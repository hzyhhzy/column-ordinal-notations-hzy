# Lean proofs for seven notations · [中文版](README.zh-CN.md)

2026-09-17: default ARD2 is the skyline edition; [ARD2-legacy](ARD2-legacy/README.md) retains all 21 unchanged old mathematical modules. The new project owns seven modules with a 57-module closure; legacy has 51. The current [ARD2RevisionFinalAudit](src/ARD2RevisionFinalAudit.lean) covers 338 modules. September 14/16 counts below are historical; project receipts state current certification. Exact isomorphism remains a paper result.

2026-09-16: default ARD is now the skyline edition, with ARD-legacy preserved. The new rule's well-ordering passed 56 modules / 178 reports, including seven newly compiled modules. The relocated legacy project passed 50 modules / 156 reports. The current aggregate receipt contains 330 modules / 897 reports: five aggregate entries freshly compiled and 325 verified modules reused. The dated 2026-09-14 split-verification accounts below are historical. The full legacy isomorphism and cross-notation comparisons remain paper results, not consequences of printed axiom lists.


This directory packages the ordinary, classical Lean proofs for **Y, RPD, LRD, Ω-LRD3, ARD, IPD, and ARD2**. It is a source project, not a collection of precompiled certificates.

The restricted-axiom arguments are in the separate [four-system paper](../proofs/paper/well-ordering.md), [ARD paper](../proofs/paper/ard-well-ordering.md), [IPD paper](../proofs/paper/ipd-well-ordering.md), and [ARD2 paper](../proofs/paper/ard2-well-ordering.md). These Lean theorems are **not** formalized derivations in the object theory `KP_ω + there exists an uncountable ordinal`. Their printed host-Lean axiom reports do not establish that metatheoretic upper bound.

## Main theorem entry points

Start with the notation's own project. The root [ARD2RevisionFinalAudit.lean](src/ARD2RevisionFinalAudit.lean) is an optional aggregate audit, not a required build step whenever a notation is added. All four historical aggregate modules remain unchanged.

| System | Final module | Main theorem |
| --- | --- | --- |
| Y | [FiniteDemandYFinal.lean](Y/src/FiniteDemandYFinal.lean) | `OrdinalFormal.YFiniteDemand.generated_strictWellOrder` |
| RPD | [FiniteDemandRPDFinal.lean](RPD/src/FiniteDemandRPDFinal.lean) | `OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder` |
| LRD | [FiniteDemandLRDFinal.lean](LRD/src/FiniteDemandLRDFinal.lean) | `OrdinalFormal.LRDFinal.standard_isWellOrder` |
| Ω-LRD3 | [OmegaLRD3Final.lean](Omega-LRD3/src/OmegaLRD3Final.lean) | `OrdinalFormal.Omega3Final.with_top_isWellOrder` |
| ARD-legacy | [ARDFinal.lean](ARD-legacy/src/ARDFinal.lean) | `OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder` |
| ARD | [ARDSkylineFinal.lean](ARD/src/ARDSkylineFinal.lean) | `OrdinalFormal.ARDSkyline.standard_with_top_strictWellOrder` |
| IPD | [IPDStandardOrder.lean](IPD/src/IPDStandardOrder.lean) | `IPD.standard_wellFounded`, `IPD.standard_total`, `IPD.term_wellFounded` |
| ARD2-legacy | [ARD2Final.lean](ARD2-legacy/src/ARD2Final.lean) | `OrdinalFormal.ARD2.paper_standard_with_top_strictWellOrder` |
| ARD2 | [ARD2SkylineFinal.lean](ARD2/src/ARD2SkylineFinal.lean) | `OrdinalFormal.ARD2Skyline.standard_with_top_strictWellOrder` |

The corresponding final modules also expose expansion well-foundedness, finite-domain results, or standard-domain variants. Their main well-ordering theorems do not take reflection, initial representations, row well-foundedness, or seed accessibility as assumptions supplied by the caller.

Y means the fixed upstream inherited-ancestry definition. Equivalence with every legal execution of an original JavaScript implementation is **not** a theorem in this package. RPD uses the current column/full-root formulation and includes its separate paper-standard-domain bridge. Ω-LRD3 uses single-column seeds and the inclusive row package `0 ≤ t ≤ b`; no other Ω-LRD version is shipped. ARD-legacy moves all four coordinates (including the row anchor) and includes all natural rows below the moved control row. Its [independent finite-rule bridge](ARD-legacy/src/ARDDefinitionFidelity.lean) identifies the paper and executable standard domains; [ARDCompression.lean](ARD-legacy/src/ARDCompression.lean) proves exact comparison and controller agreement for canonical compressed maximum-root lists versus complete-root lists. The mathematics is linked to an independently specified finite rule, not a compiler-level verification of Python or JavaScript execution.

IPD's standard domain is finite reachability from zero-start seeds, not an accessibility subtype. Its actual parent-first column order is well-founded and total; TOP is adjoined. Strict expansion is additionally well-founded on all structurally valid raw graphs, without asserting their global column order well-founded. See the [correspondence audit](../proofs/paper/ipd-fidelity.md).

ARD2 permits both row and root SELF at the child column and keeps parents strict. Its new [subdiagram bridge](ARD2/src/ARD2SkylineBridge.lean) proves actual skyline-rule output inclusion in the preserved full-package backend. The backend's [finite-rule](ARD2-legacy/src/ARD2DefinitionFidelity.lean) and [maximum-root compression](ARD2-legacy/src/ARD2Compression.lean) bridges concern ARD2-legacy, not the new skyline isomorphism. The semantic relation and initial supply are constructed, not assumed. See the [definition](../notations/ARD2/definition.md).

## Independent project layout

| Project | Private source directory | Private modules | Exact proof closure |
| --- | --- | --- | --- |
| [Y](Y/README.md) | `Y/src/` | 163 | 189 |
| [RPD](RPD/README.md) | `RPD/src/` | 4 | 36 |
| [LRD](LRD/README.md) | `LRD/src/` | 10 | 41 |
| [Ω-LRD3](Omega-LRD3/README.md) | `Omega-LRD3/src/` | 13 | 44 |
| [ARD](ARD/README.md) | `ARD/src/` | 7 | 56 |
| [ARD-legacy](ARD-legacy/README.md) | `ARD-legacy/src/` | 20 | 50 |
| [IPD](IPD/README.md) | `IPD/src/` | 40 | 55 |
| [ARD2-legacy](ARD2-legacy/README.md) | `ARD2-legacy/src/` | 21 | 51 |
| [ARD2](ARD2/README.md) | `ARD2/src/` | 7 | 57 |
| [Shared foundation](shared/README.md) | `shared/src/` | 35 | 35 |
| Optional aggregate audit | `src/` | 6 | 338 |

Each notation has its own `lakefile.lean`, toolchain, lockfile, `sources.json`, `build.py`, output directory and verification receipt. The original notation projects depend on shared modules only; only Y additionally needs external BMS. New ARD and ARD2 explicitly depend on their respective legacy semantic backends as well as shared. Unrelated notation projects remain independent. Closure counts include the shared modules actually imported and cannot be added as counts of distinct sources.

There are **326 bundled modules** (161 unchanged upstream Y modules and 165 local modules), plus **12 pinned external BMS modules**, for **338 distinct proof-source modules**. Each skyline revision added seven private modules and one aggregate entry. The 20 ARD-legacy and 21 ARD2-legacy mathematical source files were relocated unchanged; all preceding aggregate source files remain unchanged.

[layout.json](layout.json) is a repository index, not an input to individual project cache fingerprints. Each project's `sources.json` records its exact source closure, origins, revisions, SHA-256 hashes and real paths. Hashes normalize CRLF to LF. Shared foundation files retain some historical RPD/LRD/ARD names because their definitions and lemmas already had multiple consumers; this does not create dependencies on those notation leaf projects.

## Build one notation

Requirements: Git, Python 3.10+, and Lean **4.33.1** with its bundled Lake. For example, build only ARD2 from the repository root:

```sh
cd lean/ARD2
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048 --publish
```

`lake build` is the normal build. The additional bounded verifier checks the exact source closure and axiom reports, writing this project's `.build/verification.json`. `--publish` additionally writes a machine-path-free `VERIFICATION.json` and selected logs. Use the other project directories for other notations. **Do not default to the root aggregate build when adding one notation.**

After preparing dependencies:

```sh
python build.py --check-only
lake env python build.py --resume --publish
```

`--check-only` performs no download or compilation and validates this project's sources, closure and Lake enumeration. If Y's external BMS checkout is absent, its manifest entries are checked structurally; actual compilation also checks source bytes. `--resume` is incremental verification, not a fresh rebuild: source, recursive dependency, artifact and log fingerprints must still match in the same verification environment.

`--resume` accepts only a previous **complete successful** receipt that still matches. It does not continue compilation from failed or interrupted partial checkpoints; those cases rebuild the current project's closure. Normal Lake incremental builds are separate.

The verifier runs one compiler at a time, one Lean thread, with a **2048 MiB** compiler limit and **120 seconds** per module. Timeouts terminate only its own child process tree. These bounds do not apply to separately invoked dependency installation or arbitrary `lake build` commands.

Offline use accepts `--lean` and repeated `--external-path` arguments for Lean and built Mathlib/auxiliary-package import directories. Y and the aggregate additionally need `--bms-source`, which must supply BMS **source**. Do not disguise this project's old proof caches as external libraries. Machine-specific paths belong only in local commands, never in committed configuration.

Keep the sources, configuration, compiler and external dependencies being checked unchanged during verification; this verifier is not a concurrent-edit snapshot protocol. The import-manifest parser targets the single-line `import M` / `public import M` forms used by the current sources. Adopting `meta import` or `import all` requires extending the parser and revalidation first, not silently retaining an old closure claim.

When the shared foundation already has current verified artifacts, reuse them explicitly. For example, first run its bounded verifier in `lean/shared/`, then from the ARD2 project:

```sh
lake env python build.py --reuse-from ../shared --publish
python build.py --check-receipt
```

Cross-project reuse checks sources, environment, complete import-artifact bundles and logs. Receipts distinguish newly compiled from reused modules. `--check-receipt` checks the published record against current sources; it neither reruns the kernel nor remeasures the local external compiler environment.

## Add a notation without disturbing existing ones

1. Create its own `lean/Name/` with private sources, configuration, exact closure manifest and receipt; depend on the existing shared foundation.
2. Preserve existing notation sources, lockfiles, manifests and receipts. Choose non-conflicting module names; declare only owned modules in Lake.
3. Compile the new project and its actual shared dependencies. Repository README/catalog updates are allowed but are not old projects' cache inputs.
4. Update the optional root aggregate only when a joint audit is wanted. Leaf projects never depend back on the root.
5. If a shared lemma or toolchain genuinely needs modification, identify and recheck affected consumers. A changed dependency cannot retain an old verification claim unquestioned.

## Dependencies and verification scope

| Dependency | Pinned revision |
| --- | --- |
| Mathlib | `eba3d887fc52c98627f4b81507c0efc3096e91b9` |
| BMS (Y only) | `bae7e3d741f24a56d80da9b99c1345562cd10c2d` |
| Bundled Y source | `1689b21131b488ec2ba2515bd630360371a2389d` |

The pinned Mathlib source names Lean 4.33.0-rc1; this package keeps the verified compiler 4.33.1. Artifacts built by another compiler may be incompatible; rebuild dependencies from pinned sources if necessary. Remote cache availability is not part of the proof.

The pre-split fresh seven-system rebuild passed: **322 modules, 866 axiom reports, 1638.176 seconds**. Its unchanged evidence is retained in the [historical seven-system receipt](verification/SevenNotation-Monolithic-VERIFICATION.json). Post-split project results are published separately, not obtained by relabeling the old receipt.

The new layout was verified on **2026-09-14**. The [combined receipt](verification/IndependentProjects-VERIFICATION.json) checks nine actual project receipts: the shared foundation is compiled first; notation projects reuse only its certified artifacts and compile their private sources; Y also compiles 12 BMS sources; the aggregate reuses those results and compiles four joint modules. In the initial migration verification, all **322 distinct proof modules were compiled from source once in the new layout, with 866 distinct axiom reports**. Overlapping closure sizes must not be added as distinct module counts, and cached reuse is not called fresh compilation.

Each project README links to its independent `VERIFICATION.json`; see the [validation record](../VALIDATION.md) for per-project fresh/reused counts. Real Lake additionally passed 18 checks across nine exact configurations for loading, ownership, import lookup and default enumeration. The [layout receipt](verification/ProjectLayout-VERIFICATION.json) records the isolation test where an unrelated broken project leaves ARD2 passing. These are Lake configuration checks; proof compilation was performed by the bounded verifier, not a separately completed `lake build`.

Accepted reported axioms are only `propext`, `Classical.choice`, and `Quot.sound` (or a subset). The verifier rejects `sorryAx`, reported `sorry`, extra axioms, missing imports, hash mismatches and incomplete report counts. It is not a proof-theoretic analysis of Lean's foundations or a weak-KP object derivation. A fresh network bootstrap and a source rebuild of Mathlib are outside this verification scope. Generated binaries and local caches are not committed.

## Upstream sources and licensing

The 161 bundled Y modules are copied unchanged from [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d). Their Apache-2.0 license is retained in [licenses/1Y-Apache-2.0.txt](licenses/1Y-Apache-2.0.txt); existing source notices are preserved.

The BMS source dependency is [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d). No `LICENSE` or `NOTICE` file was found at that revision. Therefore **no BMS source is redistributed here**: Lake fetches it separately from its original repository. Do not silently extend the Y repository's license to this separate dependency; clarify its license before redistributing its source yourself.

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) and its dependencies are also fetched externally and retain their own licenses. An upstream license is not a license grant for all original code or documents in this new project; the owner has not yet selected a project-wide public license.
