# Lean proofs for four notations · [中文版](README.zh-CN.md)

This directory packages the ordinary, classical Lean proofs for **Y, RPD, LRD, and Ω-LRD3**. It is a source project, not a collection of precompiled certificates.

The restricted-axiom argument is in the separate [paper proof](../proofs/paper/well-ordering.md). These Lean theorems are **not** formalized derivations in the object theory `KP_ω + there exists an uncountable ordinal`. Their printed host-Lean axiom reports do not establish that metatheoretic upper bound.

## Main theorem entry points

Start with [FourNotationFinalAudit.lean](src/FourNotationFinalAudit.lean), which imports all four final modules and prints seven axiom reports.

| System | Final module | Main theorem |
| --- | --- | --- |
| Y | [FiniteDemandYFinal.lean](src/FiniteDemandYFinal.lean) | `OrdinalFormal.YFiniteDemand.generated_strictWellOrder` |
| RPD | [FiniteDemandRPDFinal.lean](src/FiniteDemandRPDFinal.lean) | `OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder` |
| LRD | [FiniteDemandLRDFinal.lean](src/FiniteDemandLRDFinal.lean) | `OrdinalFormal.LRDFinal.standard_isWellOrder` |
| Ω-LRD3 | [OmegaLRD3Final.lean](src/OmegaLRD3Final.lean) | `OrdinalFormal.Omega3Final.with_top_isWellOrder` |

The corresponding final modules also expose expansion well-foundedness, finite-domain results, or standard-domain variants. Their main well-ordering theorems do not take reflection, initial representations, row well-foundedness, or seed accessibility as assumptions supplied by the caller.

Y means the fixed upstream inherited-ancestry definition. Equivalence with every legal execution of an original JavaScript implementation is **not** a theorem in this package. RPD uses the current column/full-root formulation and includes its separate paper-standard-domain bridge. Ω-LRD3 uses single-column seeds and the inclusive row package `0 ≤ t ≤ b`; no other Ω-LRD version is shipped.

## Source layout

- `src/FiniteDemand*.lean`: the finite-demand semantic construction and its concrete host-Lean ambient instance.
- `src/OrdinalFormal/`: column diagrams, packages, comparison, representation descent, and the three new notation definitions.
- `src/OneY/`, `src/ZeroY/`: precisely the required upstream Y source closure, unchanged.
- `sources.json`: the complete import graph, origins, pinned revisions, and source hashes. Hashes normalize CRLF to LF, so Git line-ending conversion does not invalidate them.
- `build.py`: bounded source verification and axiom-report checking.

There are **225 bundled Lean modules**: 161 unchanged upstream Y modules and 64 local proof modules. Another **12 pinned BMS modules** are fetched as a Lake dependency. The proof-source closure is therefore **237 modules**, in addition to Lean, Mathlib, and Mathlib's dependencies. No unrelated paused object-theory work, build caches, historical notation definitions, or private absolute paths are required in the release.

The release-only copies of `OrdinalFormal/Domains.lean` and `OrdinalFormal/StandardValidity.lean` omit unused declarations for an earlier notation; all retained RPD/LRD proof terms are unchanged. Two final-module comments were updated to distinguish the completed paper argument from an unclaimed object-language Lean certification. `sources.json` records these changes and the original source hashes.

## Rebuild

Requirements: Git, Python 3.10 or newer, and Lean/Lake **4.33.1** (normally installed through elan). Run the following from this directory:

```sh
lake --keep-toolchain update
lake build
lake env python build.py
```

`lake build` is the normal portable build, including dependencies. `build.py` then recompiles the exact proof-source closure, checks the expected axiom reports, and produces a local `.build/verification.json`. Python may be named `python3` on your system.

The source dependency pins are:

| Dependency | Revision |
| --- | --- |
| Mathlib | `eba3d887fc52c98627f4b81507c0efc3096e91b9` |
| BMS / `YesMetaZFC` | `bae7e3d741f24a56d80da9b99c1345562cd10c2d` |
| Bundled 1Y source | `1689b21131b488ec2ba2515bd630360371a2389d` |

The pinned Mathlib source itself names Lean 4.33.0-rc1; this package deliberately uses 4.33.1, which is the compiler used for the existing verification. Keep the package toolchain unchanged. A cache built by a different compiler may be rejected; in that case the dependency must be rebuilt from its pinned source. Do not treat availability of a remote precompiled cache as part of the mathematical proof.

For an already prepared dependency environment, the bounded verifier can run directly. It uses one compiler process at a time, one Lean thread, a **2048 MiB per-compiler cap**, and a **120-second per-module wall timeout**. These bounds apply to `build.py`, not to arbitrary dependency installation commands. A timed-out child process tree is terminated; unrelated processes are never targeted.

```sh
python build.py --check-only
lake env python build.py --seconds 120 --memory-mb 2048
lake env python build.py --resume
```

`--check-only` verifies all bundled sources and the manifest closure without fetching anything. If the BMS checkout is absent, its 12 manifest entries are checked structurally and their bytes are verified when building after fetching it. `--resume` reuses only output hashes certified by this verifier for the same compiler and the same transitive source fingerprints; it is an incremental check, not a fresh rebuild.

Offline use is supported by `--lean`, `--bms-source`, and repeated `--external-path` arguments. Supply the pinned BMS **source** checkout and built Mathlib/dependency import directories, not prebuilt copies of this project's proof modules. Such machine-specific paths belong only in your command line, never in a committed configuration.

## Verification scope and status

The release was verified on **2026-09-13**: all **237 proof-source modules** were rebuilt, and all **554 expected axiom reports** passed. See the machine-path-free [verification receipt](VERIFICATION.json) and the five actual final-module logs: [Y](verification/FiniteDemandYFinal.log), [RPD](verification/FiniteDemandRPDFinal.log), [LRD](verification/FiniteDemandLRDFinal.log), [Ω-LRD3](verification/OmegaLRD3Final.log), and [combined audit](verification/FourNotationFinalAudit.log). The combined audit prints seven reports; the five final logs contain 28 reports in total.

This was a fresh rebuild of the complete proof-source closure, using existing Lean/Mathlib/dependency artifacts. It was **not** a fresh network bootstrap or a fresh rebuild of Mathlib itself. The Lake configuration was separately typechecked, and every bundled module was checked against its declared library roots. Compiled proof binaries and temporary build logs are excluded from the delivery; the retained receipt and final logs record the verification result.

The accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound` (or a subset). The verifier rejects `sorryAx`, reported `sorry` declarations, extra axioms in the printed reports, missing imports, hash mismatches, and incomplete report counts. This is not a proof-theoretic analysis of Lean's foundations, nor a claim of a minimal axiom bound for the notations.

## Upstream sources and licensing

The 161 bundled Y modules are copied unchanged from [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d). Their Apache-2.0 license is retained in [licenses/1Y-Apache-2.0.txt](licenses/1Y-Apache-2.0.txt); existing source notices are preserved.

The BMS source dependency is [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d). No `LICENSE` or `NOTICE` file was found at that revision. Therefore **no BMS source is redistributed here**: Lake fetches it separately from its original repository. Do not silently extend the Y repository's license to this separate dependency; clarify its license before redistributing its source yourself.

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) and its dependencies are also fetched externally and retain their own licenses. An upstream license is not a license grant for all original code or documents in this new project; the owner has not yet selected a project-wide public license.
