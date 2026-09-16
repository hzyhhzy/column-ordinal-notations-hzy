# Snapshot validation · [中文版](VALIDATION.zh-CN.md)

## 2026-09-16: ARD skyline migration

Default ARD is now the small skyline rule. The old NER, Python, bilingual definitions/PDFs, bilingual paper/PDFs and all 20 legacy Lean sources remain in ARD-legacy. The new implementation actually computes with skylines and a single predecessor; it does not hide a redundant graph behind its display. Other notation implementations, private Lean sources and receipts are unchanged.

- New [Python test](tests/test_ard.py): 250 graphs (150 standard), 1,000 projected legacy steps and 600 standard-order pairs; the NER cross-check also passed 1,000 expansions and 600 comparisons, in about 0.65 seconds.
- New [NER regression](tests/ard_skyline.cjs): 4,997 steps on 1,000 standard states and 2,472 steps on 500 strongly guarded raw graphs; 1,500 old/new counts, 500 literal local counts, 993 decrements, 3,000 order pairs, 1,000 adjacency round trips and 25 complete diagrams. All passed in 4.89 seconds, reported peak RSS 183 MiB, with a 512 MiB Node heap, a 90-second deadline and explicit width/iteration bounds.
- [Comparison probe](tests/rpd_ard_comparison.py): 275 states, 953 simulations, 15,866 local preparations, at most 966 per preparation, seven same-priority detours and 291 nonunique greatest source priorities. Coverage, V/F invariants and actual paths passed in 8.91 seconds. Caps: 25 seconds, 2,000 preparations/call, source width 10, target width 32, 80 states/seed.
- The [legacy test](tests/test_ard_legacy.py), generic Python tests and preserved arc/adjacency tests were rerun successfully. Old-core hash assertions remain, redirected to the legacy file; new diagrams have their own regression suite.
- The unchanged IPD and ARD2 Python suites also passed: respectively 247 graphs / 988 expansions and 37,044 graphs / 111,301 atomic expansions. Their implementation and proof sources were not edited.
- All nine verifier regressions passed, including rejection of extra axioms, stale receipts and shadowed dependencies, and independence from unrelated project metadata.

Current Lean 4.33.1 receipts:

| Project | Exact closure | Axiom reports | Freshly compiled | Explicitly reused |
| --- | --- | --- | --- | --- |
| [ARD-legacy](lean/ARD-legacy/VERIFICATION.json) | 50 | 156 | 20 | 30 |
| [ARD](lean/ARD/VERIFICATION.json) | 56 | 178 | 7 | 49 |
| [Optional aggregate](lean/VERIFICATION.json) | 330 | 897 | 5 | 325 |

Overlapping closures cannot be added as distinct modules. The new final theorem proves the actual small-rule expansion well-founded, the generated column order well-ordered, and the adjoined top well-ordered. No reflection/accessibility premise remains. Reports contain only subsets of `propext`, `Classical.choice`, `Quot.sound`. Compilers run sequentially with one thread, a 2048 MiB cap and a 120-second per-module deadline. This is not a KP object-theory derivation, a Mathlib source rebuild or a fresh network Lake bootstrap.

The [RPD bound](proofs/paper/rpd-le-ard-a2.md) and [legacy standard isomorphism](proofs/paper/ard-well-ordering.md) are paper proofs. Neither the finite tests nor the Lean axiom reports are formal comparison certificates. The comparison paper states the pinned 1Y convention.

Current publications comprise 32 definition artifacts across eight version directories (including legacy), 28 artifacts for seven bilingual papers, and 30 PDFs total. The ten affected PDFs were regenerated using ReportLab/MathJax, then rendered page by page with Poppler for bounds checks and visual inspection. Other PDFs are unchanged. `tools/check_release.py` checks the complete inventory and hashes: ten Lean scopes, 330 distinct modules and eight NER snapshots. No commit or push was made.

## Historical 2026-09-14 verification below

The old ARD name, old module counts and original display-only changes below refer to what is now ARD-legacy. These paragraphs are not the new source receipt; current status is given above and by each project's actual receipt.


Updated 2026-09-14. This record separates implementation tests, document checks, paper reasoning, and Lean kernel verification. None of these is silently substituted for another.

## Delivered documents

- RPD, LRD, Ω-LRD3, ARD, IPD, ARD2, SPD: seven definitions, each in English and Chinese Markdown and PDF, totaling **28 definition artifacts**.
- Y, RPD, LRD, Ω-LRD3: the original joint proof; ARD, IPD and ARD2: separate complete proofs. The four papers have English and Chinese Markdown and PDF versions, totaling **16 proof-paper artifacts**. IPD's direct KP tree-rank lemma is included as Appendix A, not left as an external research-file dependency.
- IPD additionally has a bilingual definition-correspondence audit.
- SPD adds a bilingual paper manuscript and PDFs: four further artifacts, making **20 proof-paper artifacts** in total. It has no Lean proof or verification receipt; the original seven Lean projects and aggregate theorem are unchanged.
- The main README, Lean instructions, source notes, and this record are also paired English/Chinese Markdown. Every English publication title links to its Chinese counterpart. The separate historical research archives include explicitly listed monolingual originals.
- Other Ω-LRD implementations, historical proof attempts, original private PDFs, installed dependencies, and precompiled proof caches are excluded from the release inventory.

The original joint paper's two languages contain the same 25 display equations and 15 numbered equation tags, in the same order. The new ARD paper has 34 English and 33 Chinese display equations: the sole difference is that the countable-boundedness formula is displayed in English but inline in Chinese. Its 15 numbered formulas agree, as do the six displays in each ARD definition. Mathematical bodies and hypotheses were cross-checked independently. The definition papers were cross-reviewed against the proofs for tuple order, control priority, package bound, seeds, standard domain, and top-element convention. The executable examples in both ARD definitions passed using the published Python module.

IPD's two proof versions each have 31 display equations and the same 12 equation tags, including Appendix A. Its English definition has ten display equations and the Chinese nine: the original-head replacement candidate is displayed in English and written as an inline code tuple in Chinese. Remaining differences concern inline typesetting, not definitions or hypotheses. The packaged Python example was executed successfully.

ARD2's two papers each have 25 display equations and the same 20 numbered equations. Apart from translation of the theory name, all display bodies agree after whitespace normalization. The two definitions have six displays each; one contains translated prose. Their four text examples and Python API example agree; the Python example was executed successfully.

## Expander checks

Command, from the package root:

```sh
python -B tests/test_python.py
python -B tests/test_ard_legacy.py
python -B tests/test_ipd.py
python -B tests/test_ard2.py
python -B tests/test_spd.py
node --max-old-space-size=256 tests/ard2_ner.cjs
node --max-old-space-size=256 tests/ard2_display.cjs
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
```

The seven test methods passed. The bounded sample included:

| Check | Count |
| --- | --- |
| Python expansion and prefix checks | 608 |
| Cross-language input cases | 160 |
| Python/NER expansion comparisons | 640 |
| Python/NER order comparisons | 400 |
| Ω-LRD3 / independent tuple-reference expansions | 152 |

The test suite has a 30-second overall checkpoint deadline and bounded queues/state sizes. Its Node comparison runs with a 15-second timeout and 256 MiB old-generation heap limit. No iterate-until-zero counterexample search is used. Node.js is optional for the pure Python tests; the JavaScript comparison is skipped if Node is unavailable. The reported snapshot was tested with Node present.

The separate ARD suite passed 120 graph cases and 480 expansions against an independently implemented full-root rule, 7 seeds, 8 invalid graph cases, invalid-index checks, 9 ARD/RPD boundary cases, and 48 common-descendant graphs with 192 expansions. Its cross-language checks covered 216 inputs, 864 expansions, 455 comparisons and 17 exact counts checked against a bounded naive local-count reference. This suite has a 40-second checkpoint deadline; its Node process has a 20-second timeout and 256 MiB old-generation heap limit. The two Python test commands took approximately 0.6 and 2.0 seconds.

The ARD arc-renderer suite additionally passed 240 random cases, 480 expansions, 480 comparisons, 241 counts, 22 drawings with 525 relations/root frames, 2,395 lane checks, 24,601 label-pair checks, 8,710 drawn-segment checks, 17,036 frame-line checks, 6 flip pairs, and 8 guard cases. It ran in approximately 1.1 seconds with a 192 MiB old-generation heap limit and approximately 126 MiB peak reported RSS. The Node limits are not hard caps on total process memory. These are geometry and API checks, not screenshots from a live browser.

The original three Python command-line examples also passed. LRD and Ω-LRD3's NER files remain byte-for-byte unchanged. The updated RPD and ARD scripts embed the entire previously published scripts from `542d47a` unchanged, with registration metadata and two adjacency displays added around them. All delivered SHA-256 values are in [SOURCES.md](SOURCES.md). The Ω-LRD3 tuple reference's separate bounded self-check passed 7 seeds, 37 states, 148 descent checks, and 111 prefix checks.

The portable adjacency suite passed 168 graphs and text round trips, 672 unchanged expansions, 160 comparisons, 498 text-prefix checks, 168 complete diagrams containing 942 relation entries, 420 old-display comparisons and 20 input/resource guards. It pins the embedded old cores by normalized source hashes and checks that both new display helpers agree. Diagram checks cover whole shaded diagonal index cells, the stepped upper-triangular boundary, removal of external axis labels, exact original counts above the tables, and preservation of complete relation tables when counts report a resource limit. It ran in approximately 1.3 seconds with a 256 MiB old-generation heap limit and about 87 MiB reported RSS. Light, dark, empty and multi-digit full previews were rendered offline and visually inspected; this is not a live-browser end-to-end test. The mathematical and proof sources were not changed by this display update.

The new IPD test passed 247 graphs (117 marked standard), 988 Python/JS expansions, 741 full-prefix checks, 500 order comparisons, 231 exact local-count sequences, 453 count-decrement checks, 1,292 larger closed-form count terms, 247 complete tree displays and 22 guards, plus 16 Python seed checks. The bounded oracle explicitly skipped 8 expensive expansion cases and 16 count cases; skipped cases are not successes. This run took 5.56 seconds; Node reported 130 MiB RSS with a 512 MiB old-generation heap limit. The wrapper gives Python 30 seconds and Node 55 seconds, with process-tree cleanup. A separate display regression passed 12 samples, 76 node occurrences, 9 nested-head frames, 51 child links and 2 guards. It requires no NER checkout and makes no live-browser claim. The older Python, ARD, adjacency and arc suites were rerun successfully without modifying their definitions.

ARD2's independent atomic oracle passed 37,044 graphs and 111,301 expansions, including every canonical legal graph of width at most three, seeds and bounded random cases. The Python run took about 11.1 seconds with 25.3 MiB peak RSS. Node passed 996 independent atomic steps, 676 Python-to-JavaScript expansion vectors, 169 comparisons and seven count cases in about one second with 83 MiB RSS. The display suite passed eight samples, 153 complete arc groups, 34 table entries, seven text round trips and five guard cases, including count exhaustion that leaves complete geometry visible. Node used a 256 MiB heap; the tests check 512 MiB RSS and explicit time/work bounds. Seven complete light/dark SVG previews were rendered from the real JS output and visually reviewed; this is an offline rendering check, not a live NER session. The old six test commands were independently rerun successfully, with every previously tracked notation and Lean mathematical source unchanged.

The unified SPD test is self-contained and imports no private research files. It passed an independent tuple oracle on 65 standard states / 260 expansions, 45 raw diagrams / 180 expansions, 100 comparisons and 162 local count decrements, plus 9 invalid-input cases, 4 resource guards and a 1,200-column iterative chain. A separate mixed-parent check passed 160 raw diagrams / 640 expansions / 441 count decrements. The count decoder recovered all 65 standard states and classified all 86 count words of width at most three (43 valid / 43 invalid), including checks distinguishing raw count collisions from standard membership.

SPD's NER test passed 65 standard states / 260 expansions. Python-to-JavaScript vectors agreed on 44 diagrams / 176 expansions / 100 comparisons, and count decoding agreed on 106 inputs (63 accepted / 43 rejected). The unified run took about 18 seconds. Python peak RSS stayed below 35 MiB under a 256 MiB monitored bound; Node used a 256 MiB old-generation heap ceiling and reported less than 130 MiB RSS. The wrapper imposes a 54-second overall checkpoint deadline, caps each child at 50 seconds and terminates and waits for its own direct child on timeout; these children launch no further processes. Allocation, queue and iteration bounds are explicit. The Python examples in the definition were executed separately. These are registration-stub tests, not live NER browser clicks.

During SPD integration, the earlier Python, ARD, IPD, ARD2, display, adjacency and Lean-verifier regression suites were rerun successfully. The six older notation implementations and all Lean sources/receipts remain unchanged. No new Lean kernel compilation is claimed.

These are finite tests. They do not establish equivalence on every input, certify standardness of arbitrary parsed graphs, or replace a well-ordering proof. A full live-browser integration test was not repeated during packaging.

## PDF checks

The release contains **24 PDFs / 158 pages**, generated with ReportLab, MathJax formulas and embedded fonts. All twenty earlier PDFs / 124 pages remain byte-identical and retain their previous visual reviews. SPD adds 8 English-definition pages, 6 Chinese-definition pages, 11 English-proof pages and 9 Chinese-proof pages.

All **34 new SPD pages** were rendered with Poppler and passed text/image bounds checks with zero overflow, then visually inspected in contact sheets. English definition page 4, English proof pages 8–9, and Chinese proof page 7 were also inspected at full-page resolution. The Chinese definition was tightened to avoid a short seventh page; earlier PDFs were not regenerated.

SPD has its own title and 2026-09-14 footer. Each definition has 18 display formulas; each proof has 37 display formulas and the same 20 equation tags. Mathematical expressions and hypotheses were cross-checked across languages. The corrected strict guard and endpoint formulas render without missing symbols or clipping.

[tools/pdf-build-report.json](tools/pdf-build-report.json) records page counts and hashes; [the QA receipt](tools/pdf-qa-report.json) distinguishes this new review from the preserved reviews of the earlier 124 pages. Commands are in the [main README](README.md). Intermediate images and formula caches are excluded from release source.

## Lean source verification

The source union remains **310 bundled modules plus 12 pinned external BMS modules: 322 in total**. The split moves 306 files into shared and seven private notation projects; four aggregate modules remain in place. The exact bytes of all 310 bundled files were compared: mathematical sources and module names are unchanged.

Projects have independent source manifests, Lake configurations, toolchains, lockfiles, outputs and verification receipts. Exact closures are shared 35, Y 189, RPD 36, LRD 41, Ω-LRD3 44, ARD 50, IPD 55 and ARD2 51. These counts include overlapping shared dependencies, not disjoint module sets. Only Y depends on external BMS.

`python lean/ARD2/build.py --check-only` checks only ARD2's exact closure, source hashes and project Lake enumeration, without loading another notation. The root `python lean/build.py --check-only` is an optional repository-wide check.

The pre-split fresh sequential seven-system rebuild genuinely passed **322 modules / 866 axiom reports** in 1638.176 seconds. Its [unchanged archived receipt](lean/verification/SevenNotation-Monolithic-VERIFICATION.json) records that run and is not relabeled as a new-layout build.

Nine regression groups in `python -B tests/test_lean_verifier.py` passed: exact nine-project closures, all five import-artifact fingerprints, per-module cleanup, external-cache shadowing rejection, named/count-checked axiom logs, stale/incomplete receipts, project locks, unrelated-project fingerprint stability, and current import syntax/nested comments. These tests use temporary data and never pass fake artifacts to Lean; the actual kernel checks come from the source compilations below.

The independent projects genuinely passed, with separate receipts:

| Project receipt | Closure modules | Axiom reports | Newly compiled | Explicitly certified reuse |
| --- | --- | --- | --- | --- |
| [shared](lean/shared/VERIFICATION.json) | 35 | 93 | 35 | 0 |
| [Y](lean/Y/VERIFICATION.json) | 189 | 422 | 175 | 14 |
| [RPD](lean/RPD/VERIFICATION.json) | 36 | 91 | 4 | 32 |
| [LRD](lean/LRD/VERIFICATION.json) | 41 | 110 | 10 | 31 |
| [Ω-LRD3](lean/Omega-LRD3/VERIFICATION.json) | 44 | 119 | 13 | 31 |
| [ARD](lean/ARD-legacy/VERIFICATION.json) | 50 | 156 | 20 | 30 |
| [IPD](lean/IPD/VERIFICATION.json) | 55 | 166 | 40 | 15 |
| [ARD2](lean/ARD2/VERIFICATION.json) | 51 | 160 | 21 | 30 |
| [Optional aggregate](lean/VERIFICATION.json) | 322 | 866 | 4 | 318 |

The shared foundation is compiled fresh first; leaves reuse only that newly certified shared baseline, and the aggregate reuses those certified leaf/shared artifacts and compiles four joint modules. The [combined check](lean/verification/IndependentProjects-VERIFICATION.json) compares every module's fingerprint, complete import-artifact hashes and reports, confirming that, in the initial migration verification, **all 322 distinct modules were freshly compiled exactly once, with all 866 distinct axiom reports passing**. Closure sizes overlap; their sum is not a count of distinct modules.

Real Lake passed 18 checks across nine exact configurations for loading, unique ownership, default enumeration and import lookup. The [configuration/migration receipt](lean/verification/ProjectLayout-VERIFICATION.json) distinguishes these checks from a completed `lake build`. Adding an intentionally broken new project and an unrelated broken Y source in a scratch copy left both ARD2 checks passing; loading the broken project itself failed as a negative control.

The final read-only consistency check rehashed the actual compiler, implicit sysroot and external import artifacts, then validated all nine projects' public/local receipts, complete artifact bundles and logs. All passed; this check does not rerun the Lean kernel. During additional `--resume` tests, RPD and ARD2 each encountered a transient Windows file-replacement refusal. Failed checkpoints were correctly marked incomplete, original public successful receipts stayed unchanged, and both retries passed. Initial compilation statistics are recorded separately from these later retries.

The source verifier accepts only reported `propext`, `Classical.choice`, `Quot.sound`, or subsets. Compilation uses existing Lean and pinned Mathlib/auxiliary artifacts, but builds local proofs from checked sources. No fresh network bootstrap or Mathlib source rebuild is claimed. The [Lean guide](lean/README.md) documents resource bounds and cache inputs; generated binaries and local caches are not distributed.

The documentation link migration changes only relative source URLs, not formulas or visible labels. The PDF renderer emits only labels for relative links, so all 20 PDFs remain unchanged. Three old Lean addresses in ARD2's JS/Python explanatory text are corrected separately without changing expansion rules; the other five notation implementations stay unchanged.

## Scope that remains explicit

All four papers argue in `KP_ω + there exists an uncountable ordinal`, with full set induction; the ordinary Lean proofs are not object-language derivations in that system. The finite geometric interfaces used in the papers are linked to their concrete verified source implementations. For ARD, Lean additionally proves equality with an independently defined finite-union expansion rule and standard domain, plus exact agreement of the compressed and full-root comparisons and controllers. This is not a formal verification of every line of the Python or JavaScript runtime.

For ARD2, Lean constructs the actual two-SELF relation and unconditional initial supply, proves the whole staged splice, and identifies the independent paper finite rule and reachable domain. The standard subtype contains neither accessibility nor representability as an assumption. The paper's weak-KP construction is distinct from the ordinary-Lean proof.

For IPD, Lean proves the actual all-position mathematical rule; the source-language correspondence and exact two-position JS pruning are established in the [paper audit](proofs/paper/ipd-fidelity.md), not a JS-VM formalization. IPD's standard subtype does not assume accessibility or representability. Neither comparison with wY/TPD nor cofinality is added as a claim.

The well-ordering conclusions concern the stated standard domains, with the documented top-element conventions, not the column order on arbitrary parsed graphs. The Y theorem is for the fixed upstream inherited-ancestry definition. Full legal-domain equivalence with Naruyoko's original JavaScript remains outside this package's claims. No optimal axiom strength, proof-theoretic ordinal comparison, or relative order-type inequality between the seven Lean-verified systems or involving SPD is established by this packaging task.

Run `python tools/check_release.py` to check language pairing, relative entry links, the twenty-four PDF/source pairs and build hashes, NER snapshot hashes, private-path exclusions, the Lean source closure, and consistency of the public verification receipt with the current manifest, per-module dependency fingerprints, build inputs and final theorem logs. This consistency check does not rerun the Lean kernel.

The final SPD integration check passed **73 Markdown files: 52 bilingual publication files and 21 explicitly listed monolingual archives**, 24 PDFs, seven pinned NER scripts, and all nine existing Lean verification scopes / 322 distinct modules. The old checker had incorrectly required translations for those 21 already tracked, unchanged research originals; its exact-path exception now waives only counterpart and language-link requirements. Heading syntax, formulas, all local links, private-path exclusions, and all Lean checks remain active, and a missing named archive fails validation. No new file is automatically exempted by its directory.
