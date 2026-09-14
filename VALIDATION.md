# Snapshot validation · [中文版](VALIDATION.zh-CN.md)

Updated 2026-09-14. This record separates implementation tests, document checks, paper reasoning, and Lean kernel verification. None of these is silently substituted for another.

## Delivered documents

- RPD, LRD, Ω-LRD3, ARD, IPD: five definitions, each in English and Chinese Markdown and PDF, totaling **20 definition artifacts**.
- Y, RPD, LRD, Ω-LRD3: the original joint proof; ARD and IPD: separate complete proofs. The three papers have English and Chinese Markdown and PDF versions, totaling **12 proof-paper artifacts**. IPD's direct KP tree-rank lemma is included as Appendix A, not left as an external research-file dependency.
- IPD additionally has a bilingual definition-correspondence audit.
- The main README, Lean instructions, source notes, and this record are also paired English/Chinese Markdown. Every English title links to its Chinese counterpart.
- Other Ω-LRD implementations, historical proof attempts, original private PDFs, installed dependencies, and precompiled proof caches are excluded from the release inventory.

The original joint paper's two languages contain the same 25 display equations and 15 numbered equation tags, in the same order. The new ARD paper has 34 English and 33 Chinese display equations: the sole difference is that the countable-boundedness formula is displayed in English but inline in Chinese. Its 15 numbered formulas agree, as do the six displays in each ARD definition. Mathematical bodies and hypotheses were cross-checked independently. The definition papers were cross-reviewed against the proofs for tuple order, control priority, package bound, seeds, standard domain, and top-element convention. The executable examples in both ARD definitions passed using the published Python module.

IPD's two proof versions each have 31 display equations and the same 12 equation tags, including Appendix A. Its English definition has ten display equations and the Chinese nine: the original-head replacement candidate is displayed in English and written as an inline code tuple in Chinese. Remaining differences concern inline typesetting, not definitions or hypotheses. The packaged Python example was executed successfully.

## Expander checks

Command, from the package root:

```sh
python -B tests/test_python.py
python -B tests/test_ard.py
python -B tests/test_ipd.py
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

These are finite tests. They do not establish equivalence on every input, certify standardness of arbitrary parsed graphs, or replace a well-ordering proof. A full live-browser integration test was not repeated during packaging.

## PDF checks

The release contains **16 PDFs / 102 pages**, generated with ReportLab, MathJax formulas and embedded fonts. The original twelve PDFs / 66 pages are unchanged. IPD adds 6 English-definition pages, 5 Chinese-definition pages, 14 English-proof pages and 11 Chinese-proof pages. All 36 new pages were visually inspected in contact sheets; repaired English request formulas and selected dense Chinese/rank pages were also inspected at page resolution. All 102 pages were rerendered with Poppler and passed text/image bounds checks with zero overflow.

The new Chinese formula delimiters were normalized for Markdown/PDF compatibility. Consecutive English displays were separated to repair a clipped line of request formulas. IPD received its own title and 2026-09-14 footer; appendix cross-references were qualified to avoid collisions with the main paper. The final Chinese amendment was rerendered and all its pages reinspected. No formula is replaced by a blank or silently dropped.

[tools/pdf-build-report.json](tools/pdf-build-report.json) records page counts and hashes; [the QA receipt](tools/pdf-qa-report.json) gives the current 102-page scope. Commands are in the [main README](README.md). Intermediate images and formula caches are excluded from release source.

## Lean source verification

The package contains 288 Lean source modules and describes 12 additional pinned external BMS modules. `python lean/build.py --check-only` verifies the complete 300-module import closure and the bundled source hashes without downloading anything. The external BMS bytes are additionally hash-checked when their source checkout is supplied for compilation.

A fresh sequential rebuild of **all 300 proof-source modules passed**, with **774 axiom reports**. The [public receipt](lean/VERIFICATION.json) and [Lean instructions](lean/README.md) identify this six-system rebuild. IPD contributes 40 proof modules and one new joint audit. The earlier four- and five-system receipts and audits are retained as historical records, not used instead of rebuilding IPD.

Only existing Lean and pinned Mathlib/auxiliary-package artifacts are reused. The publication build recompiles Y, external BMS, and local notation proof modules from their checked sources; it does not load the old research project's proof caches. This is not a fresh network bootstrap or a rebuild of all Mathlib dependencies. The Lake configuration is separately checked in offline mode with local dependency overrides. Generated build artifacts are excluded from the release inventory.

The accepted reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. Resource and build details are in [lean/README.md](lean/README.md). Dependency bootstrapping is distinct from fresh recompilation of this project's proof-source closure.

## Scope that remains explicit

All three papers argue in `KP_ω + there exists an uncountable ordinal`, with full set induction; the ordinary Lean proofs are not object-language derivations in that system. The finite geometric interfaces used in the papers are linked to their concrete verified source implementations. For ARD, Lean additionally proves equality with an independently defined finite-union expansion rule and standard domain, plus exact agreement of the compressed and full-root comparisons and controllers. This is not a formal verification of every line of the Python or JavaScript runtime.

For IPD, Lean proves the actual all-position mathematical rule; the source-language correspondence and exact two-position JS pruning are established in the [paper audit](proofs/paper/ipd-fidelity.md), not a JS-VM formalization. IPD's standard subtype does not assume accessibility or representability. Neither comparison with wY/TPD nor cofinality is added as a claim.

The well-ordering conclusions concern the stated standard domains, with the documented top-element conventions, not the column order on arbitrary parsed graphs. The Y theorem is for the fixed upstream inherited-ancestry definition. Full legal-domain equivalence with Naruyoko's original JavaScript remains outside this package's claims. No optimal axiom strength, proof-theoretic ordinal comparison, or relative order-type inequality between the six systems is established by this packaging task.

Run `python tools/check_release.py` to check language pairing, relative entry links, the sixteen PDF/source pairs and build hashes, NER snapshot hashes, private-path exclusions, the Lean source closure, and consistency of the public verification receipt with the current manifest, per-module dependency fingerprints, build inputs and final theorem logs. This consistency check does not rerun the Lean kernel.
