# Snapshot validation · [中文版](VALIDATION.zh-CN.md)

Prepared 2026-09-13. This record separates implementation tests, document checks, paper reasoning, and Lean kernel verification. None of these is silently substituted for another.

## Delivered documents

- RPD, LRD, Ω-LRD3: three definitions, each in English and Chinese Markdown and PDF, totaling **12 definition artifacts**.
- Y, RPD, LRD, Ω-LRD3: one complete joint proof in both languages and formats, totaling **4 proof-paper artifacts**.
- The main README, Lean instructions, source notes, and this record are also paired English/Chinese Markdown. Every English title links to its Chinese counterpart.
- Other Ω-LRD implementations, historical proof attempts, original private PDFs, installed dependencies, and precompiled proof caches are excluded from the release inventory.

The paper's two languages contain the same 25 display equations and 15 numbered equation tags, in the same order. Mathematical display bodies were cross-checked after allowing translated textual phrases and whitespace. The definition papers were cross-reviewed against the joint proof for tuple order, control priority, package bound, seeds, standard domain, and top-element convention.

## Expander checks

Command, from the package root:

```sh
python -B tests/test_python.py
```

The seven test methods passed. The bounded sample included:

| Check | Count |
| --- | --- |
| Python expansion and prefix checks | 456 |
| Cross-language input cases | 121 |
| Python/NER expansion comparisons | 484 |
| Python/NER order comparisons | 300 |
| Ω-LRD3 / independent tuple-reference expansions | 152 |

The test suite has a 30-second overall checkpoint deadline and bounded queues/state sizes. Its Node comparison runs with a 15-second timeout and 256 MiB heap cap. No iterate-until-zero counterexample search is used. Node.js is optional for the pure Python tests; the JavaScript comparison is skipped if Node is unavailable. The reported snapshot was tested with Node present.

The three Python command-line examples also passed. The NER files matched the original selected scripts byte-for-byte; their SHA-256 values are in [SOURCES.md](SOURCES.md). The Ω-LRD3 tuple reference's separate bounded self-check passed 7 seeds, 37 states, 148 descent checks, and 111 prefix checks.

These are finite tests. They do not establish equivalence on every input, certify standardness of arbitrary parsed graphs, or replace a well-ordering proof. A full live-browser integration test was not repeated during packaging.

## PDF checks

Eight PDFs were generated with ReportLab and MathJax formulas, with fonts embedded from the local machine. The PDFs comprise **41 pages**. All pages were rendered using Poppler; body/formula placement was checked, including numbered equations, Chinese text, tables, code examples, headers, and page numbers. Programmatic text/image boundary checks found no overflow. The final Chinese paper has nine pages; its spacing was tightened slightly to avoid an almost-empty tenth page.

Two renderer issues found during inspection were corrected before delivery: numbered display equations now render their mathematical body and number separately, and CJK line wrapping safely handles inline formula images. The latest outputs were rendered again after these corrections. No blank placeholder is used in place of a formula.

[tools/pdf-build-report.json](tools/pdf-build-report.json) records each output's page count and SHA-256; [the QA receipt](tools/pdf-qa-report.json) records the final 41-page review. The regeneration and QA commands are documented in the [main README](README.md). Intermediate PNGs and formula caches were removed after inspection; they can be regenerated and are not release artifacts.

## Lean source verification

The package contains 225 Lean source modules and describes 12 additional pinned external BMS modules. `python lean/build.py --check-only` verifies the complete 237-module import closure and the bundled source hashes without downloading anything. The external BMS bytes are additionally hash-checked when their source checkout is supplied for compilation.

A fresh sequential rebuild of **all 237 proof-source modules passed**, with **554 axiom reports**. The [public verification receipt](lean/VERIFICATION.json) records the result; the [Lean instructions](lean/README.md) link the five final theorem/axiom logs. Release-only removal of unused earlier-notation declarations and the final comment updates were included in the checked source snapshot.

Only existing Lean and pinned Mathlib/auxiliary-package artifacts were reused. The Y, external BMS, and local notation proof modules were compiled from their checked sources, not loaded from the old research project's proof caches. This is not a fresh network bootstrap or a rebuild of all Mathlib dependencies. The Lake configuration was also loaded and typechecked by Lake in offline mode with local dependency overrides. Generated build artifacts were removed after the public receipt and final logs were exported.

The accepted reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. Resource and build details are in [lean/README.md](lean/README.md). Dependency bootstrapping is distinct from fresh recompilation of this project's proof-source closure.

## Scope that remains explicit

The joint paper argues in `KP_ω + there exists an uncountable ordinal`, with full set induction; the ordinary Lean proof is not an object-language derivation in that system. The finite geometric interfaces used in the paper are linked to their concrete verified source implementations.

The Y theorem is for the fixed upstream inherited-ancestry definition. Full legal-domain equivalence with Naruyoko's original JavaScript remains outside this package's claims. No optimal axiom strength, proof-theoretic ordinal comparison, or relative order-type inequality between the four systems is established by this packaging task.

Run `python tools/check_release.py` to check language pairing, relative entry links, the eight PDF/source pairs, NER snapshot hashes, private-path exclusions, and the Lean source closure.
