# Column Ordinal Notations - HZY · [中文版](README.zh-CN.md)

At 20:00 on September 11, @Phyrion published a [well-ordering proof for the Y-sequence system](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). Shortly afterwards, @test_alpha0 reduced the required axiomatic foundation to $KP_\omega+\text{there exists an uncountable ordinal}$. This repository collects RPD, LRD, Ω-LRD3, ARD, IPD, and ARD2, notation systems devised by GPT6-astra after studying those proofs, together with their well-ordering proofs. RPD is expected to be at least as strong as Y while admitting a much shorter definition; exploratory arguments for this comparison are kept in the research directory, not in the verified theorem collection. LRD and Ω-LRD3 are further extensions of that construction. ARD makes row labels into references to earlier columns, so the row coordinate itself moves during expansion. IPD uses finite-level iterated tree profiles and relocates references even inside nested heads. ARD2 returns to three natural-number coordinates, allowing both row and root SELF references and full-context root packages. All six admit paper well-ordering proofs in the same axiomatic system. Their order-type relationships with omega-Y and other familiar notation systems are currently unknown.

Definitions, executable fundamental sequences, and well-ordering proofs for column-diagram ordinal notations. This source snapshot was prepared on **2026-09-14** for [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). The suffix `hzy` refers to the repository owner's name.

The new notation implementations are **RPD, LRD, Ω-LRD3, ARD, IPD and ARD2**. The proof collection covers **Y, RPD, LRD, Ω-LRD3, ARD, IPD and ARD2**. Other Ω-LRD variants and historical experimental implementations are deliberately excluded.

## Definitions and expanders

Each definition is available in English and Chinese, as Markdown and PDF: **24 definition artifacts** in total. English Markdown is the default; the title of every English document links to its Chinese counterpart.

| Notation | English definition | Chinese definition | NER expander | Python expander |
| --- | --- | --- | --- | --- |
| RPD | [Markdown](notations/RPD/definition.md) · [PDF](notations/RPD/definition.pdf) | [Markdown](notations/RPD/definition.zh-CN.md) · [PDF](notations/RPD/definition.zh-CN.pdf) | [JavaScript](notations/RPD/RPD-mountain.ne-rewritten.js) | [rpd.py](notations/RPD/rpd.py) |
| LRD | [Markdown](notations/LRD/definition.md) · [PDF](notations/LRD/definition.pdf) | [Markdown](notations/LRD/definition.zh-CN.md) · [PDF](notations/LRD/definition.zh-CN.pdf) | [JavaScript](notations/LRD/LRD.ne-rewritten.js) | [lrd.py](notations/LRD/lrd.py) |
| Ω-LRD3 | [Markdown](notations/Omega-LRD3/definition.md) · [PDF](notations/Omega-LRD3/definition.pdf) | [Markdown](notations/Omega-LRD3/definition.zh-CN.md) · [PDF](notations/Omega-LRD3/definition.zh-CN.pdf) | [JavaScript](notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js) | [omega_lrd3.py](notations/Omega-LRD3/omega_lrd3.py) |
| ARD | [Markdown](notations/ARD/definition.md) · [PDF](notations/ARD/definition.pdf) | [Markdown](notations/ARD/definition.zh-CN.md) · [PDF](notations/ARD/definition.zh-CN.pdf) | [JavaScript](notations/ARD/ARD-arcs.ne-rewritten.js) | [ard.py](notations/ARD/ard.py) |
| IPD | [Markdown](notations/IPD/definition.md) · [PDF](notations/IPD/definition.pdf) | [Markdown](notations/IPD/definition.zh-CN.md) · [PDF](notations/IPD/definition.zh-CN.pdf) | [JavaScript](notations/IPD/IPD.ne-rewritten.js) | [ipd.py](notations/IPD/ipd.py) |
| ARD2 | [Markdown](notations/ARD2/definition.md) · [PDF](notations/ARD2/definition.pdf) | [Markdown](notations/ARD2/definition.zh-CN.md) · [PDF](notations/ARD2/definition.zh-CN.pdf) | [JavaScript](notations/ARD2/ARD2.ne-rewritten.js) | [ard2.py](notations/ARD2/ard2.py) |

For the browser version, load the complete JavaScript file into the custom-notation facility of [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Each file is an independent registration script; no build step is needed. Existing display modes and resource guards are preserved. The scripts also retain their original Chinese help text, including historical proof-status notes; the papers and validation record in this package state the current proof scope.

An optional [RPD with Y lower-bound annotations](notations/RPD/y-lower-bound/README.md) adds `≥ Y【mountain】` to the display. Its separate subdirectory contains the standalone JS, algorithm documentation and paper-level comparison notes; the original RPD expander is unchanged, and these comparisons are not end-to-end Lean-certified.

RPD, ARD and ARD2 also offer `邻接表（文字）` (text adjacency) and `邻接表（图）` (graphical adjacency) in the equivalent-display menu. The text uses one `[]` per column, semicolons for layers and commas for parent positions, retaining internal blanks. In HTML or the native diagram popup, each active layer is a compact upper-triangular table: shaded whole diagonal cells carry both row and column indices, off-diagonal entries carry maximum roots, and the exact count sequence appears once above all tables. Resource limits are reported explicitly, without approximate counts or partial tables.

The Python files use only the Python standard library. They implement the mathematical expansion core, not NER's interface or display caches. Read the command-line examples in the corresponding definition. Large expansions can still be expensive: a valid mathematical definition is not a promise of cheap evaluation.

## Well-ordering proofs: seven systems

The original joint paper covers Y, RPD, LRD and Ω-LRD3. A separate complete ARD paper gives the dynamic-row extension. The IPD paper adds iterated tree profiles, including the direct KP tree-rank construction as Appendix A. The ARD2 paper gives the two-SELF extension and its actual seam transport. All four papers work in:

$$
KP_\omega+\text{there exists an uncountable ordinal}.
$$

Here KP includes full set induction. The paper does not add a power-set axiom, full separation/collection, a choice axiom, a reflection axiom, or a large-cardinal axiom.

- **Paper:** [English Markdown](proofs/paper/well-ordering.md) · [English PDF](proofs/paper/well-ordering.pdf) · [Chinese Markdown](proofs/paper/well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/well-ordering.zh-CN.pdf).
- **ARD paper:** [English Markdown](proofs/paper/ard-well-ordering.md) · [English PDF](proofs/paper/ard-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard-well-ordering.zh-CN.pdf).
- **IPD paper:** [English Markdown](proofs/paper/ipd-well-ordering.md) · [English PDF](proofs/paper/ipd-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ipd-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ipd-well-ordering.zh-CN.pdf).
- **ARD2 paper:** [English Markdown](proofs/paper/ard2-well-ordering.md) · [English PDF](proofs/paper/ard2-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard2-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard2-well-ordering.zh-CN.pdf).
- **IPD correspondence audit:** [English](proofs/paper/ipd-fidelity.md) · [Chinese](proofs/paper/ipd-fidelity.zh-CN.md).
- **Lean:** [Build instructions and theorem index](lean/README.md) · [Chinese instructions](lean/README.zh-CN.md).
- **Independent Lean projects:** [Y](lean/Y/README.md) · [RPD](lean/RPD/README.md) · [LRD](lean/LRD/README.md) · [Ω-LRD3](lean/Omega-LRD3/README.md) · [ARD](lean/ARD/README.md) · [IPD](lean/IPD/README.md) · [ARD2](lean/ARD2/README.md).
- **Optional aggregate entry:** [SevenNotationFinalAudit.lean](lean/src/SevenNotationFinalAudit.lean).

Each notation has independent build configuration, outputs and verification receipts, depending only on itself and the [shared foundation](lean/shared/README.md); only Y additionally needs BMS. Adding a notation does not modify existing projects or force their proofs to rebuild.

The Lean project formalizes the ordinary mathematical well-ordering theorems. **It does not encode a derivation in the weak object theory above.** The paper's axiom ledger and the Lean kernel checks are distinct results.

Y means the fixed upstream inherited-ancestry definition, pinned to commit `1689b21131b488ec2ba2515bd630360371a2389d`. A full equivalence proof between that definition and the original Naruyoko JavaScript on every legal input is not claimed here. The verified proof collection includes no comparison of the seven order types, optimal axiom-strength claim, or proof-theoretic ordinal comparison. Separate research notes record exploratory comparison arguments and candidates.

## Exploratory order-type comparisons

The separate [research directory](research/README.md) contains derivations and comparison drafts, not additional certified theorems. The current [IPD comparison overview (Chinese)](research/ordinal-comparisons-20260914/README.zh-CN.md) covers the paper-level Y≤RPD argument, proposed IPD upper bounds for RPD/Y/wY/ARD/TPD, and the subsequent ARD2–IPD investigation. The notes distinguish paper arguments, local lemmas, bounded checks, and unproved candidates; archiving them does not establish an end-to-end Lean comparison.

Supporting manuscripts and candidate data are included. Experimental code and private source manuscripts are not bundled. Historical test reports and the current status of the formal proofs must be read separately.

## Checks and PDF regeneration

Run the bounded expander and build-verifier tests from this directory:

```sh
python tests/test_python.py
python tests/test_ard.py
python tests/test_ipd.py
python tests/test_ard2.py
python -B tests/test_lean_verifier.py
node --max-old-space-size=256 tests/ard2_ner.cjs
node --max-old-space-size=256 tests/ard2_display.cjs
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
```

Follow [the Lean instructions](lean/README.md) for pinned dependencies and the sequential, resource-bounded build. Neither PDF generation nor Node.js is needed for Lean compilation.

To regenerate the twenty publication PDFs, install Pandoc, Node.js, the document-tool dependencies, and suitable local fonts:

```sh
python -m pip install -r tools/requirements.txt
npm --prefix tools install
python tools/render_pdfs.py
python tools/qa_pdfs.py
```

The renderer uses ReportLab with MathJax-rendered formulas. It never silently omits unsupported Markdown constructs. On Windows, it uses fonts from `C:/Windows/Fonts`; `--font-dir` or `ORDINAL_PDF_FONTS` selects another font directory. Fonts are not redistributed. The QA command additionally requires Poppler's `pdftoppm`; inspect its page images under the ignored `tmp/pdf-qa/` directory. Regenerating a PDF does not replace visual review.

See [validation and provenance](VALIDATION.md) for the checks performed on this snapshot and [source/license notes](SOURCES.md) before publication.

## Directory map

```text
README.md / README.zh-CN.md       Main entry points
notations/
  RPD/                           Bilingual definitions, PDFs, JS, Python
  LRD/                           Bilingual definitions, PDFs, JS, Python
  Omega-LRD3/                     Bilingual definitions, PDFs, JS, Python
  ARD/                           Bilingual definitions, PDFs, arc-view JS, Python
  IPD/                           Bilingual definitions, PDFs, tree-view JS, Python
  ARD2/                          Bilingual definitions, PDFs, five-view JS, Python
proofs/paper/                    Joint, ARD, IPD and ARD2 proofs; bilingual correspondence audit
research/                       Comparison drafts, candidates and historical research notes
lean/                           Source closure, dependency pins, bounded build
tests/                          Bounded expander and verifier regression tests
tools/                          Reproducible PDF generation and QA
```

## Before publishing

This project's own public license has **not** been selected. Included third-party material keeps its stated license; that does not automatically license the new code or papers. The BMS dependency is fetched externally because no license was found in its pinned source tree. See [the detailed notes](SOURCES.md). No private source manuscript or machine-specific research cache is included.
