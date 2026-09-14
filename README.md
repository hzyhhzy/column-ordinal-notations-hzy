# Column Ordinal Notations - HZY · [中文版](README.zh-CN.md)

At 20:00 on September 11, @Phyrion published a [well-ordering proof for the Y-sequence system](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). Shortly afterwards, @test_alpha0 reduced the required axiomatic foundation to $KP_\omega+\text{there exists an uncountable ordinal}$. This repository collects RPD, LRD, Ω-LRD3, ARD, and IPD, notation systems devised by GPT6-astra after studying those proofs, together with their well-ordering proofs. RPD is expected to be at least as strong as Y while admitting a much shorter definition; this strength comparison has not been proved. LRD and Ω-LRD3 are further extensions of that construction. ARD makes row labels into references to earlier columns, so the row coordinate itself moves during expansion. IPD uses finite-level iterated tree profiles and relocates references even inside nested heads. All five admit paper well-ordering proofs in the same axiomatic system. Their order-type relationships with omega-Y and other familiar notation systems are currently unknown.

Definitions, executable fundamental sequences, and well-ordering proofs for column-diagram ordinal notations. This source snapshot was prepared on **2026-09-14** for [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). The suffix `hzy` refers to the repository owner's name.

The new notation implementations are **RPD, LRD, Ω-LRD3, ARD and IPD**. The proof collection covers **Y, RPD, LRD, Ω-LRD3, ARD and IPD**. Other Ω-LRD variants and historical experiments are deliberately excluded.

## Definitions and expanders

Each definition is available in English and Chinese, as Markdown and PDF: **20 definition artifacts** in total. English Markdown is the default; the title of every English document links to its Chinese counterpart.

| Notation | English definition | Chinese definition | NER expander | Python expander |
| --- | --- | --- | --- | --- |
| RPD | [Markdown](notations/RPD/definition.md) · [PDF](notations/RPD/definition.pdf) | [Markdown](notations/RPD/definition.zh-CN.md) · [PDF](notations/RPD/definition.zh-CN.pdf) | [JavaScript](notations/RPD/RPD-mountain.ne-rewritten.js) | [rpd.py](notations/RPD/rpd.py) |
| LRD | [Markdown](notations/LRD/definition.md) · [PDF](notations/LRD/definition.pdf) | [Markdown](notations/LRD/definition.zh-CN.md) · [PDF](notations/LRD/definition.zh-CN.pdf) | [JavaScript](notations/LRD/LRD.ne-rewritten.js) | [lrd.py](notations/LRD/lrd.py) |
| Ω-LRD3 | [Markdown](notations/Omega-LRD3/definition.md) · [PDF](notations/Omega-LRD3/definition.pdf) | [Markdown](notations/Omega-LRD3/definition.zh-CN.md) · [PDF](notations/Omega-LRD3/definition.zh-CN.pdf) | [JavaScript](notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js) | [omega_lrd3.py](notations/Omega-LRD3/omega_lrd3.py) |
| ARD | [Markdown](notations/ARD/definition.md) · [PDF](notations/ARD/definition.pdf) | [Markdown](notations/ARD/definition.zh-CN.md) · [PDF](notations/ARD/definition.zh-CN.pdf) | [JavaScript](notations/ARD/ARD-arcs.ne-rewritten.js) | [ard.py](notations/ARD/ard.py) |
| IPD | [Markdown](notations/IPD/definition.md) · [PDF](notations/IPD/definition.pdf) | [Markdown](notations/IPD/definition.zh-CN.md) · [PDF](notations/IPD/definition.zh-CN.pdf) | [JavaScript](notations/IPD/IPD.ne-rewritten.js) | [ipd.py](notations/IPD/ipd.py) |

For the browser version, load the complete JavaScript file into the custom-notation facility of [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Each file is an independent registration script; no build step is needed. Existing display modes and resource guards are preserved. The scripts also retain their original Chinese help text, including historical proof-status notes; the papers and validation record in this package state the current proof scope.

RPD and ARD also offer `邻接表（文字）` (text adjacency) and `邻接表（图）` (graphical adjacency) in the equivalent-display menu. The text uses one `[]` per column, semicolons for layers and commas for parent positions, retaining internal blanks. In HTML or the native diagram popup, each active layer is a compact upper-triangular table: shaded whole diagonal cells carry both row and column indices, off-diagonal entries carry maximum roots, and the exact count sequence appears once above all tables. Resource limits are reported explicitly, without approximate counts or partial tables.

The Python files use only the Python standard library. They implement the mathematical expansion core, not NER's interface or display caches. Read the command-line examples in the corresponding definition. Large expansions can still be expensive: a valid mathematical definition is not a promise of cheap evaluation.

## Well-ordering proofs: six systems

The original joint paper covers Y, RPD, LRD and Ω-LRD3. A separate complete ARD paper gives the dynamic-row extension. The IPD paper adds iterated tree profiles, including the direct KP tree-rank construction as Appendix A. All three papers work in:

$$
KP_\omega+\text{there exists an uncountable ordinal}.
$$

Here KP includes full set induction. The paper does not add a power-set axiom, full separation/collection, a choice axiom, a reflection axiom, or a large-cardinal axiom.

- **Paper:** [English Markdown](proofs/paper/well-ordering.md) · [English PDF](proofs/paper/well-ordering.pdf) · [Chinese Markdown](proofs/paper/well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/well-ordering.zh-CN.pdf).
- **ARD paper:** [English Markdown](proofs/paper/ard-well-ordering.md) · [English PDF](proofs/paper/ard-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard-well-ordering.zh-CN.pdf).
- **IPD paper:** [English Markdown](proofs/paper/ipd-well-ordering.md) · [English PDF](proofs/paper/ipd-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ipd-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ipd-well-ordering.zh-CN.pdf).
- **IPD correspondence audit:** [English](proofs/paper/ipd-fidelity.md) · [Chinese](proofs/paper/ipd-fidelity.zh-CN.md).
- **Lean:** [Build instructions and theorem index](lean/README.md) · [Chinese instructions](lean/README.zh-CN.md).
- **Joint Lean entry point:** [SixNotationFinalAudit.lean](lean/src/SixNotationFinalAudit.lean).

The Lean project formalizes the ordinary mathematical well-ordering theorems. **It does not encode a derivation in the weak object theory above.** The paper's axiom ledger and the Lean kernel checks are distinct results.

Y means the fixed upstream inherited-ancestry definition, pinned to commit `1689b21131b488ec2ba2515bd630360371a2389d`. A full equivalence proof between that definition and the original Naruyoko JavaScript on every legal input is not claimed here. No comparison of the six order types, optimal axiom-strength claim, or proof-theoretic ordinal comparison is included.

## Checks and PDF regeneration

Run the bounded expander tests from this directory:

```sh
python tests/test_python.py
python tests/test_ard.py
python tests/test_ipd.py
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
```

Follow [the Lean instructions](lean/README.md) for pinned dependencies and the sequential, resource-bounded build. Neither PDF generation nor Node.js is needed for Lean compilation.

To regenerate the sixteen publication PDFs, install Pandoc, Node.js, the document-tool dependencies, and suitable local fonts:

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
proofs/paper/                    Joint, ARD and IPD proofs; bilingual correspondence audit
lean/                           Source closure, dependency pins, bounded build
tests/                          Bounded expander regression tests
tools/                          Reproducible PDF generation and QA
```

## Before publishing

This project's own public license has **not** been selected. Included third-party material keeps its stated license; that does not automatically license the new code or papers. The BMS dependency is fetched externally because no license was found in its pinned source tree. See [the detailed notes](SOURCES.md). No private source manuscript or machine-specific research cache is included.
