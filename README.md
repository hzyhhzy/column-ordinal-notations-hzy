# Column Ordinal Notations - HZY · [中文版](README.zh-CN.md)

At 20:00 on September 11, @Phyrion published a [well-ordering proof for the Y-sequence system](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). Shortly afterwards, @test_alpha0 reduced the required axiomatic foundation to $KP_\omega+\text{there exists an uncountable ordinal}$. This repository collects RPD, LRD, Ω-LRD3, ARD, IPD, and ARD2, notation systems devised by GPT6-astra after studying those proofs, together with their well-ordering proofs. RPD admits a much shorter definition than Y; the paper comparison chain below proves it is at least as strong as the fixed 1Y definition. LRD and Ω-LRD3 are further extensions of that construction. ARD makes row labels into references to earlier columns, so the row coordinate itself moves during expansion. IPD uses finite-level iterated tree profiles and relocates references even inside nested heads. ARD2 returns to three natural-number coordinates, allowing both row and root SELF references and full-context root packages. All six admit paper well-ordering proofs in the same axiomatic system. Their order-type relationships with omega-Y and other familiar notation systems are currently unknown.

Definitions, executable fundamental sequences, and well-ordering proofs for column-diagram ordinal notations. This source snapshot was prepared on **2026-09-16** for [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). The suffix `hzy` refers to the repository owner's name.

The new notation implementations are **RPD, LRD, Ω-LRD3, ARD, IPD, ARD2 and SPD**. The Lean proof collection covers **Y, RPD, LRD, Ω-LRD3, ARD, IPD and ARD2**. ARD-legacy is retained as an explicit previous edition; other Ω-LRD variants and historical experimental implementations are excluded.

**SPD (Slot Profile Diagrams)** adds four-integer relations whose heads and arguments are read recursively from earlier columns; the input contains no separate tree field. It includes bilingual definitions, a paper well-ordering manuscript, Python and NER implementations, and bounded regression tests. **SPD has no Lean proof yet.** Its order-type relationships with ARD, ARD2, wY and the whole IPD system remain unknown; its local-profile constructions are not a proof of those comparisons.

## ARD skyline revision (2026-09-16)

Default **ARD now uses simplified skyline rules**: triple column lists remain, but dominated records disappear and one predecessor replaces the full lower-row package. Standard order type, indexed fundamental sequences and counts are preserved. The complete previous NER, Python, definitions, paper and Lean project remain under [ARD-legacy](notations/ARD-legacy/definition.md).

The paper comparison result is

$$
\boxed{\mathrm{ARD}(1,2)\ge\mathrm{RPD}\ge 1Y.}
$$

Here `ARD(1,2)` denotes `[][(0,0,0)]`, not the whole ARD limit. The [fixed-bound embedding proof](proofs/paper/rpd-le-ard-a2.md) embeds every finite standard RPD term strictly below it, so the whole ARD order type is strictly greater than RPD. **The comparisons and full legacy isomorphism are paper results; the new ARD's own well-ordering has a separate Lean theorem.** 1Y denotes the pinned upstream definition here, not a new equivalence claim for arbitrary raw JS inputs.

## Definitions and expanders

Each definition is available in English and Chinese, as Markdown and PDF: **32 definition artifacts (including the preserved legacy edition)** in total. English Markdown is the default; the title of every English definition links to its Chinese counterpart.

| Notation | English definition | Chinese definition | NER expander | Python expander |
| --- | --- | --- | --- | --- |
| RPD | [Markdown](notations/RPD/definition.md) · [PDF](notations/RPD/definition.pdf) | [Markdown](notations/RPD/definition.zh-CN.md) · [PDF](notations/RPD/definition.zh-CN.pdf) | [JavaScript](notations/RPD/RPD-mountain.ne-rewritten.js) | [rpd.py](notations/RPD/rpd.py) |
| LRD | [Markdown](notations/LRD/definition.md) · [PDF](notations/LRD/definition.pdf) | [Markdown](notations/LRD/definition.zh-CN.md) · [PDF](notations/LRD/definition.zh-CN.pdf) | [JavaScript](notations/LRD/LRD.ne-rewritten.js) | [lrd.py](notations/LRD/lrd.py) |
| Ω-LRD3 | [Markdown](notations/Omega-LRD3/definition.md) · [PDF](notations/Omega-LRD3/definition.pdf) | [Markdown](notations/Omega-LRD3/definition.zh-CN.md) · [PDF](notations/Omega-LRD3/definition.zh-CN.pdf) | [JavaScript](notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js) | [omega_lrd3.py](notations/Omega-LRD3/omega_lrd3.py) |
| ARD | [Markdown](notations/ARD/definition.md) · [PDF](notations/ARD/definition.pdf) | [Markdown](notations/ARD/definition.zh-CN.md) · [PDF](notations/ARD/definition.zh-CN.pdf) | [JavaScript](notations/ARD/ARD.ne-rewritten.js) | [ard.py](notations/ARD/ard.py) |
| ARD-legacy | [Markdown](notations/ARD-legacy/definition.md) · [PDF](notations/ARD-legacy/definition.pdf) | [Markdown](notations/ARD-legacy/definition.zh-CN.md) · [PDF](notations/ARD-legacy/definition.zh-CN.pdf) | [JavaScript](notations/ARD-legacy/ARD-arcs.ne-rewritten.js) | [ard.py](notations/ARD-legacy/ard.py) |
| IPD | [Markdown](notations/IPD/definition.md) · [PDF](notations/IPD/definition.pdf) | [Markdown](notations/IPD/definition.zh-CN.md) · [PDF](notations/IPD/definition.zh-CN.pdf) | [JavaScript](notations/IPD/IPD.ne-rewritten.js) | [ipd.py](notations/IPD/ipd.py) |
| ARD2 | [Markdown](notations/ARD2/definition.md) · [PDF](notations/ARD2/definition.pdf) | [Markdown](notations/ARD2/definition.zh-CN.md) · [PDF](notations/ARD2/definition.zh-CN.pdf) | [JavaScript](notations/ARD2/ARD2.ne-rewritten.js) | [ard2.py](notations/ARD2/ard2.py) |
| SPD | [Markdown](notations/SPD/definition.md) · [PDF](notations/SPD/definition.pdf) | [Markdown](notations/SPD/definition.zh-CN.md) · [PDF](notations/SPD/definition.zh-CN.pdf) | [JavaScript](notations/SPD/SPD.ne-rewritten.js) | [spd.py](notations/SPD/spd.py) |

For the browser version, load the complete JavaScript file into the custom-notation facility of [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Each file is an independent registration script; no build step is needed. Existing display modes and resource guards are preserved. The scripts also retain their original Chinese help text, including historical proof-status notes; the papers and validation record in this package state the current proof scope.

An optional [RPD with Y lower-bound annotations](notations/RPD/y-lower-bound/README.md) adds `≥ Y【mountain】` to the display. Its separate subdirectory contains the standalone JS, algorithm documentation and paper-level comparison notes; the original RPD expander is unchanged, and these comparisons are not end-to-end Lean-certified.

RPD, ARD and ARD2 also offer `邻接表（文字）` (text adjacency) and `邻接表（图）` (graphical adjacency) in the equivalent-display menu. The text uses one `[]` per column, semicolons for layers and commas for parent positions, retaining internal blanks. In HTML or the native diagram popup, each active layer is a compact upper-triangular table: shaded whole diagonal cells carry both row and column indices, off-diagonal entries carry maximum roots, and the exact count sequence appears once above all tables. Resource limits are reported explicitly, without approximate counts or partial tables.

The Python files use only the Python standard library. They implement the mathematical expansion core, not NER's interface or display caches. Read the command-line examples in the corresponding definition. Large expansions can still be expensive: a valid mathematical definition is not a promise of cheap evaluation.

SPD provides list and exact count-sequence displays. Its NER input also accepts `S2`, `Top[2][1]`, full relation lists, and standard count words such as `C(1,3,16)`. The separate [Python count decoder](notations/SPD/spd_count_decode.py) reconstructs the unique standard expression and distinguishes invalid input from resource exhaustion. A structurally legal handwritten list is not automatically a standard notation.

## Well-ordering proofs and proof status

The original joint paper covers Y, RPD, LRD and Ω-LRD3. The ARD-legacy paper gives the dynamic-row extension; the new ARD paper proves its skyline simplification and direct semantic descent. The IPD paper adds iterated tree profiles, including the direct KP tree-rank construction as Appendix A. The ARD2 paper gives the two-SELF extension and its actual seam transport. These well-ordering papers work in:

$$
KP_\omega+\text{there exists an uncountable ordinal}.
$$

Here KP includes full set induction. The paper does not add a power-set axiom, full separation/collection, a choice axiom, a reflection axiom, or a large-cardinal axiom.

- **Paper:** [English Markdown](proofs/paper/well-ordering.md) · [English PDF](proofs/paper/well-ordering.pdf) · [Chinese Markdown](proofs/paper/well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/well-ordering.zh-CN.pdf).
- **ARD paper:** [English Markdown](proofs/paper/ard-well-ordering.md) · [English PDF](proofs/paper/ard-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard-well-ordering.zh-CN.pdf).
- **ARD-legacy paper:** [English](proofs/paper/ard-legacy-well-ordering.md) · [Chinese](proofs/paper/ard-legacy-well-ordering.zh-CN.md).
- **ARD(1,2)≥RPD comparison:** [English](proofs/paper/rpd-le-ard-a2.md) · [Chinese](proofs/paper/rpd-le-ard-a2.zh-CN.md).
- **IPD paper:** [English Markdown](proofs/paper/ipd-well-ordering.md) · [English PDF](proofs/paper/ipd-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ipd-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ipd-well-ordering.zh-CN.pdf).
- **ARD2 paper:** [English Markdown](proofs/paper/ard2-well-ordering.md) · [English PDF](proofs/paper/ard2-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard2-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard2-well-ordering.zh-CN.pdf).
- **SPD paper manuscript (not Lean-formalized):** [English Markdown](proofs/paper/spd-well-ordering.md) · [English PDF](proofs/paper/spd-well-ordering.pdf) · [Chinese Markdown](proofs/paper/spd-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/spd-well-ordering.zh-CN.pdf).
- **IPD correspondence audit:** [English](proofs/paper/ipd-fidelity.md) · [Chinese](proofs/paper/ipd-fidelity.zh-CN.md).
- **Lean:** [Build instructions and theorem index](lean/README.md) · [Chinese instructions](lean/README.zh-CN.md).
- **Independent Lean projects:** [Y](lean/Y/README.md) · [RPD](lean/RPD/README.md) · [LRD](lean/LRD/README.md) · [Ω-LRD3](lean/Omega-LRD3/README.md) · [ARD](lean/ARD/README.md) · [IPD](lean/IPD/README.md) · [ARD2](lean/ARD2/README.md).
- **Optional aggregate entry:** [ARDRevisionFinalAudit.lean](lean/src/ARDRevisionFinalAudit.lean).

Each notation has independent build configuration, outputs and verification receipts, depending on its declared sources and the [shared foundation](lean/shared/README.md); new ARD explicitly reuses the preserved ARD-legacy semantic backend, and only Y additionally needs BMS. Adding a notation does not modify existing projects or force their proofs to rebuild.

Here “each notation” refers to the seven systems listed in the Lean index. SPD is an implementation-and-paper addition only: there is no `lean/SPD` project, verification receipt, or extension of the seven-system aggregate theorem. Its manuscript develops the finite-demand/new-parent route in the same weak set theory; it distinguishes well-founded expansion on legal raw diagrams from well-ordering of the designated standard column order.

The Lean project formalizes the ordinary mathematical well-ordering theorems. **It does not encode a derivation in the weak object theory above.** The paper's axiom ledger and the Lean kernel checks are distinct results.

Y means the fixed upstream inherited-ancestry definition, pinned to commit `1689b21131b488ec2ba2515bd630360371a2389d`. A full equivalence proof between that definition and the original Naruyoko JavaScript on every legal input is not claimed here. The Lean-certified collection includes no cross-notation order-type comparison, optimal axiom-strength claim, or proof-theoretic ordinal comparison; the displayed comparison chain is proved on paper. Separate research notes record exploratory comparison arguments and candidates.

## Exploratory order-type comparisons

The separate [research directory](research/README.md) contains derivations and comparison drafts, not additional certified theorems. The current [IPD comparison overview (Chinese)](research/ordinal-comparisons-20260914/README.zh-CN.md) covers the paper-level Y≤RPD argument, proposed IPD upper bounds for RPD/Y/wY/ARD/TPD, and the subsequent ARD2–IPD investigation. The notes distinguish paper arguments, local lemmas, bounded checks, and unproved candidates; archiving them does not establish an end-to-end Lean comparison.

Supporting manuscripts and candidate data are included. Experimental code and private source manuscripts are not bundled. Historical test reports and the current status of the formal proofs must be read separately.

## Documents for AI readers

The [AI reading collection](ai-docs/README.md) contains bilingual onboarding, design, and handoff documents. Its first guide is **Designing Beautiful Fundamental-Sequence Ordinal Notations** ([English](ai-docs/fundamental-sequence-aesthetics.md) · [中文](ai-docs/fundamental-sequence-aesthetics.zh-CN.md)): column-based syntax, prefix-preserving expansion, exact count-sequence comparison, concise internal structure, and substantive strength improvements. These guides provide requirements and explanations, not additional Lean certificates or unqualified order-type comparisons.

## Checks and PDF regeneration

Run the bounded expander and build-verifier tests from this directory:

```sh
python tests/test_python.py
python tests/test_ard.py
python tests/test_ard_legacy.py
node --max-old-space-size=512 tests/ard_skyline.cjs
python -B tests/rpd_ard_comparison.py
python tests/test_ipd.py
python tests/test_ard2.py
python -B tests/test_spd.py
python -B tests/test_lean_verifier.py
node --max-old-space-size=256 tests/ard2_ner.cjs
node --max-old-space-size=256 tests/ard2_display.cjs
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
```

Follow [the Lean instructions](lean/README.md) for pinned dependencies and the sequential, resource-bounded build. Neither PDF generation nor Node.js is needed for Lean compilation.

To regenerate the thirty publication PDFs, install Pandoc, Node.js, the document-tool dependencies, and suitable local fonts:

```sh
python -m pip install -r tools/requirements.txt
npm --prefix tools install
python tools/render_pdfs.py
python tools/qa_pdfs.py
```

The renderer uses ReportLab with MathJax-rendered formulas. It never silently omits unsupported Markdown constructs. On Windows, it uses fonts from `C:/Windows/Fonts`; `--font-dir` or `ORDINAL_PDF_FONTS` selects another font directory. Fonts are not redistributed. The QA command additionally requires Poppler's `pdftoppm`; inspect its page images under the ignored `tmp/pdf-qa/` directory. Regenerating a PDF does not replace visual review.

See [validation and provenance](VALIDATION.md) for the checks performed on this snapshot and [source/license notes](SOURCES.md) before publication.

`python tools/check_release.py` checks the publication inventory, local links and existing Lean receipts. The bilingual requirement covers the publication documents; 21 explicitly listed pre-existing monolingual research archives retain their original language. They still receive heading, formula, link and private-path checks. New documents do not receive an automatic archive exemption.

## Directory map

```text
README.md / README.zh-CN.md       Main entry points
notations/
  RPD/                           Bilingual definitions, PDFs, JS, Python
  LRD/                           Bilingual definitions, PDFs, JS, Python
  Omega-LRD3/                     Bilingual definitions, PDFs, JS, Python
  ARD/                           Skyline definitions, PDFs, five-view JS, Python
  ARD-legacy/                    Preserved previous edition
  IPD/                           Bilingual definitions, PDFs, tree-view JS, Python
  ARD2/                          Bilingual definitions, PDFs, five-view JS, Python
  SPD/                           Bilingual definitions, PDFs, list/count JS, Python, count decoder
proofs/paper/                    Joint, ARD, IPD, ARD2 proofs and SPD manuscript; correspondence audit
research/                       Comparison drafts, candidates and historical research notes
ai-docs/                        Bilingual guides and handoff documents for AI readers
lean/                           Source closure, dependency pins, bounded build
tests/                          Bounded expander and verifier regression tests
tools/                          Reproducible PDF generation and QA
```

## Before publishing

This project's own public license has **not** been selected. Included third-party material keeps its stated license; that does not automatically license the new code or papers. The BMS dependency is fetched externally because no license was found in its pinned source tree. See [the detailed notes](SOURCES.md). No private source manuscript or machine-specific research cache is included.
