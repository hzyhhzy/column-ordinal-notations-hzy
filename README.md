# Column Ordinal Notations - HZY · [中文版](README.zh-CN.md)

At 20:00 on September 11, @Phyrion published a [well-ordering proof for the Y-sequence system](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). Shortly afterwards, @test_alpha0 reduced the required axiomatic foundation to $KP_\omega+\text{there exists an uncountable ordinal}$. This repository collects RPD, LRD, Ω-LRD3, ARD, IPD, and ARD2, notation systems devised by GPT6-astra after studying those proofs, together with their well-ordering proofs. RPD admits a much shorter definition than Y; the paper comparison chain below proves it is at least as strong as the fixed 1Y definition. LRD and Ω-LRD3 are further extensions of that construction. ARD makes row labels into references to earlier columns, so the row coordinate itself moves during expansion. IPD uses finite-level iterated tree profiles and relocates references even inside nested heads. ARD2 returns to three natural-number coordinates, allowing both row and root SELF references and full-context root packages. All six admit paper well-ordering proofs in the same axiomatic system. Whole-system comparisons with omega-Y remain open; the specific known comparisons and common initial segments are recorded below.

Definitions, executable fundamental sequences, and proof/status documents for column notations, including explicitly marked pseudo-orders. This source snapshot was updated on **2026-10-06** for [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy). The suffix `hzy` refers to the repository owner's name.

The notation implementations are **SRPD, RPD, LRD, Ω-LRD3, ARD, IPD, ARD2, SPD, CWY, CWY2, Ω-CWY, ACD, CSD, ICP, FMP, CTN and DQDN**, with the candidate/failed/pseudo-order distinctions below. The Lean proof collection still covers only **Y, RPD, LRD, Ω-LRD3, ARD, IPD and ARD2**. ARD-legacy and ARD2-legacy are retained as explicit previous editions; other Ω-LRD variants are excluded. External e0MN implementations are credited separately, not counted as inventions of this project.

## DQDN and its collected results (2026-10-06)

[**DQDN — Demand Query Diagram Notation**](notations/DQDN/README.md) is now packaged with its unchanged four-view [NER expander](notations/DQDN/DQDN.ne-rewritten.js), a self-contained Python dependency set and validated [public frontend](notations/DQDN/standard.py), bilingual definitions and a [paper well-ordering argument](proofs/paper/dqdn-well-ordering.md). This is the common TOP-standard domain, not arbitrary untyped graphs. The old weak-KP upper bounds are not asserted for it, and no DQDN Lean project is added.

The [results and proof index](research/dqdn/README.md) collects the three-view equality tables, ζ₀/Γ₀/BHO carrier bounds, the BO convention, the global ≥PTO(Zω) argument and the paper chain $\lim(\mathrm{BMS})\le\mathrm{PTO}(Z_2)\le|\mathrm{TOP}[2]|$, including the strict four-row BMS bound. **Paper arguments, finite replay and open claims are distinguished.** Neither TOP[2]=PTO(Z₂) nor lim(DQDN)=PTO(Zω) is proved here. Full Chinese derivations are preserved with English companions; the long location manuscript has an explicitly condensed English reading edition.

TOP[1] has the paper value ε₀, while TOP[2] has count word `1,2,1,2`. The default NER list remains six small entries; the 880-column ω^ω example is not restored to it. [Validation](research/dqdn/validation.md) and [provenance](notations/DQDN/provenance.json) record the migration and bounded tests. Other notations, PDFs and Lean projects are unchanged.

## CTN: a computable pseudo-order with a CK initial segment (2026-10-01)

[**CTN — Comprehension Table Notation**](notations/CTN/definition.md) is the linear-limit system previously called **CTN2** in research files. It is now named CTN throughout this package; the original CTN frontend is retired and not included. The mathematical rules of the former CTN2 are unchanged.

Its actual columns are just 1 and 2, compared lexicographically. Expansion deletes or replaces only the last column, A[0] deletes it, and A[n] is a full prefix of A[n+1]. Ending in 1 is exactly being a successor; non-successor fundamental sequences grow by exactly one column per index after their first term. `12=ω`.

**The whole system is deliberately ill-founded.** The [bilingual paper argument](proofs/paper/ctn-well-founded-part.md) gives $\operatorname{otp}(\mathrm{WF}(\mathrm{CTN}))=\omega_1^{CK}$, not whole-system well-ordering or PTO(Z₂). The top `2` is not CK or a genuine ordinal. The package includes a six-view [NER expander](notations/CTN/CTN.ne-rewritten.js), [Python frontend](notations/CTN/ctn.py), separate finite-table checker, bilingual definitions and proof, and [small-ordinal locations](notations/CTN/small-ordinals.md). The ω^ω certificate is stored sparsely with its generator, not as a 69-million-column string. ε₀ remains unlocated. There is no CTN Lean project, new PDF, or change to other notations.

## SRPD: a common initial segment and TBMS comparisons (2026-09-28)

[**SRPD**](notations/SRPD/definition.md) is now packaged independently: each column is just a nonincreasing parent list, with an implicit first root. It includes a [NER expander](notations/SRPD/SRPD.ne-rewritten.js), [Python kernel](notations/SRPD/srpd.py), bilingual rules, and a [common-segment / well-ordering transfer argument](notations/SRPD/correspondence.md). NER retains parent-list, count-sequence and round-trip-checked BMS-style height-list views. The existing expansion rule is unchanged.

**SRPD independently presents a common initial segment of RPD, ARD, ARD2 and IPD.** Precisely, the order type strictly below SRPD's initial `[0]` agrees with the following standard initial segments:

| System | Endpoint (strictly below it) |
| --- | --- |
| RPD | `1,2` |
| ARD | `1,1,3` |
| ARD2 | `1,1,3` |
| IPD | `1,2` |
| Ordinary e0MN (@test_alpha0) | `1,3`, namely M13 |

This identifies initial-segment order types; **it does not identify SRPD with the whole RPD system**. The correspondence handles the raw projection's finite bottom, implicit root and one-index shift at the top; raw strings and all expansion indices must not be equated without those qualifications. Well-ordering transfers from the RPD segment under the existing paper's weak-KP upper bound. **No new SRPD Lean theorem is added**, and the seven existing systems' proofs are unchanged.

The [**bilingual SRPD vs TBMS summary**](research/srpd-tbms/README.md) retains the final routes: current carriers for whole ordinary TBMS and the tighter special bound for `TBMS ()(1^ε₀)`. The existing paper descent simulation puts the whole TBMS limit strictly below SRPD `1,2,4,8,4,2`, and further below a fixed descendant of its first fundamental-sequence term. This is not a comparison inferred from count growth. The latest `…6,7,9` remains an open candidate. Paper arguments, finite checks and unproved claims are separated; neither a Lean comparison nor a canonical index-preserving converter is claimed.

For the **complete proof process and the construction of the simulation**, start with the [proof archive guide](research/srpd-tbms/archive/README.md): 25 required proof/lemma manuscripts, their simulators/runtime dependencies and 2 route-specific verification records (73 imported items) are collected under `research/srpd-tbms/archive/`. Bilingual reading routes, paper-to-code references and portable replay commands keep this material discoverable without cluttering the root.

## FMP: full finite-map completion (2026-09-23)

[**FMP (Finite Map Patterns)**](notations/FMP/definition.md) is now included with its original Python kernel, standalone [NER script](notations/FMP/FMP.ne-rewritten.js), bilingual definitions and PDFs, bounded tests, and a [bilingual paper well-ordering manuscript](proofs/paper/fmp-well-ordering.md). The index means **copy $n$ times**, then delete the controller self-copy and fully complete the new region. Unavailable copied maps become empty without deleting their points. Five display modes, including exact count prefixes and the triangular adjacency table, are retained.

The manuscript proves standard-domain well-ordering under **ZFC + I3**, using bounded certificates, full-completion closure and the minimum-bad-cap argument. It is author-audited paper work, **not an independently refereed or Lean-certified result**. FMP has no Lean project or verification receipt and is not included in the weak-KP collection below. No exact FMP/DMP equivalence or BMS-limit equality is claimed by this addition. DMP's deferred completion and the output-length reindexing are not substituted for original FMP.

The accompanying [BMS lower-bound paper](proofs/paper/bms-le-fmp-12242444.md) proves **$\lim(\mathrm{BMS})\le\mathrm{FMP}(1,2,2,4,2,4,4,4)$**, via a whole-standard-domain order embedding below the eight-column expression. [English PDF](proofs/paper/bms-le-fmp-12242444.pdf) · [中文文稿](proofs/paper/bms-le-fmp-12242444.zh-CN.md) · [中文 PDF](proofs/paper/bms-le-fmp-12242444.zh-CN.pdf). This uses the original copy-indexed rule; equality, strictness and minimality remain unproved. The comparison is paper-level, not Lean-certified.

## Comparison archive and additional implementations (2026-09-20)

The new [bilingual comparison catalogue](research/order-comparisons/README.md) links the archived proof manuscripts: whole-system RPD/ARD/ARD2/wY bounds in ordinary e0MN, precise low-segment correspondences, the wY→RWD and BMS lower bounds, and the **conditional** BMS→IBLP `initial[0][1]` argument. These are paper comparisons, not new Lean theorems. Target well-ordering and stronger unproved claims are explicitly distinguished.

- **ACD** and **CSD** now have NER, Python and bilingual Markdown definitions. Global well-ordering remains open; no actual standard CSD infinite expansion chain was found in the reviewed records. That is not a proof of its nonexistence.
- **ICP** is preserved with NER, Python and bilingual rules **as a known non-well-ordered candidate**. Its standard infinite-chain manuscript and bounded check are included; its proved low-segment comparisons remain separate.
- [**Ordinary e0MN and strong e0MN**](external/README.md) were **invented by @test_alpha0**, not this project. Only the selected fast-counting NER editions are bundled; no new mathematical definition or Python port is supplied. Attribution and unresolved redistribution-license status are documented.

This addition does not change existing expansion rules, add a Lean project, or include PPS4S. The new definitions are Markdown-only; existing publication PDFs are retained.

**SPD (Slot Profile Diagrams)** adds four-integer relations whose heads and arguments are read recursively from earlier columns; the input contains no separate tree field. It includes bilingual definitions, a paper well-ordering manuscript, Python and NER implementations, and bounded regression tests. **SPD has no Lean proof yet.** Its order-type relationships with ARD, ARD2, wY and the whole IPD system remain unknown; its local-profile constructions are not a proof of those comparisons.

## ARD2 skyline revision (2026-09-17)

Default **ARD2 now uses skyline compression**: retain the greatest `(row, root)` at each parent, remove dominated entries, and replace a whole lower-row package with one predecessor. Both SELF coordinates and the seam-child borrow ceiling remain. The standard order type, indexed fundamental sequences and counts are unchanged. The [exact isomorphism](proofs/paper/ard2-well-ordering.md) is a paper result; the new rule has its own [Lean well-ordering project](lean/ARD2/README.md).

The previous NER, Python, bilingual definitions, paper and Lean sources are preserved as [ARD2-legacy](notations/ARD2-legacy/definition.md). Distinct NER IDs allow simultaneous import; the default is still named **ARD2**, retaining five displays and the existing budgets. `ARD ≤ ARD2(1,3)` transfers through the target isomorphism. No new whole-system wY/CWY2 comparison is asserted.

## CWY family (2026-09-17)

Added **CWY, CWY2 and Ω-CWY**, each with a standalone NER file and bilingual Markdown/PDF rules.

- **CWY:** the NER artifact is original wY plus the stretched compact-list view, not the independent CWY expansion kernel. The included Python core and bound wrapper implement the mathematical root-stretched version, whose existing paper argument gives an internal bound B above an isomorphic wY copy. The pure-seed indices differ from the NER adapter; the definition explains this explicitly.
- **CWY2:** the current marker-free direct-column kernel. The [full equivalence paper](proofs/paper/cwy2-equivalence.md) ([PDF](proofs/paper/cwy2-equivalence.pdf)) gives indexed expansion commutation and an order isomorphism with wY on corresponding standard domains, relative to the cited finite lemmas of the supplied wY manuscript. Well-ordering transfers from that manuscript in its weak-KP framework. This is a paper result, **not Lean-certified**.
- **Ω-CWY:** the self-indexed candidate with D[b+1] for limit labels, nesting-depth top, and original/count/mountain views. Its whole-domain well-ordering, cofinality and wY comparison remain **unproved**. The definition includes existing finite structural and Cantor-fragment arguments only.

None of these three adds a Lean project or enlarges the existing seven-system theorem. The private wY source manuscript is not redistributed. The two older CWY-family JS artifacts include upstream NER-derived code; see [source and licensing cautions](SOURCES.md) before public redistribution.

## ARD skyline revision (2026-09-16)

Default **ARD now uses simplified skyline rules**: triple column lists remain, but dominated records disappear and one predecessor replaces the full lower-row package. Standard order type, indexed fundamental sequences and counts are preserved. The complete previous NER, Python, definitions, paper and Lean project remain under [ARD-legacy](notations/ARD-legacy/definition.md).

The paper comparison result is

$$
\boxed{\mathrm{ARD}(1,2)\ge\mathrm{RPD}\ge 1Y.}
$$

Here `ARD(1,2)` denotes `[][(0,0,0)]`, not the whole ARD limit. The [fixed-bound embedding proof](proofs/paper/rpd-le-ard-a2.md) embeds every finite standard RPD term strictly below it, so the whole ARD order type is strictly greater than RPD. **The comparisons and full legacy isomorphism are paper results; the new ARD's own well-ordering has a separate Lean theorem.** 1Y denotes the pinned upstream definition here, not a new equivalence claim for arbitrary raw JS inputs.

The new [embedding below the fixed ARD2 term (1,3)](proofs/paper/ard-le-ard2-13.md) ([PDF](proofs/paper/ard-le-ard2-13.pdf)) uses `ARD2(1,3)=[][(0,0,1)]=A₂[1][1]`. For finite standard domains it gives

$$\alpha_{1Y}\le\alpha_{\mathrm{RPD}}<\alpha_{\mathrm{ARD}}
\le|\mathrm{ARD2}(1,3)|<\alpha_{\mathrm{ARD2}}.$$

This too is a **paper comparison, not yet Lean-formalized**. It claims neither an initial image, count preservation, indexed FS commutation, nor equality with that fixed term. Whole-domain comparisons with wY/CWY2 remain unresolved.

## Definitions and expanders

Definitions are available in English and Chinese. Thirteen existing editions retain **52 Markdown/PDF definition artifacts** (including FMP); ACD, CSD, ICP, SRPD, CTN and DQDN have twelve further Markdown definitions without new PDFs. English Markdown is the default, with a title link to Chinese.

| Notation | English definition | Chinese definition | NER expander | Python expander |
| --- | --- | --- | --- | --- |
| SRPD — common initial segment | [Markdown](notations/SRPD/definition.md) | [Markdown](notations/SRPD/definition.zh-CN.md) | [JavaScript](notations/SRPD/SRPD.ne-rewritten.js) | [srpd.py](notations/SRPD/srpd.py) |
| RPD | [Markdown](notations/RPD/definition.md) · [PDF](notations/RPD/definition.pdf) | [Markdown](notations/RPD/definition.zh-CN.md) · [PDF](notations/RPD/definition.zh-CN.pdf) | [JavaScript](notations/RPD/RPD-mountain.ne-rewritten.js) | [rpd.py](notations/RPD/rpd.py) |
| LRD | [Markdown](notations/LRD/definition.md) · [PDF](notations/LRD/definition.pdf) | [Markdown](notations/LRD/definition.zh-CN.md) · [PDF](notations/LRD/definition.zh-CN.pdf) | [JavaScript](notations/LRD/LRD.ne-rewritten.js) | [lrd.py](notations/LRD/lrd.py) |
| Ω-LRD3 | [Markdown](notations/Omega-LRD3/definition.md) · [PDF](notations/Omega-LRD3/definition.pdf) | [Markdown](notations/Omega-LRD3/definition.zh-CN.md) · [PDF](notations/Omega-LRD3/definition.zh-CN.pdf) | [JavaScript](notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js) | [omega_lrd3.py](notations/Omega-LRD3/omega_lrd3.py) |
| ARD | [Markdown](notations/ARD/definition.md) · [PDF](notations/ARD/definition.pdf) | [Markdown](notations/ARD/definition.zh-CN.md) · [PDF](notations/ARD/definition.zh-CN.pdf) | [JavaScript](notations/ARD/ARD.ne-rewritten.js) | [ard.py](notations/ARD/ard.py) |
| ARD-legacy | [Markdown](notations/ARD-legacy/definition.md) · [PDF](notations/ARD-legacy/definition.pdf) | [Markdown](notations/ARD-legacy/definition.zh-CN.md) · [PDF](notations/ARD-legacy/definition.zh-CN.pdf) | [JavaScript](notations/ARD-legacy/ARD-arcs.ne-rewritten.js) | [ard.py](notations/ARD-legacy/ard.py) |
| IPD | [Markdown](notations/IPD/definition.md) · [PDF](notations/IPD/definition.pdf) | [Markdown](notations/IPD/definition.zh-CN.md) · [PDF](notations/IPD/definition.zh-CN.pdf) | [JavaScript](notations/IPD/IPD.ne-rewritten.js) | [ipd.py](notations/IPD/ipd.py) |
| ARD2 | [Markdown](notations/ARD2/definition.md) · [PDF](notations/ARD2/definition.pdf) | [Markdown](notations/ARD2/definition.zh-CN.md) · [PDF](notations/ARD2/definition.zh-CN.pdf) | [JavaScript](notations/ARD2/ARD2.ne-rewritten.js) | [ard2.py](notations/ARD2/ard2.py) |
| ARD2-legacy | [Markdown](notations/ARD2-legacy/definition.md) · [PDF](notations/ARD2-legacy/definition.pdf) | [Markdown](notations/ARD2-legacy/definition.zh-CN.md) · [PDF](notations/ARD2-legacy/definition.zh-CN.pdf) | [JavaScript](notations/ARD2-legacy/ARD2-legacy.ne-rewritten.js) | [ard2.py](notations/ARD2-legacy/ard2.py) |
| SPD | [Markdown](notations/SPD/definition.md) · [PDF](notations/SPD/definition.pdf) | [Markdown](notations/SPD/definition.zh-CN.md) · [PDF](notations/SPD/definition.zh-CN.pdf) | [JavaScript](notations/SPD/SPD.ne-rewritten.js) | [spd.py](notations/SPD/spd.py) |
| FMP | [Markdown](notations/FMP/definition.md) · [PDF](notations/FMP/definition.pdf) | [Markdown](notations/FMP/definition.zh-CN.md) · [PDF](notations/FMP/definition.zh-CN.pdf) | [JavaScript](notations/FMP/FMP.ne-rewritten.js) | [kernel](notations/FMP/fmp.py) · [counts and parser](notations/FMP/fmp_tools.py) |
| CWY | [Markdown](notations/CWY/definition.md) · [PDF](notations/CWY/definition.pdf) | [Markdown](notations/CWY/definition.zh-CN.md) · [PDF](notations/CWY/definition.zh-CN.pdf) | [wY adapter + CWY view](notations/CWY/wY-CWY.ne-rewritten.js) | [core](notations/CWY/compact_wy.py) · [bound wrapper](notations/CWY/compact_wy_bound.py) |
| CWY2 | [Markdown](notations/CWY2/definition.md) · [PDF](notations/CWY2/definition.pdf) | [Markdown](notations/CWY2/definition.zh-CN.md) · [PDF](notations/CWY2/definition.zh-CN.pdf) | [JavaScript](notations/CWY2/CWY2.ne-rewritten.js) | No Python; [readable JS core](notations/CWY2/cwy_direct.mjs) |
| Ω-CWY | [Markdown](notations/Omega-CWY/definition.md) · [PDF](notations/Omega-CWY/definition.pdf) | [Markdown](notations/Omega-CWY/definition.zh-CN.md) · [PDF](notations/Omega-CWY/definition.zh-CN.pdf) | [JavaScript](notations/Omega-CWY/Omega-CWY.ne-rewritten.js) | No Python; [readable JS core](notations/Omega-CWY/core.mjs) |
| ACD — open | [Markdown](notations/ACD/definition.md) | [Markdown](notations/ACD/definition.zh-CN.md) | [JavaScript](notations/ACD/ACD.ne-rewritten.js) | [acd.py](notations/ACD/acd.py) |
| CSD — open | [Markdown](notations/CSD/definition.md) | [Markdown](notations/CSD/definition.zh-CN.md) | [JavaScript](notations/CSD/CSD.ne-rewritten.js) | [csd.py](notations/CSD/csd.py) · [local clock](notations/CSD/local_clock.py) |
| ICP — not well-ordered | [Markdown](notations/ICP/definition.md) | [Markdown](notations/ICP/definition.zh-CN.md) | [JavaScript](notations/ICP/ICP.ne-rewritten.js) | [icp.py](notations/ICP/icp.py) |
| CTN — CK pseudo-order | [Markdown](notations/CTN/definition.md) | [Markdown](notations/CTN/definition.zh-CN.md) | [JavaScript](notations/CTN/CTN.ne-rewritten.js) | [ctn.py](notations/CTN/ctn.py) · [table checker](notations/CTN/ctn_table.py) |
| DQDN — paper well-ordering | [Markdown](notations/DQDN/definition.md) | [Markdown](notations/DQDN/definition.zh-CN.md) | [JavaScript](notations/DQDN/DQDN.ne-rewritten.js) | [public frontend](notations/DQDN/standard.py) · [typed generator](notations/DQDN/typed_builder.py) |

For the browser version, load the complete JavaScript file into the custom-notation facility of [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/). Each file is an independent registration script; no build step is needed. Existing display modes and resource guards are preserved. The scripts also retain their original Chinese help text, including historical proof-status notes; the papers and validation record in this package state the current proof scope.

An optional [RPD with Y lower-bound annotations](notations/RPD/y-lower-bound/README.md) adds `≥ Y【mountain】` to the display. Its separate subdirectory contains the standalone JS, algorithm documentation and paper-level comparison notes; the original RPD expander is unchanged, and these comparisons are not end-to-end Lean-certified.

RPD, ARD and ARD2 also offer `邻接表（文字）` (text adjacency) and `邻接表（图）` (graphical adjacency) in the equivalent-display menu. The text uses one `[]` per column, semicolons for layers and commas for parent positions, retaining internal blanks. In HTML or the native diagram popup, each active layer is a compact upper-triangular table: shaded whole diagonal cells carry both row and column indices, off-diagonal entries carry maximum roots, and the exact count sequence appears once above all tables. Resource limits are reported explicitly, without approximate counts or partial tables.

The Python files use only the Python standard library. They implement the mathematical expansion core, not NER's interface or display caches. Read the command-line examples in the corresponding definition. Large expansions can still be expensive: a valid mathematical definition is not a promise of cheap evaluation.

SPD provides list and exact count-sequence displays. Its NER input also accepts `S2`, `Top[2][1]`, full relation lists, and standard count words such as `C(1,3,16)`. The separate [Python count decoder](notations/SPD/spd_count_decode.py) reconstructs the unique standard expression and distinguishes invalid input from resource exhaustion. A structurally legal handwritten list is not automatically a standard notation.

## Well-ordering proofs and proof status

The original joint paper covers Y, RPD, LRD and Ω-LRD3. The ARD-legacy paper gives the dynamic-row extension; the new ARD paper proves its skyline simplification and direct semantic descent. The IPD paper adds iterated tree profiles, including the direct KP tree-rank construction as Appendix A. The ARD2-legacy paper gives the two-SELF extension and actual seam transport; the new ARD2 paper proves its exact skyline isomorphism and direct semantic descent. These well-ordering papers work in:

$$
KP_\omega+\text{there exists an uncountable ordinal}.
$$

Here KP includes full set induction. The paper does not add a power-set axiom, full separation/collection, a choice axiom, a reflection axiom, or a large-cardinal axiom.

- **Paper:** [English Markdown](proofs/paper/well-ordering.md) · [English PDF](proofs/paper/well-ordering.pdf) · [Chinese Markdown](proofs/paper/well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/well-ordering.zh-CN.pdf).
- **ARD paper:** [English Markdown](proofs/paper/ard-well-ordering.md) · [English PDF](proofs/paper/ard-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard-well-ordering.zh-CN.pdf).
- **ARD-legacy paper:** [English](proofs/paper/ard-legacy-well-ordering.md) · [Chinese](proofs/paper/ard-legacy-well-ordering.zh-CN.md).
- **ARD(1,2)≥RPD comparison:** [English](proofs/paper/rpd-le-ard-a2.md) · [Chinese](proofs/paper/rpd-le-ard-a2.zh-CN.md).
- **ARD2(1,3)≥ARD comparison:** [English Markdown](proofs/paper/ard-le-ard2-13.md) · [English PDF](proofs/paper/ard-le-ard2-13.pdf) · [Chinese Markdown](proofs/paper/ard-le-ard2-13.zh-CN.md) · [Chinese PDF](proofs/paper/ard-le-ard2-13.zh-CN.pdf).
- **IPD paper:** [English Markdown](proofs/paper/ipd-well-ordering.md) · [English PDF](proofs/paper/ipd-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ipd-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ipd-well-ordering.zh-CN.pdf).
- **ARD2 paper:** [English Markdown](proofs/paper/ard2-well-ordering.md) · [English PDF](proofs/paper/ard2-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard2-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard2-well-ordering.zh-CN.pdf).
- **ARD2-legacy paper:** [English Markdown](proofs/paper/ard2-legacy-well-ordering.md) · [English PDF](proofs/paper/ard2-legacy-well-ordering.pdf) · [Chinese Markdown](proofs/paper/ard2-legacy-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/ard2-legacy-well-ordering.zh-CN.pdf).
- **SPD paper manuscript (not Lean-formalized):** [English Markdown](proofs/paper/spd-well-ordering.md) · [English PDF](proofs/paper/spd-well-ordering.pdf) · [Chinese Markdown](proofs/paper/spd-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/spd-well-ordering.zh-CN.pdf).
- **CWY2/wY equivalence (paper):** [English Markdown](proofs/paper/cwy2-equivalence.md) · [English PDF](proofs/paper/cwy2-equivalence.pdf) · [Chinese Markdown](proofs/paper/cwy2-equivalence.zh-CN.md) · [Chinese PDF](proofs/paper/cwy2-equivalence.zh-CN.pdf). CWY representation/bound arguments are in its definition; Ω-CWY has no global well-ordering proof.
- **IPD correspondence audit:** [English](proofs/paper/ipd-fidelity.md) · [Chinese](proofs/paper/ipd-fidelity.zh-CN.md).
- **FMP paper (ZFC + I3; not Lean-formalized):** [English Markdown](proofs/paper/fmp-well-ordering.md) · [English PDF](proofs/paper/fmp-well-ordering.pdf) · [Chinese Markdown](proofs/paper/fmp-well-ordering.zh-CN.md) · [Chinese PDF](proofs/paper/fmp-well-ordering.zh-CN.pdf). This is a separate stronger axiom bound, not the weak-KP bound above.
- **Lean:** [Build instructions and theorem index](lean/README.md) · [Chinese instructions](lean/README.zh-CN.md).
- **Independent Lean projects:** [Y](lean/Y/README.md) · [RPD](lean/RPD/README.md) · [LRD](lean/LRD/README.md) · [Ω-LRD3](lean/Omega-LRD3/README.md) · [ARD](lean/ARD/README.md) · [IPD](lean/IPD/README.md) · [ARD2](lean/ARD2/README.md).
- **Optional aggregate entry:** [ARD2RevisionFinalAudit.lean](lean/src/ARD2RevisionFinalAudit.lean).

Each notation has independent build configuration, outputs and verification receipts, depending on its declared sources and the [shared foundation](lean/shared/README.md); new ARD and ARD2 explicitly reuse their respective preserved legacy semantic backends, and only Y additionally needs BMS. Adding a notation does not modify existing projects or force their proofs to rebuild.

Here “each notation” refers to the seven systems listed in the Lean index. SPD is an implementation-and-paper addition only: there is no `lean/SPD` project, verification receipt, or extension of the seven-system aggregate theorem. Its manuscript develops the finite-demand/new-parent route in the same weak set theory; it distinguishes well-founded expansion on legal raw diagrams from well-ordering of the designated standard column order.

The Lean project formalizes the ordinary mathematical well-ordering theorems. **It does not encode a derivation in the weak object theory above.** The paper's axiom ledger and the Lean kernel checks are distinct results.

Y means the fixed upstream inherited-ancestry definition, pinned to commit `1689b21131b488ec2ba2515bd630360371a2389d`. A full equivalence proof between that definition and the original Naruyoko JavaScript on every legal input is not claimed here. The Lean-certified collection includes no cross-notation order-type comparison, optimal axiom-strength claim, or proof-theoretic ordinal comparison; the displayed comparison chain is proved on paper. Separate research notes record exploratory comparison arguments and candidates.

## Exploratory order-type comparisons

The separate [research directory](research/README.md) contains derivations and comparison drafts, not additional certified theorems. Start with the [2026-09-20 bilingual result catalogue](research/order-comparisons/README.md). The earlier [IPD comparison overview (Chinese)](research/ordinal-comparisons-20260914/README.zh-CN.md) covers the paper-level Y≤RPD argument, proposed IPD upper bounds for RPD/Y/wY/ARD/TPD, and the subsequent ARD2–IPD investigation. The notes distinguish paper arguments, local lemmas, bounded checks, and unproved candidates; archiving them does not establish an end-to-end Lean comparison.

Other research archives retain their designated manuscripts and candidate data. The SRPD/TBMS package retains only proofs, runtime dependencies and checks actually used by the final routes, not the whole historical reference graph. Private source PDFs and unrelated research caches are excluded. Historical test reports and current formal-proof status must be read separately.

## Documents for AI readers

The [AI reading collection](ai-docs/README.md) contains bilingual onboarding, design, and handoff documents. Its first guide is **Designing Beautiful Fundamental-Sequence Ordinal Notations** ([English](ai-docs/fundamental-sequence-aesthetics.md) · [中文](ai-docs/fundamental-sequence-aesthetics.zh-CN.md)): column-based syntax, prefix-preserving expansion, exact count-sequence comparison, concise internal structure, and substantive strength improvements. These guides provide requirements and explanations, not additional Lean certificates or unqualified order-type comparisons.

## Checks and PDF regeneration

Run the bounded expander and build-verifier tests from this directory:

```sh
python tests/test_python.py
python -B tests/dqdn.py
python tests/test_ard.py
python tests/test_ard_legacy.py
node --max-old-space-size=512 tests/ard_skyline.cjs
python -B tests/rpd_ard_comparison.py
python -B tests/ard_ard2_comparison.py
python -B tests/ard_ard2_forest.py
python tests/test_ipd.py
python tests/test_ard2.py
python -B tests/test_ard2_legacy.py
python -B tests/test_spd.py
python -B tests/test_fmp.py
python -B tests/fmp_bms_comparison.py
node --max-old-space-size=512 tests/fmp_ner.cjs
python -B tests/fmp_fixtures.py | node --max-old-space-size=512 tests/fmp_cross_language.cjs
python -B tests/test_lean_verifier.py
node --max-old-space-size=256 tests/ard2_ner.cjs
node --max-old-space-size=256 tests/ard2_display.cjs
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
python -B tests/test_cwy.py
node --max-old-space-size=256 tests/cwy_family.mjs
python -B tests/imported_notations.py --fixtures | node --max-old-space-size=256 tests/imported_notations.cjs
python -B notations/ICP/check_infinite_chain.py
```

Follow [the Lean instructions](lean/README.md) for pinned dependencies and the sequential, resource-bounded build. Neither PDF generation nor Node.js is needed for Lean compilation.

If a restricted host disallows Node spawning Python, run the same cross-language CWY test as two bounded processes: `python -B tests/test_cwy.py --fixtures | node --max-old-space-size=256 tests/cwy_family.mjs --fixtures-stdin`. This does not skip the Python oracle.

To regenerate all 44 publication PDFs, install Pandoc, Node.js, the document-tool dependencies, and suitable local fonts:

```sh
python -m pip install -r tools/requirements.txt
npm --prefix tools install
python tools/render_pdfs.py
python tools/qa_pdfs.py
```

The renderer uses ReportLab with MathJax-rendered formulas. It never silently omits unsupported Markdown constructs. On Windows, it uses fonts from `C:/Windows/Fonts`; `--font-dir` or `ORDINAL_PDF_FONTS` selects another font directory. Fonts are not redistributed. The QA command additionally requires Poppler's `pdftoppm`; inspect its page images under the ignored `tmp/pdf-qa/` directory. Regenerating a PDF does not replace visual review.

See [validation and provenance](VALIDATION.md) for the checks performed on this snapshot and [source/license notes](SOURCES.md) before publication.

`python tools/check_release.py` checks the publication inventory, local links and existing Lean receipts. Publication documents are bilingual. The 21 earlier monolingual archives and the explicitly inventoried comparison manuscripts retain their original language as requested; heading, formula, link and private-path checks still apply. New documents do not receive an automatic directory-wide exemption.

## Directory map

```text
README.md / README.zh-CN.md       Main entry points
notations/
  DQDN/                          Typed-query columns, bilingual rules, four-view NER, Python
  RPD/                           Bilingual definitions, PDFs, JS, Python
  LRD/                           Bilingual definitions, PDFs, JS, Python
  Omega-LRD3/                     Bilingual definitions, PDFs, JS, Python
  ARD/                           Skyline definitions, PDFs, five-view JS, Python
  ARD-legacy/                    Preserved previous edition
  IPD/                           Bilingual definitions, PDFs, tree-view JS, Python
  ARD2/                          Bilingual definitions, PDFs, five-view JS, Python
  ARD2-legacy/                   preserved old definition, programs and papers
  SPD/                           Bilingual definitions, PDFs, list/count JS, Python, count decoder
  CWY/                           Bilingual rules/proof, PDFs, wY-view JS, Python core/bound
  CWY2/                          Bilingual rules, PDFs, standalone JS and direct core
  Omega-CWY/                     Bilingual candidate rules, PDFs, three-view JS and sources
  ACD/, CSD/, ICP/               Bilingual Markdown, JS/Python; open or failed candidates
external/                       @test_alpha0's e0MN/strong e0MN, fast-counting NER only
proofs/paper/                    Existing proofs, SPD manuscript, CWY2 equivalence and audits
research/                       Bilingual comparison catalogue, proof archives and older notes
ai-docs/                        Bilingual guides and handoff documents for AI readers
lean/                           Source closure, dependency pins, bounded build
tests/                          Bounded expander and verifier regression tests
tools/                          Reproducible PDF generation and QA
```

## Before publishing

This project's own public license has **not** been selected. Included third-party material keeps its stated license; that does not automatically license the new code or papers. The BMS dependency is fetched externally because no license was found in its pinned source tree. See [the detailed notes](SOURCES.md). No private source manuscript or machine-specific research cache is included.
