# Lower bounds for Laver-table q(5) · [中文](README.zh-CN.md)

This directory collects three existing paper-proof routes, their quantitative interfaces and supporting manuscripts. Here $q(5)$ is the first **table-order parameter** at which the first row of the ordinary binary Laver table has period 32; the table has $2^{q(5)}$ elements. The archived paper routes use **ZFC + I3**, in one fixed $\operatorname{Iter}(j)$. The separate Lean project below now certifies a conditional bound without I3.

## New Lean result (2026-11-06)

$$
q(5)\downarrow\ \Longrightarrow\ q(5)>F_{\Lambda+\omega+1}(3),\qquad
\Lambda=\lim(\mathrm{BMS}).
$$

The [independent Lean 4.33.1 project](lean/README.md) contains the [final theorem](lean/LaverLowerBounds/OriginalBMSBound.lean), exact numerical BM4/parent-coordinate expansion equivalence, a realized finite FGH evaluation, a portable build command, and [152-module verification receipt](lean/verification/VERIFICATION.json). Its only audited axioms are `propext`, `Classical.choice`, and `Quot.sound`; it assumes neither I3 nor global BMS well-ordering.

**Scope:** input `3`, ordinal level `Lambda+omega+1`, ordinary Lean foundations. This is not an object-language ZFC derivation, a proof that `q(5)` exists, or certification of the larger-input/tower/IBLP paper results below. The theorem is quantified over every family of finite tables satisfying the defining equations. Full conventions and boundaries are in the [project README](lean/README.md).

## Archived paper results

The main papers replace the old arbitrarily prescribed large input with the integer naturally produced by the original proof and derive the resulting numerical bounds.

| Route | Collected result | Natural input and proof |
|---|---|---|
| Finite-type BMS towers, realized by BLP operations | $q(5)>2^Y>Y\ge H_{C[7]}(M)$ and $q(5)>F_{C[6]}(M-1)+1$ | $M=\mathcal Q(1)$ from six actual typed operators; [paper](01-blp-tower.zh-CN.md) |
| Dynamic BMS feedback | $q(5)>F_{\Lambda+\omega+1}(K(g(g(z))))$ | Direct Qi-line input, finite-FGH input, and a stronger auxiliary-recursion input; [paper](02-bms-feedback.zh-CN.md) |
| Mark-preserving short modify/cut from an original IBLP initial value | $\delta(S_*)<q(5)$ and $\mu(S_*)\le\tau(S_*)<2^{q(5)}$ | $S_*=R[2^L][2^{2^L-1}]$, $L=C_{\rm line}$; [paper](03-iblp-modify.zh-CN.md) |

Here $\Lambda=\lim(\mathrm{BMS})$, $g=F_\Lambda$, $K=F_{\Lambda+\omega}$, $R=I[0][3][0]$, and $C=R[0][1]^8$. The last exponent means eight consecutive original operations.

The first route's exact descent-tree ranks satisfy $\alpha_1=\Lambda$, $\alpha_{n+1}=\Lambda\omega^{\alpha_n}$ and $\operatorname{rank}(C[n])=\alpha_n$. If one additionally uses $\omega^\Lambda=\Lambda$, these are a five-$\Lambda$ tower for FGH and a six-$\Lambda$ tower for Hardy. Fundamental sequences remain those of the specified original IBLP terms; a rank identification alone is not a numerical hierarchy comparison.

The second route admits direct long-line initialization. Its strongest inputs use the finite-parameter parent-packet bridge for pIBLP; whole-system pIBLP well-ordering is not assumed. The third retains the original legacy rules for two initialization steps, then counts **paper-guard** short modify with full frozen mark/native completion. Its total count is bounded by $2^{q(5)}$, while deletions are bounded directly by $q(5)$.

Read the [Chinese overview](README.zh-CN.md), [conventions](common/conventions.zh-CN.md), [dependency map](PROOF_DEPENDENCIES.zh-CN.md), and [manuscript index](proofs/README.md). The shared [fixed-index BMS theorem](common/bms-fixed-index.zh-CN.md) includes

$$
D(h)\ge e_{F_{B_r}(x)},\qquad
h\ge r+2+\lceil\log_2(x+2)\rceil,\qquad e_0=1,\ e_{n+1}=2^{e_n}.
$$

It assembles normalized parent-table covers, row/width exchange, the forest controller and exact FGH–Hardy compilation. The [natural-mark guide](common/natural-marks.zh-CN.md) indexes the local semantic inputs.

Supporting manuscripts retain their original Chinese or English exposition. They are reading editions: obsolete prescribed-input paragraphs may be omitted, with source line ranges and hashes in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json); the main papers supply the natural-input arguments. Historical drafts and withdrawn candidates are not additional theorem premises. Published inputs are listed in the [bibliography](BIBLIOGRAPHY.md).

Run the bounded package checks with:

    python -B tools/validate.py

See [validation scope and receipt](VALIDATION.md). These checks do not evaluate giant hierarchies, build large Laver tables or certify transfinite proofs. The full original IBLP $R$ Hardy/FGH comparison remains open.
