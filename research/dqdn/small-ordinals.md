# DQDN locations and exact small values · [中文版](small-ordinals.zh-CN.md)

This is a condensed English reading edition of the full Chinese manuscript. It retains the exact-value tables, current bounds, conventions, main proof mechanisms and correction boundary; the detailed admissible-relation derivations remain in Chinese §§6, 9, 10 and 13. **Paper equality, carrier lower bound, independent source graph and TOP-standard expression are different claims.** No table entry is inferred just from a finite computation test.

Write A_n=TOP[2][n] and H(b)=h(B(1,b,L_initial,pending_empty)). The ordinary source rank counts every demanded computational step. A compressed query-tree rank may be smaller by deterministic overhead.

## Standard small values

TOP[1]=ε₀ and TOP[1][1]=ω; the latter has 17 data columns and one active column. Further calibrated values include ω² through ω¹⁰, ω^ω, ω^(ω+1), and ω^(ω·2). Their paths and lengths are in the tables below. The specific ω⁴ and ω⁸ paths require more columns than some larger powers because the fixed generator order, rather than shortest source syntax, determines their positions.

The 880-column ω^ω path stops just after its final generator output; omitting that last step leaves a source with one more full-rank step and value ω^(ω+1), in 879 columns. The extra loop source used for ω^(ω·2) needs 1,079 columns. These equalities include the prefix analysis, not only identification of the last source.

The proof pattern is to expose the exact final demanded source, compute its full rank, and bound every surviving earlier sibling block. Smaller exponents are absorbed by the final principal term. An independent hand-written ε₀ source with 21 columns is therefore kept separate from the standard two-column ε₀ boundary; see [epsilon0](epsilon0.md).

## The first budgets of the second generator

For n≥1 the column valuation gives

$$|A_n|=\varepsilon_0+\sum_{i<n}\omega^{H(c(i))},
\qquad |A_0|=\varepsilon_0+1.$$

This is an ordinal sum in the displayed order, not a commutative sum. The finite data of each child block is absorbed by its nonzero active weight. Answer b>0 first occurs at child index 2b+1, hence at the last block of A_(2b+2). Odd n generally leave an additional smaller tail.

Each S/Q construction costs three fields, context extension/variable/numeral/application four, lambda abstraction three, and Rec five. The cheapest closed Nat recursion step costs 18 fields: two context extensions, a variable and two lambdas. With Rec this is 23; a potentially nonzero queried index requires another three fields. Thus budgets through 25 cannot execute an unbounded recursion loop.

In that range, a useful one-argument lambda consists of a chain of S/Q above a variable or numeral. An optimistic shared cost for a applications, k body S/Q nodes and u outer S/Q nodes is 11+3k+4a+3u, with at most u+a(k+1) computation steps. The possible cases under budget 25 are bounded by floor(b/3). Consecutive Q constructors attain it; one or two spare fields can remain uncommitted. Including b construction steps and one output step gives H(b)=b+1+floor(b/3).

At budget 26, R(0,I,Q0), with I=λk.λx.x, has rank ω: after the query answer m it makes 3m+1 finite steps. No more complex useful Rec shape fits this budget. Budgets 27–28 add only generation overhead. At 29–30 an extra S/Q can add one source-rank step but not a second unbounded loop.

Budget 31 first permits two useful Rec nodes sharing I and Q0. Let t=R(Q0,I,Q0) and u=R(t,I,t). Its shared syntax is evaluated afresh at each occurrence. There are four independent queries and three successive arbitrary finite loops; the first three answers a,b,c give 3(a+b+c)+7 steps. Its source rank is ω·3, not ω·2. The minimal-cost classification leaves no budget for another recursion in I or higher-type iteration; this shape gives the maximal loop pattern.

Accordingly the current **paper** classification is

$$H(b)=\begin{cases}
b+1+\lfloor b/3\rfloor,&0\le b\le25,\\
\omega+b+1+\lfloor(b-26)/3\rfloor,&26\le b\le30,\\
\omega\cdot3+32,&b=31.
\end{cases}$$

The previous ω·2+32 claim was withdrawn because it ignored returned query values used for later control. The current universal upper classification is still a paper case analysis, not an exhaustive finite search or independently checked theorem. `small_generator_ranks.py` replays witnesses and selected traces. Its formulas for **b=32…35 remain candidates**; no new exact values beyond n=65 are published here.

## Later source-rank lower bounds

Put δ(x)=R(x,I,x). It evaluates x first as an index and later afresh as the base. A return-value-sensitive continuation-rank induction gives the rank of δ^r(Q0) as ω(2^r−1) for r≥1. The source

$$W_2=R(Q0,\lambda k.\lambda x.\delta(x),Q0)$$

has full rank ω²: fixing the outer answer gives finitely many queries/loops with ranks cofinal in ω². Its actual generation costs 49 fields, so

$$|A_{100}|\ge\varepsilon_0+\omega^{\omega^2+50}.$$

A type-iterated ordinary source of rank ω^ω costs 86 fields and gives

$$|A_{174}|\ge\varepsilon_0+\omega^{\omega^\omega+87}.$$

The exact independent ε₀ source costs 208 fields under this authoring route and gives

$$|A_{418}|\ge\varepsilon_0+\omega^{\varepsilon_0+209}
=\varepsilon_0\cdot\omega^{209}.$$

These are not equalities for their carriers and need not be minimal construction budgets.

## Veblen and compact iterator bounds

The full manuscript first uses ordinary System F encodings of zero, successor and countably branching trees. Its observer interprets a limit by a strict Q and recursively observes the selected child. Correctness requires preserving the tree, not just its final numeral. Veblen limits require strictly smaller cofinal approximants; a branch that already reaches the proposed supremum cannot be treated as a harmless cofinal child.

The later compact construction replaces those explicit trees by polymorphic iterator profiles. For a base relation R(t,α), the admissibility conditions permit deterministic predecessors and a demanded query over cofinal strict lower bounds. Higher function profiles uniformly preserve all related arguments. Finite function-level iteration realizes multiplication and exponentiation profiles; the self-power macro S and the ε-closure macro E act uniformly over arbitrary admissible base relations. This uniformity permits using the polymorphic iterator type itself as a base, rather than assuming a missing lifting step.

The derived operator D advances a strictly-lower-level Veblen coverage relation by one. A diagonal K(c) realizes sup_(β<α) φ_β(α) when c realizes α≥ω. This must not automatically be called φ_α(α). For nonzero limit ω≤α<Γ₀ it is φ_α(0): the smaller Veblen fixed points give the lower bound; α<φ_α(0) and the common fixed-point property give the upper bound. Iterating from ω produces a sequence cofinal in Γ₀.

The full admissibility, lifting and coverage inductions are in Chinese §13. The following are source-to-standard **lower** bounds, using recorded real construction fields b and one output step. The numerical index is 2b+2; none is claimed minimal.

| Source target bound | Independent columns | Fields b | Standard carrier bound |
| --- | ---: | ---: | --- |
| ε₀ | 18 | 145 | ε₀·ω^146 ≤ A_292 |
| ε_ω | 21 | 175 | ε_ω·ω^176 ≤ A_352 |
| ζ₀ | 24 | 261 | ζ₀·ω^262 ≤ A_524 |
| η₀=φ₃(0) | 33 | 460 | η₀·ω^461 ≤ A_922 |
| φ_ω(0) | 33 | 464 | φ_ω(0)·ω^465 ≤ A_930 |
| Γ₀ | 35 | 441 | Γ₀·ω^442 ≤ A_884 |

All these are ordinary source programs, not additions to the DQDN core. Later type-reuse experiments lower some field counts; the [index](README.md) keeps those implementation measurements distinct from the written bounds above.

## Buchholz conventions and BHO

Use the original tree rules in [Buchholz 1987, §1 and appendix](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf), not the Arai or Schwichtenberg variants. With 1=0⁺ they include D₀(0)=1, D_(σ+1)(0)=(z)_(z∈𝒯_σ), and D_σ(a⁺)=(D_σ(a)·(n+1))_(n∈ℕ). For a branch a=(a_x)_(x∈𝒯_u) with σ≤u,

$$D_\sigma(a)=(D_\sigma(a_z))_{n\in\mathbb N},\qquad z=D_u(a_1).$$

The last family is **constant in n**, not n iterations of a selection map. Its query root still adds one to the tree rank. The reference code has explicit convention options only to expose this distinction; the rank theorem is applied to `buchholz`.

For each fixed finite v, ordinary System F encodes trees by

$$T_0=\mathbb N,\quad
T_v=\forall X.\ X\to(X\to X)\to
((T_0\to X)\to X)\to\cdots\to((T_{v-1}\to X)\to X)\to X.$$

One fold returning a tuple simultaneously computes the collapse components. At a T_r-indexed branch, the r−1 component supplies the correctly typed repeated index; using the target σ component instead would be a type error. The Church equations reproduce the original tree equations on the finite generated terms. Every fixed v still uses kind `*`, hence is available in G(1).

The original rank theorem and [Buchholz 1986, Theorem 3.7](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf) give, for 0<ν<ω,

$$\kappa_\nu=|ID_\nu|=\psi_0(\varepsilon_{\Omega_\nu+1})
=\sup_k\operatorname{rk}(D_0D_\nu^k0).$$

In particular κ₁=BHO. Querying k and selecting this finite iteration gives query rank κ_ν. Warming up to the first Q and applying stretching gives full rank κ_ν as well. This does **not** identify the rank of each individual Buchholz term with its ψ assignment; only the cofinal-family supremum is used.

Recorded standard carriers are BHO<A_4366, improved by ordinary source simplification to A_3054 and A_2690; and κ₂<A_7588, improved to A_6426. The independently written diagrams have 173/139/271 columns, not the lengths of their standard carriers. Bounded branch tests, type checks and real field replays support the implementation interface, not the infinite rank theorem. Some larger reference-tree test cases intentionally hit their node/query guards and are not counted as completed expansions.

## What BO means here

Here **BO=ψ₀(Ω_ω)=sup_(1≤ν<ω)κ_ν**. The continuity at this limit follows from the finite-closure definition: each finite derivation of membership uses finitely many parameters, already below some member of a cofinal sequence. This is not another name for BHO.

Each fixed ν program lies at level one, so BO≤TOP[2]. This establishes neither equality nor strictness, nor a particular A_n carrying all of BO. A metalevel Python function constructing a different program for each ν is not one closed System F program uniformly covering all ν.

## Three-view table

Only TOP-standard expressions appear below. Counts longer than 100 columns are abbreviated by their length. The view extractor checks exact column round trips; the ordinal labels retain the paper proof status explained above. Minimal means least sufficient index at each step, not fewest steps. In the growth view, `0` denotes an equal-length replacement yielding the one-column ordinal 1; the zero expression displays `∅`.

### Main values

| Ordinal | Count sequence | Minimal operation path | Net-growth sequence |
|---|---|---|---|
| $0$ | `0` | `TOP[0]` | `∅` |
| $1$ | `1` | `TOP[1][0]` | `0` |
| $\omega$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2` | `TOP[1][1]` | `1,16` |
| $\omega\cdot2$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2` | `TOP[1][2]` | `1,18` |
| $\omega\cdot3$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2` | `TOP[1][3]` | `1,20` |
| $\omega^2$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2` | `TOP[1][4]` | `1,24` |
| $\omega^3$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[1][6]` | `1,30` |
| $\omega^4$ | 【185 columns】 | `TOP[1][8][38]` | `1,36,147` |
| $\omega^5$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[1][8]` | `1,36` |
| $\omega^6$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[1][10]` | `1,42` |
| $\omega^7$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[1][12]` | `1,48` |
| $\omega^8$ | 【200 columns】 | `TOP[1][14][38]` | `1,54,144` |
| $\omega^9$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[1][14]` | `1,54` |
| $\omega^{10}$ | `1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[1][16]` | `1,60` |
| $\omega^\omega$ | 【880 columns】 | `TOP[1][54][8][1][1][1][8][1][1][1][26][1][1][1][30][1][1][30][1][1][40][8][1][42][1][4][1][1][1]` | `1,174,27,5,5,6,23,5,5,6,86,5,5,5,91,5,7,89,5,7,124,29,6,126,5,15,5,6,1` |
| $\omega^{\omega+1}$ | 【879 columns】 | `TOP[1][54][8][1][1][1][8][1][1][1][26][1][1][1][30][1][1][30][1][1][40][8][1][42][1][4][1][1]` | `1,174,27,5,5,6,23,5,5,6,86,5,5,5,91,5,7,89,5,7,124,29,6,126,5,15,5,6` |
| $\omega^{\omega\cdot2}$ | 【1079 columns】 | `TOP[1][64][8][1][1][1][8][1][1][1][26][1][1][1][30][1][1][30][1][1][40][8][1][42][1][4][1][1][42][1][6][1][1][1][1][1]` | `1,204,27,5,5,6,23,5,5,6,86,5,5,5,91,5,7,89,5,7,124,29,6,126,5,15,5,6,125,5,23,5,6,1,3,2` |
| $\varepsilon_0$ | `1,2` | `TOP[1]` | `1` |

### Early second-layer values

| Ordinal | Count sequence | Minimal operation path | Net-growth sequence |
|---|---|---|---|
| $\varepsilon_0+1$ | `1,2,1` | `TOP[2][0]` | `2` |
| $\varepsilon_0+\omega$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2` | `TOP[2][1]` | `3,17` |
| $\varepsilon_0+\omega\cdot2$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2` | `TOP[2][2]` | `3,19` |
| $\varepsilon_0+\omega\cdot3$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2` | `TOP[2][3]` | `3,21` |
| $\varepsilon_0+\omega^2$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,2` | `TOP[2][4]` | `3,24` |
| $\varepsilon_0+\omega^2+\omega$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,2,1,2` | `TOP[2][5]` | `3,26` |
| $\varepsilon_0+\omega^3$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,2,1,2,1,1,1,2` | `TOP[2][6]` | `3,30` |
| $\varepsilon_0+\omega^5$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[2][8]` | `3,36` |
| $\varepsilon_0+\omega^6$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[2][10]` | `3,42` |
| $\varepsilon_0+\omega^{13}$ | `1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2,1,2,1,1,1,2` | `TOP[2][20]` | `3,72` |
| $\varepsilon_0+\omega^{19}$ | 【106 columns】 | `TOP[2][30]` | `3,102` |
| $\varepsilon_0+\omega^{26}$ | 【136 columns】 | `TOP[2][40]` | `3,132` |
| $\varepsilon_0+\omega^{33}$ | 【166 columns】 | `TOP[2][50]` | `3,162` |
| $\varepsilon_0+\omega^{34}$ | 【172 columns】 | `TOP[2][52]` | `3,168` |
| $\varepsilon_0+\omega^{34}+\omega^{17}$ | 【174 columns】 | `TOP[2][53]` | `3,170` |
| $\varepsilon_0+\omega^{\omega+27}$ | 【178 columns】 | `TOP[2][54]` | `3,174` |
| $\varepsilon_0+\omega^{\omega+27}+\omega^3$ | 【180 columns】 | `TOP[2][55]` | `3,176` |
| $\varepsilon_0+\omega^{\omega+28}$ | 【184 columns】 | `TOP[2][56]` | `3,180` |
| $\varepsilon_0+\omega^{\omega+29}$ | 【190 columns】 | `TOP[2][58]` | `3,186` |
| $\varepsilon_0+\omega^{\omega+31}$ | 【196 columns】 | `TOP[2][60]` | `3,192` |
| $\varepsilon_0+\omega^{\omega+32}$ | 【202 columns】 | `TOP[2][62]` | `3,198` |
| $\varepsilon_0+\omega^{\omega\cdot3+32}$ | 【208 columns】 | `TOP[2][64]` | `3,204` |
| $\varepsilon_0+\omega^{\omega\cdot3+32}+\omega^{21}$ | 【210 columns】 | `TOP[2][65]` | `3,206` |
