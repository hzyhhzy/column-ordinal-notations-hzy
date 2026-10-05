# DQDN results and proofs · [中文版](README.zh-CN.md)

This directory preserves the mathematical work available when DQDN research was paused on 2026-10-05. Repository integration does not restart the timed research. The [implementation](../../notations/DQDN/README.md) and [well-ordering argument](../../proofs/paper/dqdn-well-ordering.md) have separate entries.

**Evidence convention:** a paper result below is a claim supported by the collected written argument, not an independently refereed or Lean-certified theorem. Finite program checks certify only the tested paths and interfaces. In particular, a program's source rank is not automatically the ordinal value of its entire TOP-standard carrier.

## Main conclusions

| Claim | Evidence and scope |
| --- | --- |
| The TOP-standard DQDN domain is well-ordered | [Paper argument](../../proofs/paper/dqdn-well-ordering.md); all-answer typed normalization and the common-root order lemma |
| TOP[1]=ε₀ | [Tower profiles](tower-profiles.md), [epsilon0](epsilon0.md); includes the separate uniform System T upper bound |
| ω through selected larger powers, and early TOP[2][n] | [41-row three-view table and explanations](small-ordinals.md); exact paper classifications through n=65, not a finite-test proof |
| ζ₀<TOP[2][524], Γ₀<TOP[2][884] | [Compact iterator argument](small-ordinals.zh-CN.md), §13; carrier lower bounds, not equalities |
| BHO<TOP[2][2690] | Same manuscript, §9; original Buchholz tree convention, not an exact standard location |
| BO≤TOP[2] | Same manuscript, §9.5; **BO means ψ₀(Ωω)**, not BHO |
| BMS(0⁴)(1⁴)<TOP[2]; lim(BMS)≤TOP[2] | [BMS comparison](bms-top2.md); uses fixed-height BMS and a parameter-preserving System F extraction argument |
| Global DQDN limit ≥ PTO(Zω) | [Girard interface](girard-oracle-bridge.md); finite-order full comprehension, not System T alone |
| Global limit = PTO(Zω), or TOP[2]=PTO(Z₂) | **Not established**; [upper-bound obligations](upper-bound-open.md) remain |

The BMS manuscript gives the more informative chain

$$\sigma_4<\mathrm{PTO}(Z_2)\le |\mathrm{TOP}[2]|,
\qquad \lim(\mathrm{BMS})\le\mathrm{PTO}(Z_2)\le |\mathrm{TOP}[2]|.$$

It neither assumes nor proves lim(BMS)=PTO(Z₂). It supplies no implemented BMS→DQDN converter commuting with fundamental sequences, and no concrete n carrying the four-row BMS seed below TOP[2][n].

## Reading route

1. [Definition](../../notations/DQDN/definition.md): ordinary demand rules, all 28 generator operations, standardness and column order.
2. [Well-ordering](../../proofs/paper/dqdn-well-ordering.md): typed sources, finite fuel, ordinal weights and why lexicographic descent is covered.
3. [Tower profiles](tower-profiles.md) and [epsilon0](epsilon0.md): distinguish compressed query rank, one-step source rank, independent graphs and standard carriers.
4. [Small ordinals](small-ordinals.md): main equalities, early-fuel classification, Veblen/Buchholz constructions and the three-view tables. The full derivations and correction history are retained in the Chinese manuscript; English is a condensed reading edition, not a line-by-line translation.
5. [BMS comparison](bms-top2.md), [global Girard bridge](girard-oracle-bridge.md), [open upper bound](upper-bound-open.md).

The main definition, usage and well-ordering paper are bilingual. The six research manuscripts have English companions; the long small-ordinal companion is explicitly abridged. No single-language blanket exemption has been added to release checks.

## Corrections and unfinished work

- The old H(31)=ω·2+32 claim was withdrawn. The current paper classification is **H(31)=ω·3+32**, accounting for a returned query value that controls a later loop. The original correction is retained in §10.4.
- Upper bounds for fuel b=32…35 remain unfinished. `small_generator_ranks.py` includes lower witnesses and candidate formulas beyond 31, not established equalities beyond n=65.
- Type-reuse experiments in `compact_type_author.py` reduce field counts further without changing the source programs. The main comparison table above deliberately uses the bounds with fully recorded manuscript derivations; it does not silently convert every later measured field count into a new exact ordinal location.
- ζ₀, Γ₀, BHO and BO have not been given exact standard names here. Finite sibling prefixes must be audited for any equality, even when the final independent source has a known rank.
- No object-theory formalization, general proof extractor, optimized weak-theory upper bound or DQDN Lean project has been completed.

## Code and verification

[code/](code/) contains the exact-current-kernel authoring helpers and bounded tests needed by these manuscripts. Runtime dependencies live in `notations/DQDN/`; older CCDN/LCDN/LQDN candidate frontends, session-recovery utilities, private PDFs and scratch caches are not being published as DQDN.

Run `python -B tests/dqdn.py` at repository root. It configures local imports and runs fixed test groups with time, DAG, step, output and memory budgets. See the [validation record](validation.md) for results and limits. The original NER host-source test depended on an outside checkout; it is not claimed as a portable test or a live browser test in this package.
