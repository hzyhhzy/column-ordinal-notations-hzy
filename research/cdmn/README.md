# CDMN research status · [中文版](README.zh-CN.md)

October 10, 2026. **The whole CDMN system remains unproved well-ordered; no standard infinite descent is known.** The current expander uses the prefix-zero rule. Positive indices are unchanged. A self-reviewed finite simulation argument identifies its reachable domain and order with the earlier deep-zero version; individual zero steps and old index certificates are not interchangeable.

[Definition](../../notations/CDMN/definition.md) · [NER](../../notations/CDMN/CDMN.ne-rewritten.js) · [Python](../../notations/CDMN/cdmn.py) · [Finite properties](../../proofs/paper/cdmn-properties.md) · [Provenance](../../notations/CDMN/provenance.json)

## Current results and open targets

Here `1=[]` is one empty column, `W=[0:1]`, and superscripts in the compact display are row graphs, not ordinary ordinal powers.

| Subject | Current status |
| --- | --- |
| `S=()(1^(1))` and natural-height seeds | Self-reviewed exact BMS correspondence: S=lim(BMS), and `[][0:h]=BMS(0^h)(1^h)` for h≥1 |
| `T=()(1^(1))(1)(3^(1))(3)` | Self-reviewed proof that this is the least standard term with descendants of arbitrarily large finite nesting depth |
| Ordinary TBMS compared with T | A full source-order embedding gives `lim(TBMS) ≤ T`, under the existing TBMS endpoint interface; no equality or strict inequality at T is established |
| `R∞=()(1^(1))(1)(3^(1))(3^2)(5,3)(6^(1))` | Self-reviewed complete-cone well-ordering argument, covering the entire standard initial segment by comparability |
| `A=()(1^(1)())` | Well-ordering remains open; the first unresolved child is `A[2]=()(1^(1))(2^(2))` |
| BTBMS upper comparisons | Standard carriers and exact first/second-layer formulas; complete descendant embeddings remain open |

The supported comparisons are
\[
\lim(\mathrm{TBMS})\le T<R_\infty<A[2]<A.
\]
Finite CDMN terms use the existing comparator and standard entries. The leftmost ordinal interpretation uses the stated source interface and complete-cone paper proof. `R∞` is a local frontier, **not the CDMN limit**. Thus `lim(TBMS)<R∞` is safe; the saved end-of-window summary does not prove `lim(TBMS)<T`.

## Read the arguments

- [Exact finite-row BMS correspondence and BMS limit](papers/s2-equals-bms.md) gives the later equality, beyond the original lower-bound argument.
- [Depth threshold and TBMS lower bound](depth-and-tbms.md) separates the independent claims.
- [BTBMS comparisons and the adjacent-reader target](btbms-comparisons.md) gives the encoding, formulas, carriers and missing closure.
- [Proof dependencies and standard entries](proof-dependencies.md) specifies the independent interfaces.

The complete Chinese well-ordering derivations are preserved with explicitly **abridged English companions**, in dependency order:

1. [Cumulative row ranks and protected components](papers/cumulative-row-potential.md).
2. [Separated operator drivers](papers/separated-operator-driver.md).
3. [Finite-type drivers](papers/finite-type-driver.md).
4. [Coherent families as a new proof layer](papers/polymorphic-family-driver.md).
5. [Finite proof layers and their common endpoint](papers/finite-universe-diagonal.md).
6. [Uniform families and an exposed mixed port](papers/global-family-mixed-port.md).

These are self-reviewed paper proofs, **not Lean-certified, independently referee-verified, or audited inside KP plus an uncountable ordinal**. Ordinary ZFC is the sufficient ambient framework claimed by the manuscripts. This statement covers the proved cones, not the whole CDMN system.

## Why A is still open

Put `W_j=[j:1]`. For every \(n\ge0\),
\[
A[n]=C_n=[][0:W_0][1:W_1]\cdots[n-1:W_{n-1}],\qquad C_0=[].
\]
C1 is covered by closed-row reflection. In C2, a reader accesses a nonempty earlier column; the copied row still refers to external context. It cannot be put in the independently well-ordered closed row library above. C2 already reaches T, so initial syntax depth is not an induction bound.

Whole-system comparisons with RPD, ARD, SRPD, Y, wY, ordinary/strong e0MN and BTBMS remain unfinished. An unsuccessful map is not an opposite inequality. A raw order-preserving code is not a standard-domain embedding until every image is proved standard.

## Historical counterexample work and validation

Rejected full-source and non-strict-threshold rules admit a parameterized pumping chain. The current strict threshold blocks those mechanisms, not all infinite descents. The [dilation lemma](dilation.md) supplies another sufficient pumping test. Distinguish its old deep-zero macro from the current prefix-zero macro; see its version statement and the [historical evidence index](historical/README.md).

Historical statistics retain unknowns and truncations; they are not claims that every old experiment was rerun during packaging. Current executable checking is `python -B tests/cdmn.py`; the [validation receipt](../../tools/cdmn-validation.json) records its scope. Neither finite checks nor strict one-step lexicographic decrease prove well-ordering. No global CDMN Lean theorem or new PDF is supplied.
