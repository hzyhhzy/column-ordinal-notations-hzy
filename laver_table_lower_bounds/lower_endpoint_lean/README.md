# Lower critical endpoints in Lean · [中文](README.zh-CN.md)

**The complete BMS bound is currently at kappa-3-11. The BMS tower bound at the smaller endpoint eta is not yet formalized.**

[K11Bound.lean](K11Bound.lean) proves, for every ordinary binary finite Laver-table family,

$$
A_m(11,16)\ne0\ \Longrightarrow\
F_{\Lambda+1}(120)\downarrow\ \land\
F_{\Lambda+1}(120)<v_2(A_m(11,16))<m,
\qquad\Lambda=\lim(\mathrm{BMS}).
$$

Elements use residues modulo 2^m; zero represents the usual final element. The valuation is capped at m. The statement requires only this particular entry to be nonzero, not a period-32 assumption on row 1. Its index is stable at every larger order. Consequently, its finite stable index is either absent or exceeds the stated BMS+1 value. Under the usual critical-point interpretation it is the index of kappa-3-11, namely J11(gamma4).

The numerical BM4 hierarchy, including its actual terminating evaluation, is inherited from the [shared library](../lean/README.md). The argument uses 131 of 252 actual segments for initialization, then 121 feedback steps. Each step realizes a base BMS FGH evaluation and rebuilds the complete row budget for the next call. See [Entrance](K11/Entrance.lean), [Counting](K11/Counting.lean), [Feedback](K11/Feedback.lean), and [Successor](K11/Successor.lean).

For the smaller endpoint

$$
\eta=\bigl((J_{11}(J_3))(J_7)\bigr)(\gamma_3),
$$

[Word.lean](LowerEndpoint/Word.lean) defines the exact finite-table word and proves projection, non-saturated index stability, and uniqueness for arbitrary application words. [Entrance.lean](LowerEndpoint/Entrance.lean) constructs the compressed low background directly from table equations and proves the finite-index version of

$$
\eta<\kappa^{11}_3<\kappa^{10}_3<\kappa^9_3<\kappa_4,
\qquad\kappa_4=\gamma_{q(5)-1}
$$

when q(5) exists. Application between embeddings is left-associated and is not ordinary composition.

The remaining paper target is the bound F_(C[6])(2047) at eta, with C and its fundamental sequences fixed by the [tower manuscript](../01-blp-tower.zh-CN.md). Two essential steps remain: a strict-supremum cap below eta and the whole-type relative BMS compiler with its precise numerical comparison. Neither is assumed as an axiom or as a hidden hypothesis. The intermediate comparison with J13(gamma16) is also not yet part of the machine-checked result.

Build with Lean 4.33.1 and Python:

```sh
python -B build.py --lean-bin /path/to/lean/bin --record
```

The script rebuilds all local and shared source dependencies into this directory's `.build`; each compiler uses one thread, at most 2048 MB, and a 60-second timeout. The [receipt](verification/VERIFICATION.json) and [log](verification/build.txt) explicitly distinguish verified results from the remaining target. No existing proof project or verification receipt is modified.

These are direct finite-combinatorial theorems in ordinary Lean foundations, not object-language ZFC derivations or a Lean construction of I3 models. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in final axiom audits. [PROVENANCE.json](PROVENANCE.json) records sources and normalized hashes.
