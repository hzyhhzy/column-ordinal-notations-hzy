# Separated operators and visible ports · [中文全文](separated-operator-driver.zh-CN.md)

This is an abridged English companion to the [full Chinese derivation](separated-operator-driver.zh-CN.md). It uses the [cumulative-row transfer theorem](cumulative-row-potential.md). Claims remain self-reviewed paper proofs for the prefix-zero rule.

Fix an independently well-ordered closed base \(G\) and a countable, well-ordered, expansion-closed domain \(R\) of closed rows containing 0 and 1. A driver consists of complete operator pairs \([0:1][a:W]\), singleton row-1 ports pointing to separators, and data columns pointing only to ports or other data. Ordinary data cannot reference an operator's interior or its \(W\) column.

Delete the hidden \(W\) columns and compress the base to obtain a finite skeleton. Its cumulative row labels give a fixed reflection measure \(\mu\). Every data step preserves the driver grammar and decreases \(\mu\): a port has only one row-1 record, so its shell becomes empty before it copies a complete operator pair; a nonempty data shell blocks inherited row 1.

Induct on \(\mu\). A terminal data column uses the smaller-step induction hypothesis. A terminal complete operator is \(L(P)\): first prove the shorter prefix \(P\) well-ordered, then use the already established transfer theorem. A terminal cap uses closed concatenation. The proof does not pretend the unknown interior of an operator is a fixed closed row.

## A final open reader

If \(F\) is a proved driver and \(c\) a visible port or data position, then \(F[c:W]\) also has a well-ordered complete cone. First fix the already proved \(F\), and use \(R\cup E_F\) as the closed row library. Its positive children are exactly \(F[c:F^{\oplus n}]\), with rows translated to the owner, and its zero child is \(F[]\). Each child belongs to the proved driver class.

This is not permission to append arbitrary readers repeatedly: the newly added \(W\) is not automatically visible driver data.

The concrete consequence is
\[
N=T[4:W]=()(1^{(1)})(1)(3^{(1)})(3)(5^{(1)}).
\]
Its complete cone, hence its standard initial segment, is covered. The original manuscript's then-open \(H\) is solved by the following finite-type paper, not by this lemma alone.

See [proof dependencies](../proof-dependencies.md) for standard entries and [historical checks](../historical/README.md) for bounded tests. No weak-axiom reduction or Lean certificate is asserted.
