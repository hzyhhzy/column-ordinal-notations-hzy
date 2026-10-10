# Uniform families and an exposed mixed port · [中文全文](global-family-mixed-port.zh-CN.md)

This is an abridged English companion to the [full Chinese derivation](global-family-mixed-port.zh-CN.md).

For a coherent finite pattern \(A\), write
\[
\mathcal F(A)\iff
\forall h<\omega\ \forall k\ge m(h)\,
\operatorname{Good}_{h,k}(A_{h,k}).
\]
All Good predicates are defined beforehand by the [finite-layer construction](finite-universe-diagonal.md). The previous anchor occurs only in the first singleton row-1 boundary; later references use global 0 or the local block root.

With \(a=|A|\), both
\[
\Delta A=A[\mathrm{self}:2],\qquad
\Xi A=A[\mathrm{self}:2][\mathrm{self}+a:1;\mathrm{self}:1]
\]
preserve \(\mathcal F\). For \(\Delta\), each child evaluates a finite same-layer type tower. For \(\Xi\), it evaluates a tower starting \(n\) proof-family layers higher and descending back to the original layer. Only independently known good families and the already proved row-2 operator occur as arguments; \(\Xi\)'s own preservation is not an input assumption.

## The mixed-port driver

After a known base, allow complete \(\Xi\) pairs, singleton row-1 ports pointing to separators, and closed-row data referencing mixed ports, ordinary ports or data. Compress the base, but retain both columns of every \(\Xi\) pair in the reflection skeleton.

A donor mixed port contains two row-1 records. A nonempty shell blocks both; an empty shell inherits only the first, after which the strict threshold blocks the second. The result is an ordinary port, not an incomplete unknown macro. A separator can be reached only through a singleton row-1 port; it copies the whole \(\Xi\) pair. These cases preserve the driver grammar and decrease the fixed cumulative-row measure.

Induction on this one parameter-independent measure proves the driver uniformly at every layer and type. Terminal \(\Xi\) or \(\Delta\) calls their already proved preservation properties on a smaller prefix.

A final \(W\) may read at a visible mixed port, ordinary port or data position. Fix parameters, independently prove the resulting prefix \(p\), and use the closed library \(R\cup E_p\). Its children are \(p[c:p^{\oplus n}]\), plus \(p[]\) at zero. This does not allow unrestricted later partial copies of the new reader.

Applying the construction to \(\Lambda=[\mathrm{prev}:1][\mathrm{self}:W]\) over \(S\) yields the current full-cone paper frontier:
\[
R_\infty=[][0:W][0:1][2:W][2:2][4:1;2:1][5:W].
\]
It is standard, exceeds \(F_\infty\), and is below \(A[2]=()(1^{(1)})(2^{(2)})\). Neither that \(A[2]\) nor the entire CDMN system has a well-ordering proof.

The result is self-reviewed, not Lean-certified or independently reviewed. The weak-axiom ledger remains open. See [standard entries and dependencies](../proof-dependencies.md) and [historical checks](../historical/README.md).
