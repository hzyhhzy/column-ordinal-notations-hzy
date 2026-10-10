# Cumulative row ranks and complete cones · [中文全文](cumulative-row-potential.zh-CN.md)

This is an abridged English companion to the [full Chinese derivation](cumulative-row-potential.zh-CN.md). All claims are self-reviewed paper arguments for the prefix-zero rule, not Lean certificates or independent mathematical review.

Let \(1=[]\), \(W=[0:1]\), \(S=[][0:W]\),
\(L(G)=G[0:1][|G|:W]\), and \(P(G)=L(G)[|G|:1]\).
The transfer theorem is: if the complete cone of a nonzero closed \(G\) is well-ordered, so is the complete cone of \(L(G)\).

## Fixed closed row domains

For an independently well-ordered, expansion-closed row domain with rank \(\rho\), replace a column's raw row values by cumulative semantic labels
\[
K_i=\sum_{j\le i}\omega^{\rho(r_j)}.
\]
These labels increase even when the raw rows do not. A donor row \(d\) passes the strict guard only if it exceeds all preceding seam and donor rows. Its power absorbs their cumulative sum; its inherited \(K\) is exactly the donor's original \(K\). The fixed countable-row reflection theorem in the [existing proof](../../../proofs/paper/well-ordering.md) therefore supplies a strictly decreasing last-label measure. This is a proof measure, not a modification of the expander.

## The precise row library

Put \(B=G[0:1]\), and let \(\alpha\) be the order type of the proper cone of \(G\). The required library is
\[
E_G=\{B^{\oplus k}\oplus G^{\oplus l}\oplus H:k,l<\omega,\ H<G\},
\]
with rank \(\alpha\omega k+\alpha l+\rho_G(H)\).
Its closed concatenations expand right to left. It is expansion-closed and ordered lexicographically by \((k,l,H)\). Arbitrary finite concatenations of arbitrary descendants must not replace this library: their raw lexicographic order need not be well-founded.

## Protected components

After the first step of \(L(G)\), retain a protected \(B\) prefix. Real data references may target its final separator or later data, not the interior of \(G\). Data rows belong to \(E_G\); low-root singleton row-1 columns remain separate from real data. The strict guard preserves this distinction.

Compress only the inaccessible \(G\) interior to a root marker. The reflection label \(\mu\) of the remaining skeleton decreases under data operations, copying and component deletion. Once the last component enters an actual \(G\)-descendant \(H\), its known rank \(\nu=\rho_G(H)\) decreases while the skeleton stays fixed. Thus \((\mu,\nu)\) decreases lexicographically. Taking the least measure over valid finite decompositions makes the argument independent of a chosen decomposition.

Natural-number rows establish the base \(S\). The exact identity \(P(G)[n]=L^{n+1}(G)\) then proves \(P\) preserves complete-cone well-ordering. In particular \(T=P(S)\) and subsequent finite iterations are covered. Later papers extend this frontier.

Ordinary ZFC covers the stated construction; the full object-by-object reduction to KP plus an uncountable ordinal has not been audited. See [dependencies](../proof-dependencies.md) and [historical checks](../historical/README.md).
