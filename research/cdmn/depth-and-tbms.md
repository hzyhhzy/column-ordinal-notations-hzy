# The depth threshold and TBMS lower bound · [中文版](depth-and-tbms.zh-CN.md)

This result and proof outline uses the current prefix-zero CDMN rule. Minimality and embedding are independent claims. Both remain self-reviewed paper arguments, not Lean theorems; see the [dependency ledger](proof-dependencies.md).

## The least unbounded-depth term

Let \(1=[]\), \(W=[0:1]\), \(S=[][0:W]\), and
\[
L(G)=G[0:1][|G|:W],\qquad M_{-1}=S,\quad M_n=L(M_{n-1}),
\]
\[
T=M_0[2:1]=()(1^{(1)})(1)(3^{(1)})(3).
\]
The exact rule gives \(T[n]=M_n\) for every \(n\ge0\). Depth counts actual nested syntax, without shared compression.

The paper argument proves that the complete cone of Mn has maximum depth n+3, while T has descendants of arbitrarily large finite depth. Every proper standard term below T belongs to one fixed Mn cone and therefore has a finite depth bound. Standard-domain comparability makes T the least standard term with unbounded descendant depth.

The invariant is a decomposition into protected closed components. If G's cone has depth≤d, put B=G[0:1]. Its children are finite closed concatenations of G. After the first step of L(G), its reader has become a closed row assembled from B descendants. Real data references may target only the separator or later data, never G's interior. Low-root singleton row-1 columns cannot mix with real data under the strict guard. Copying preserves complete components; when data disappear, B expands independently. Thus L raises the bound by at most one.

The bound is attained:
\[
M_n([1][0])^n=D_n,\quad D_0=M_0,\quad
D_n=M_{n-1}[0:1][2n+2:\tau_{2n+3}(D_{n-1})].
\]
Dn has depth n+2, and one more [1] reaches n+3.

For a term already known standard,
\[
\operatorname{DepthUnbounded}(Q)\iff Q\ge T.
\]
For Q<T, set \(m=\max(0,\lceil(|Q|-4)/2\rceil)\). Then Q≤Mm, giving bound m+3. This test is not asserted for arbitrary unreachable legal graphs. Unbounded finite depth does not establish an infinite descending chain.

## A full TBMS source embedding

Let \(Q_0=(), Q_{j+1}=()(1^{Q_j})\) be the ordinary TBMS seeds. The proof uses the independently supplied canonical-parent-table and recursive cumulative-endpoint interface, not an unknown CDMN rank.

A base code C0 embeds \(g<Q_3\) into M0 and has the entrance
\[
M_0[1][0][q+1]=C_0(Q_3[q]).
\]
It shifts real parents by 2, represents empty source columns by low-root row 1, and uses natural-row parent codes for its endpoints. This base simulation and the source interface are stated dependencies, not new Lean certificates supplied by this outline.

At level n≥1, fix P=M(n−1), b=|P|=2n+2. A source column j with parent-table record (p,v) is encoded by
\[
(b+p,\tau_{b+j}(C_{n-1}(\operatorname{cat}(v)))).
\]
Empty parent tables become [0:1]; source zero maps separately to the empty graph. Closed row transport and uniform parent offsets preserve order.

Deletion uses finite cleanup. Unit copying first prepares the actual predecessor endpoint with a trailing empty column, then takes a genuine outer step. High-row refinement uses the actual new cumulative endpoint, including formerly absorbed pieces. To restore an empty source column, a finite parent-decreasing cleanup returns its low-root marker.

The identity
\[
M_n[1][0]=M_{n-1}[0:1][2n+2:\tau_{2n+3}(M_{n-1})]
\]
gives all higher entrances by lifting lower-level row paths. Hence every source descendant has a standard target image.

Choose \(\ell(g)=\min\{n:g<Q_{n+3}\}\) and F(g)=Cℓ(g)(g). The level-0 images lie below M0; at n≥1, nonzero images lie strictly between M(n−1) and Mn. These disjoint increasing intervals give one global strict order embedding. Mapping the source external top to T proves
\[
\operatorname{Std}(\mathrm{TBMS})\cup\{\mathrm{Limit}\}
\hookrightarrow \operatorname{Desc}(T)\cup\{T\},
\qquad \lim(\mathrm{TBMS})\le T.
\]
Cofinality is not equality. A strict inequality at T is not established.

## Complete-cone well-ordering is a separate result

The embedding does not prove T's complete cone well-ordered. The independent [cumulative-row transfer](papers/cumulative-row-potential.md), its finite L iterations, and first-step decomposition do. Later [mixed-port work](papers/global-family-mixed-port.md) reaches R∞, yielding the safe bound
\[
\lim(\mathrm{TBMS})\le T<R_\infty.
\]
See [standard entries](proof-dependencies.md) and [bounded historical evidence](historical/README.md). These experiments do not replace the universal arguments.
