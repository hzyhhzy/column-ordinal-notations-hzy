# BLP and BMS bounds at smaller endpoints · [中文](README.zh-CN.md)

Chinese PDFs: [Overview](README.zh-CN.pdf) · [Common entrance](endpoints.zh-CN.pdf) · [BLP proof](blp.zh-CN.pdf) · [BMS proof](bms.zh-CN.pdf).

This collection edits two paper arguments of 2026-11-09 for inclusion on **2026-11-14**. Assume **ZFC + I3**, using one fixed generator $j$ and its $\operatorname{Iter}(j)$. These are paper proofs, not new Lean certificates or reductions to the assumption that a particular finite-table entry is nonzero.

Write $J_1=j$ and $J_{n+1}=J_n(j)$. Parentheses between embeddings denote application, associated to the left; $\circ$ denotes ordinary composition. The $\gamma_n$ enumerate generated critical points in increasing order. In particular,

$$
\kappa_0=\gamma_0,\quad\kappa_1=\gamma_1,\quad
\kappa_2=\gamma_2,\quad\kappa_3=\gamma_4.
$$

Define

$$
\begin{aligned}
\xi&=((J_{11}(J_3))(J_7))(\kappa_2)=\gamma_r,\\
\eta&=((J_{11}(J_3))(J_7))(\gamma_3)=\gamma_s,\\
\Sigma&=J_{13}(\gamma_{16})=\gamma_N,\qquad
\Theta=J_{11}(\kappa_3).
\end{aligned}
$$

The two constructions have different actual endpoints, with

$$
\boxed{J_{11}(\gamma_3)<\xi<\eta<\Sigma<\Theta.}
$$

**Ordinary BLP**

$r\ge2^{f(P_{25},8)}$ and, independently, $r\ge2^{\Psi^{\circ4}(8)}$, where $\Psi(m)=f(p_{\rm init},m)$

[All rows and actual witnesses of the 25-row pattern](blp.md)

**Six finite types of relative BMS**

$s\ge2^Y$, $Y\ge H_{C[7]}(M)$, $M=\mathcal Q(8)\ge2048$; hence $s>F_{C[6]}(M-1)+1$, in particular $s>F_{C[6]}(2047)$

[Strict supremum bound, type interfaces, and numerical comparison](bms.md)


The ordinary BLP $P_{25}$ joins four seven-row copies of $p_{\rm init}$, retaining $7+6+6+6$ rows. In the BMS statement, $C=I[0][2][1]^8$ uses the fixed original IBLP fundamental sequences. Its 24-row term $C[6]$ is not this 25-row BLP. The exact rank of $C[6]$ is $\alpha_6$, where $\alpha_1=\Lambda=\lim(\mathrm{BMS})$ and $\alpha_{n+1}=\Lambda\omega^{\alpha_n}$. Numerical comparisons use the specified fundamental sequences, not just an ordinal name.

Since $r<s<N$, both results also lower-bound the spectrum index of $\Sigma$. The numerical bounds concern **natural-number spectrum indices**, not direct comparisons of uncountable critical points with large integers. No comparison between the two numerical bounds, or transfer of the BMS bound from $\eta$ to $\xi$, is asserted.

Read in this order:

1. [Common entrance and strict endpoint comparisons](endpoints.md): proofs of $\Sigma<\Theta$, the new entrance congruence with strict read guards, and $\xi<\eta<\Sigma$.
2. [BLP proof](blp.md): four source embeddings, actual seven-row witnesses, 25-row concatenation and the quantitative theorem. The final section gives a separate marked-completion corollary with its precise rule version.
3. [BMS proof](bms.md): the strict supremum bound is re-established at the new entrance, followed by the six type environments and the repository's existing whole-object compiler and numerical comparison.

Every reused mathematical input is linked to a repository manuscript or a public paper. Reading the original machine's scratch directory is unnecessary. Source hashes and editorial scope are recorded in [provenance.json](provenance.json).

The published [Lean project for the $q(5)$ bound](../lean/README.md) has a separate certification scope; it does not automatically certify the paper theorems collected here.
