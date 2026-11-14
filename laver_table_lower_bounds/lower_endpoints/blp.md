# Complete BLP bounds at the smaller endpoint $\xi$ · [中文](blp.zh-CN.md)

Assume ZFC + I3 and retain the notation of the [common entrance](endpoints.md). We construct an actual realization of the ordinary 25-row BLP $P_{25}$ with endpoint exactly $\xi$. Thus, if $\xi=\gamma_r$,

**Equation (1)**

$$
\boxed{\begin{gathered}
r\ge2^{f(P_{25},8)},\\
r\ge2^{\Psi^{\circ4}(8)},\qquad\Psi(m)=f(p_{\rm init},m).
\end{gathered}}
$$

These are independent bounds, not an assertion that $f(P_{25},8)=\Psi^{\circ4}(8)$. The common entrance proves

**Equation (2)**

$$
\xi=((J_{11}(J_3))(J_7))(\kappa_2)
<\eta<J_{13}(\gamma_{16})<J_{11}(\kappa_3).
$$

Ordinary BLPs, BLSs, $f$, and linedness use [Qi v5, Section 2](https://arxiv.org/html/2501.06733v5#S2). We give witnesses for every row rather than inferring realizability from a pattern's shape or row count.

## 1. A lower four-stage transporter

Take $T=J=e(g_2)$ and $H=T(j)$, where $e=b_0(j)$ and $b_0=q(J_7)$. The common entrance gives

$$
\operatorname{crit}T=\kappa_1,\qquad
T(\kappa_1)=\mu,\quad T(\mu)=\xi,\quad
T(g)(\kappa_1)=\chi.
$$

Since $g\equiv_{\kappa_2}j$,

$$
T(g)\equiv_{T(\kappa_2)}H.
$$

The strict read guard comes from $H$ itself:

$$
H(\kappa_1)<H(\mu)=T(\kappa_2).
$$

Consequently $H(\kappa_1)=\chi$. Also

**Equation (3)**

$$
H(\kappa_0)=\mu,\qquad
H(\mu)=T(\kappa_2),\qquad
H(T(\kappa_2))=T(\kappa_3).
$$

All subsequent stages use this $T$, with endpoint $T(\mu)=\xi<\Sigma$, rather than the higher-ending $q(J_{10})$.

## 2. Four actual source embeddings

Set

$$
\begin{gathered}
D_4=J_{14},\qquad D_{16}=J_{65534},\\
R_0=j,\quad R_1=D_4(j),\quad R_2=D_{16}(j),\quad R_3=D_{16}(R_1).
\end{gathered}
$$

[Dougherty II, Theorem 7.2(c) and Lemma 7.1](https://arxiv.org/pdf/math/9503204) provide the required finite scaling:

$$
D_4(\gamma_m)=\gamma_{4m}\ (m\le4),\qquad
D_{16}(\gamma_m)=\gamma_{16m}\ (m\le16).
$$

The four critical-sequence prefixes are therefore

| $i$ | Prefix for $R_i$ |
|---:|---|
| 0 | $\gamma_0\mapsto\gamma_1\mapsto\gamma_2\mapsto\gamma_4$ |
| 1 | $\gamma_0\mapsto\gamma_4\mapsto\gamma_8\mapsto\gamma_{16}$ |
| 2 | $\gamma_0\mapsto\gamma_{16}\mapsto\gamma_{32}\mapsto\gamma_{64}$ |
| 3 | $\gamma_0\mapsto\gamma_{64}\mapsto\gamma_{128}\mapsto\gamma_{256}$ |

Let $s_i=4^i$ and let $h_i$ be the spectrum-index function of $R_i$. The table gives $h_i(0)=s_i$ and $h_i(s_i)=2s_i$; Lemma 7.1 yields

$$
2s_i\ge s_i+s_i(h_i(1)-s_i).
$$

Strict increase gives the opposite constraint $h_i(1)\ge s_i+1$, so $R_i(\kappa_1)=\gamma_{s_i+1}$.

We also need a finite-quotient fact: if $u(\gamma_0)=v(\gamma_0)=\gamma_s$, then $u\equiv_{\gamma_{s+1}}v$. Indeed, $\operatorname{crit}(u(j))=\gamma_s$, so its residue in $P_{s+1}$ is $2^s$. Right multiplication by the generator adds one modulo $2^{s+1}$; hence the residue of $u$ is $2^s-1$, and likewise for $v$. Ordinary composition is allowed because the quotient correspondence in [Dougherty II, Theorem 2.6](https://arxiv.org/pdf/math/9503204) includes the two-operation algebra $P_j$. It follows that

**Equation (4)**

$$
R_i\equiv_{\gamma_{s_i+1}}R_{i-1}^{\circ3}\qquad(1\le i\le3).
$$

Let $H_i=T(R_i)$ and define

$$
\begin{gathered}
a_i=H_i(\kappa_0)=T(\gamma_{s_i}),\qquad b_i=H_i(\kappa_1),\\
c_i=H_i(a_i),\quad d_i=H_i(b_i),\quad e_i=H_i(c_i).
\end{gathered}
$$

Then $c_i=T(\gamma_{2s_i})$, $e_i=T(\gamma_{4s_i})$, and

$$
\kappa_0<\kappa_1<a_i<b_i<c_i<d_i<e_i.
$$

Transport (4) along $T$. The strict guard
$b_i=H_i(\kappa_1)<H_i(\mu)=T(\gamma_{s_i+1})$
allows the reading

**Equation (5)**

$$
b_i=H_{i-1}^{\circ3}(\kappa_1).
$$

## 3. Exact low bridges for every stage

Set $G_0=g$ and, for $i=0,1,2$, define

$$
C_i=H_i(H_i),\qquad G_{i+1}=C_i(C_i(G_i)).
$$

Inductively $G_i:\kappa_0\mapsto\kappa_1\mapsto a_i\mapsto b_i$. The base case is (3) and the common entrance. For the step, $C_i$ has critical point $a_i$, fixes $\kappa_0,\kappa_1$, and satisfies

$$
C_i(a_i)=c_i,\quad C_i(b_i)=d_i,\quad C_i(c_i)=e_i,\quad
C_i(d_i)=H_i^{\circ3}(\kappa_1).
$$

Two applications transport the bridge to
$\kappa_0\mapsto\kappa_1\mapsto e_i\mapsto H_i^{\circ3}(\kappa_1)$.
Since $e_i=a_{i+1}$, equation (5) gives the next stage with its low endpoints and every edge preserved.

## 4. All seven witnesses of $p_{\rm init}$

Fix one stage and write its points as $(\alpha,\beta,a,b,c,d,e)$ and its embeddings as $G,H$. They satisfy

$$
G:\alpha\mapsto\beta\mapsto a\mapsto b,\qquad
H:\alpha\mapsto a\mapsto c\mapsto e,\qquad H(\beta)=b,\ H(b)=d.
$$

Define the actual application terms

$$
D=(H(H))(H(G)),\quad E=D(H),\quad F=E(G),\quad L=F(H).
$$

Successive covariance gives

$$
\begin{gathered}
D:c\mapsto d\mapsto e,\\
E(\alpha)=a,\ E(\beta)=b,\ E(a)=d,\ E(b)=e,\\
F:a\mapsto b\mapsto d\mapsto e.
\end{gathered}
$$

Since $F$ fixes $\alpha,\beta$, we have $L(\alpha)=b$, $L(\beta)=d$, $L(b)=F(c)$, and $L(d)=e$. Let $u=L(a)$ and $v=F(c)$. Strict monotonicity gives $d<u<v<e$.

On the nine points $(\alpha,\beta,a,b,c,d,u,v,e)$, the rows are

| Row addresses | Step length | Actual owner |
|---|---:|---|
| $(0,1,2)$ | 1 | $G$ |
| $(0,1,2,3)$ | 1 | $G$ |
| $(0,1,2,3,4)$ | 2 | $H$ |
| $(0,1,2,3,4,5)$ | 2 | $H$ |
| $(0,1,2,3,5,6)$ | 3 | $L$ |
| $(0,1,2,3,5,6,7)$ | 3 | $L$ |
| $(0,1,2,3,5,6,7,8)$ | 3 | $L$ |

Each owner has critical point $\alpha$, and every step-length edge follows from the displayed images. This is the fixed $p_{\rm init}$; its last three rows share $L$. The first three points, endpoint, and any supplied linedness parameter are preserved.

## 5. Concatenation into the original 25 rows

For stage $i$, use

$$
\varphi_i(0)=0,\qquad\varphi_i(1)=1,\qquad
\varphi_i(t)=t+6i\quad(t\ge2).
$$

Keep all seven rows of the first stage; omit only the virtual first row of each later stage, adding six rows each. Since $e_i=a_{i+1}$, the seams agree exactly. New internal points lie strictly within their stage's old gaps. The last two addresses in every row remain its global row number and the next point number. Section 4 supplies all owners, giving $P_{25}$ with the following endpoints.

| Completed stages | Rows | Actual endpoint |
|---:|---:|---|
| 1 | 7 | $T(\gamma_4)$ |
| 2 | 13 | $T(\gamma_{16})$ |
| 3 | 19 | $T(\gamma_{64})$ |
| 4 | 25 | $T(\gamma_{256})=T(\mu)=\xi$ |

The initial triple remains $(\kappa_0,\kappa_1,\mu)$, equipped with the actual 8-line of the common entrance.

## 6. Quantitative bounds and subsequent operations

[Qi, Theorem 2.25](https://arxiv.org/html/2501.06733v5#S2) turns this BLS and its initial 8-line into an $f(P_{25},8)$-line ending at $\xi$. Critical-point counting (Lemma 2.5 there) gives

$$
\gamma_{\,2^{f(P_{25},8)}}\le\xi=\gamma_r,
$$

the first bound in (1). Alternatively, apply the theorem successively to the four $p_{\rm init}$ stages, retaining the actual triple and line after each application. This gives a $\Psi^{\circ4}(8)$-line and the second bound.

The index bound at $\xi$ is non-strict. The strict inequality $N>2^{f(P_{25},8)}$ follows only after using $\xi<\Sigma=\gamma_N$.

The quantitative theorem covers the entire ordinary $f$ recursion, not just the initial static pattern. Ordinary completion, $M$, $E$, and deletion are implemented by the BLS semantics and preserve or lower the endpoint. No enormous descent needs to be executed. Extra marked completion is not automatic from this argument.

## 7. A separate marked-completion corollary

The precise version in the repository's [finite-parameter marked-BLP quantitative bridge](../proofs/output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md) gives an independent bound at the same $\xi$. Its rules are ordinary row types, short copying, the correct paper guard, natural-cutoff mark semantics, a left-to-right frozen scan, and the paper's auxiliary three-point $E(m)$.

In each local $p_{\rm init}$ block, mark 3 in row 4, mark 5 in row 6, and mark 5 and 6 in row 7. Renumber with the same $\varphi_i$, obtaining $\widehat P_{25}$ with 16 marks. The local traces are $(3,1)$, $(5,1)$, $(5,1)$, and $(6,2)$: proper one-factor traces with positive sources. Carrier and unique factor are the same actual $H_i$ or $L_i$, so global equality supplies the mark semantics.

After removing each implicit next point, denote the row core by $A_r$, its step by $\ell_r$, and set $p(r)=A_r[-\ell_r-1]$, $e(r)=A_r[-\ell_r]$, $B(r)=A_r[-2]$. The required $\operatorname{Sat}$ inequality is $B(e(r))\le p(r)$ on every eligible row. The first row has $(p,e,B(e))=(0,1,0)$. Each block adds local eligible rows 3, 5, and 6 with

$$
(p,e,B(e))=(1,\varphi_i(2),1),\quad
(1,\varphi_i(2),1),\quad
(\varphi_i(2),\varphi_i(3),\varphi_i(2)).
$$

All 13 inequalities are equalities. The original 8-line and ordinary edges are unchanged, satisfying the bridge's certificate hypotheses. Its natural-cutoff, parallel-packet and scan-closure lemmas show that native and marked completion preserve the endpoint, $E(m)$ preserves it, and cut lowers it. Thus its specified function $f_\star$ satisfies

$$
\boxed{r\ge2^{f_\star(\widehat P_{25},8)}.}
$$

The full recursive induction uses the linked quantitative bridge and [local mark lemmas](../common/natural-marks.zh-CN.md), not merely a finite certificate check. No inequality $f_\star\ge f$ or extension to arbitrary long-row, full-tail original IBLP is asserted.
