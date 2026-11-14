# Common entrance and strict endpoint comparisons · [中文](endpoints.zh-CN.md)

Assume ZFC + I3 throughout. Conventions and final bounds are in the [overview](README.md). This paper gives actual embedding constructions and both required strict comparisons; finite experiments or bounds at a higher endpoint do not replace them.

## 1. Source identities and truncation

Write $e\equiv_\tau f$ for membership-truncation equivalence. The supremum arguments $\alpha$ used here are limit ordinals, so $e(<\alpha)=\sup_{\beta<\alpha}e(\beta)$ agrees with Dougherty's strict-supremum convention. Use

$$
e(f)\circ e=e\circ f,\quad
\operatorname{crit}(e(f))=e(\operatorname{crit}f),\quad
e(f(g))=e(f)(e(g)).
$$

Truncations can be lowered, transported as $h(e)\equiv_{h(\tau)}h(f)$, and preserved in the first argument of application. Reading ordinal images requires a previously established output strictly below the cutoff on at least one side.

Put

$$
K=J_{11},\quad A_0=J_{12},\quad B_0=J_{13},\quad E_0=J_{14},
\quad\mu=\gamma_{256},\quad\chi=K(\gamma_3),
$$

$$
\Sigma=B_0(\gamma_{16}),\qquad\Theta=K(\kappa_3)=A_0(\mu).
$$

The following small-term data come from [Dougherty I, Section 5, printed pages 21–24](https://arxiv.org/pdf/math/9205202#page=21); exact $\gamma$ indices also use [Dougherty II, Sections 7–8](https://arxiv.org/pdf/math/9503204).

| Embedding | Required data |
|---|---|
| $A_0$ | $\operatorname{crit}A_0=\kappa_2$, $\kappa_2\mapsto\kappa_3\mapsto\mu$ |
| $B_0$ | $\kappa_0\mapsto\kappa_1\mapsto\kappa_3\mapsto\mu$, $B_0(\kappa_2)=\gamma_{16}$ |
| $E_0$ | $\kappa_1\mapsto\kappa_3\mapsto\gamma_{16}$ |
| $J_7$ | $\kappa_0\mapsto\gamma_3$, $\kappa_1\mapsto\kappa_3$, $\kappa_2\mapsto\mu$ |
| $K$ | $\kappa_0\mapsto\kappa_2$, $\kappa_1\mapsto\kappa_3$, $\kappa_2\mapsto\mu$ |

Also $K\equiv_\mu j\circ j$ and $A_0\equiv_\mu j(J_2)$. Set

$$
s_1=j(<\kappa_1),\qquad s_2=j(<\kappa_2).
$$

The same source gives

**Equation (1)**

$$
\begin{gathered}
\kappa_1<s_1<\kappa_2,\qquad
j(<s_1)<\gamma_3<j(s_1)<s_2<\kappa_3,\\
K\!\upharpoonright V_{\kappa_2}=(j\circ j)\!\upharpoonright V_{\kappa_2}.
\end{gathered}
$$

Supremum covariance is used at actual image points only. Generated critical points are regular cardinals; for example, $\kappa_2<\mu=K(\kappa_2)$ gives $K(<\kappa_2)<\mu$.

## 2. Proof that $\chi<\Sigma<\Theta$

Let $u=B_0(s_1)=A_0(j(s_1))$. Since $s_1<\kappa_2$, we have $u<\gamma_{16}$. From $A_0=K(j)$, $B_0=A_0(j)$, and (1),

**Equation (2)**

$$
\begin{aligned}
\chi&=K(\gamma_3)<K(j(s_1))=A_0(K(s_1))\\
&=A_0(j(j(s_1)))=B_0(A_0(j(s_1)))\\
&=B_0(u)<B_0(\gamma_{16})=\Sigma.
\end{aligned}
$$

Next let $t=A_0(s_2)=B_0(<\kappa_3)$. Since $\kappa_3=A_0(\kappa_2)$, this is supremum covariance at an actual image. Strict monotonicity and the regularity of $\mu$ give

$$
\gamma_{16}<t<\mu.
$$

Apply the same formula at $t=A_0(s_2)$:

**Equation (3)**

$$
\begin{aligned}
B_0(<t)&=A_0(j(<s_2))=A_0(K(<\kappa_2))\\
&<A_0(\mu)=\Theta.
\end{aligned}
$$

The middle equality uses the images below $\kappa_2$ supplied by $K\equiv_\mu j\circ j$ and cofinality of the relevant suprema. As $t$ is a limit ordinal above $\gamma_{16}$,

**Equation (4)**

$$
\boxed{\Sigma=B_0(\gamma_{16})<B_0(<t)<\Theta=J_{11}(\kappa_3).}
$$

Also $\gamma_3>\kappa_2$ gives $\mu=K(\kappa_2)<\chi$. No new lower-endpoint construction has been used, so these comparisons do not depend circularly on its transport.

## 3. A new entrance with the same low background

Define

$$
\begin{gathered}
P=B_0(B_0),\quad U=A_0(A_0),\quad X=B_0(E_0),\\
q=X(A_0),\qquad q_{\rm old}=K(J_3)=U(A_0).
\end{gathered}
$$

Transport $A_0\equiv_\mu j(J_2)$ along $A_0$ and use LD:

**Equation (5)**

$$
\begin{aligned}
U&\equiv_\Theta A_0(j(J_2))\\
&=B_0(A_0(J_2))=B_0(P)=P(P).
\end{aligned}
$$

Since $B_0=A_0(j)\equiv_{\kappa_2}j$, transport along $B_0$ yields $P\equiv_{\gamma_{16}}E_0$. Moreover,

$$
P(\gamma_{16})=\Sigma,\qquad P(E_0)=B_0(E_0)=X.
$$

Transporting this truncation along $P$ gives $P(P)\equiv_\Sigma X$. Combining (4), (5), and preservation in the first argument of application,

**Equation (6)**

$$
\boxed{q\equiv_\Sigma q_{\rm old}.}
$$

The critical sequence of $X$ starts $\kappa_3\mapsto\mu\mapsto\Sigma$, and $X$ fixes $\kappa_2$. Thus

$$
\operatorname{crit}q=\kappa_2,\qquad
q(\kappa_2)=\mu,\qquad q(\mu)=\Sigma.
$$

The old entrance satisfies $q_{\rm old}(\kappa_3)=\chi$. The already proved guard $\chi<\Sigma$ permits reading (6):

**Equation (7)**

$$
\boxed{q(\kappa_3)=\chi.}
$$

In contrast, $q(\mu)=\Sigma<\Theta=q_{\rm old}(\mu)$, so (6) is not global equality.

## 4. Two smaller endpoints and their short expressions

Let $b_0=q(J_7)$. Application covariance and the fact that $q$ fixes $\kappa_1$ give

$$
\begin{aligned}
b_0(\kappa_1)&=q(J_7(\kappa_1))=\chi,\\
b_0(\mu)&=q(J_7(\kappa_2))=q(\mu)=\Sigma.
\end{aligned}
$$

Define $\xi=b_0(\kappa_2)$ and $\eta=b_0(\gamma_3)$. Apply strict monotonicity of $b_0$ to $\kappa_1<\kappa_2<\gamma_3<\kappa_3<\mu$:

**Equation (8)**

$$
\chi<\xi<\eta<b_0(\kappa_3)<\Sigma<\Theta.
$$

By (6), $b_0\equiv_\Sigma q_{\rm old}(J_7)$. The established guards $\xi,\eta<\Sigma$ allow both readings, hence

**Equation (9)**

$$
\boxed{\begin{aligned}
\xi&=((J_{11}(J_3))(J_7))(\kappa_2),\\
\eta&=((J_{11}(J_3))(J_7))(\gamma_3).
\end{aligned}}
$$

This proves the complete chain, including both construction endpoints below $J_{13}(\gamma_{16})$ and that endpoint below $J_{11}(\kappa_3)$.

## 5. Shared low background

Put

$$
\begin{gathered}
g=q(j),\quad g_i=q(J_i),\quad\delta=q(\gamma_3),\\
e=b_0(j),\quad J=e(g_2),\quad k=J(g),\quad x=e(g).
\end{gathered}
$$

LD gives $J=x(x)$. The actual profiles are

**Equation (10)**

$$
\begin{gathered}
\mu<\delta<\chi<\xi<\eta<\Sigma,\\
g:\kappa_0\mapsto\kappa_1\mapsto\mu\mapsto\chi,\\
\operatorname{crit}J=\kappa_1,\quad J(\kappa_1)=\mu,\quad J(\mu)=\xi,\\
k(\kappa_0)=\mu,\quad k(\kappa_1)=\chi,\quad k(\mu)=\xi.
\end{gathered}
$$

The equality $k(\kappa_1)=\chi$ requires a truncation reading. Since $\operatorname{crit}e=\delta$, we have $e(g)\equiv_\delta g$. Transport along $J$ and use LD:

$$
e(g_3)=J(e(g))\equiv_{J(\delta)}J(g)=k.
$$

The guard is $e(g_3)(\kappa_1)=e(\delta)=\chi<\xi=J(\mu)<J(\delta)$. Lowering the truncation also yields $k\equiv_\delta g_3$.

Finally fix an actual 8-line $(\kappa_0;\kappa_1,\mu)$. Here $\mathcal L(a;b,c;m)$ means that $b=x_0<\cdots<x_m=c$ and embeddings $h_i$ in the same algebra satisfy

$$
\operatorname{crit}h_i=a,\qquad h_i(a)=x_i,\qquad h_i(x_i)=x_{i+1}.
$$

The embeddings $j,J_3$ provide $\mathcal L(\kappa_0;\kappa_1,\kappa_3;2)$. Their $B_0$-image provides $\mathcal L(\kappa_1;\kappa_3,\mu;2)$. Line multiplication takes $\mathcal L(a;b,c;m)$ and $\mathcal L(b;c,d;n)$ to $\mathcal L(a;b,d;m2^n)$, giving $2\cdot2^2=8$. This constructs actual witnesses rather than inferring linedness from $\mu=\gamma_{256}$. [Qi, Lemma 2.3](https://arxiv.org/html/2501.06733v5#S2)

Both subsequent papers use this background and the same 8-line: [BLP](blp.md), [BMS](bms.md).
