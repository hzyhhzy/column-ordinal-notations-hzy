# 共同入口与严格端点比较 · [English](endpoints.md)

全篇假设 ZFC + I3。约定及两条最终下界见[总览](README.zh-CN.md)。以下给出实际嵌入构造，特别证明所需的两段比较，而不以有限实验或某个较高端点的下界代替它们。

## 1. 基础资料与截断约定

写 $e\equiv_\tau f$ 表示 membership 截断等价。本篇的上确界参数 $\alpha$ 均为极限序数，故 $e(<\alpha)=\sup_{\beta<\alpha}e(\beta)$，与 Dougherty 的严格上确界约定一致。使用

$$
e(f)\circ e=e\circ f,\quad
\operatorname{crit}(e(f))=e(\operatorname{crit}f),\quad
e(f(g))=e(f)(e(g)).
$$

截断等价可降低截断点，可沿实际嵌入 $h$ 搬运为 $h(e)\equiv_{h(\tau)}h(f)$，也可在 application 的第一参数中保留。读取序数点像时，必须已有至少一侧的输出严格小于截断点。

置

$$
K=J_{11},\quad A_0=J_{12},\quad B_0=J_{13},\quad E_0=J_{14},
\quad\mu=\gamma_{256},\quad\chi=K(\gamma_3),
$$

$$
\Sigma=B_0(\gamma_{16}),\qquad\Theta=K(\kappa_3)=A_0(\mu).
$$

所需的公开小项资料如下。点像及截断见 [Dougherty I，第 5 节，印刷页 21–24](https://arxiv.org/pdf/math/9205202#page=21)；准确的 $\gamma$ 下标也使用 [Dougherty II，第 7–8 节](https://arxiv.org/pdf/math/9503204)。

| 嵌入 | 所需资料 |
|---|---|
| $A_0$ | $\operatorname{crit}A_0=\kappa_2$，$\kappa_2\mapsto\kappa_3\mapsto\mu$ |
| $B_0$ | $\kappa_0\mapsto\kappa_1\mapsto\kappa_3\mapsto\mu$，$B_0(\kappa_2)=\gamma_{16}$ |
| $E_0$ | $\kappa_1\mapsto\kappa_3\mapsto\gamma_{16}$ |
| $J_7$ | $\kappa_0\mapsto\gamma_3$，$\kappa_1\mapsto\kappa_3$，$\kappa_2\mapsto\mu$ |
| $K$ | $\kappa_0\mapsto\kappa_2$，$\kappa_1\mapsto\kappa_3$，$\kappa_2\mapsto\mu$ |

另有 $K\equiv_\mu j\circ j$、$A_0\equiv_\mu j(J_2)$。令

$$
s_1=j(<\kappa_1),\qquad s_2=j(<\kappa_2).
$$

同一来源给出

**式 (1)**

$$
\begin{gathered}
\kappa_1<s_1<\kappa_2,\qquad
j(<s_1)<\gamma_3<j(s_1)<s_2<\kappa_3,\\
K\!\upharpoonright V_{\kappa_2}=(j\circ j)\!\upharpoonright V_{\kappa_2}.
\end{gathered}
$$

上确界协变仅在实际像点使用。生成临界点是正则基数；例如 $\kappa_2<\mu=K(\kappa_2)$ 给 $K(<\kappa_2)<\mu$。

## 2. 严格证明 $\chi<\Sigma<\Theta$

令 $u=B_0(s_1)=A_0(j(s_1))$。因为 $s_1<\kappa_2$，有 $u<\gamma_{16}$。由 $A_0=K(j)$、$B_0=A_0(j)$ 和 (1)，

**式 (2)**

$$
\begin{aligned}
\chi&=K(\gamma_3)<K(j(s_1))=A_0(K(s_1))\\
&=A_0(j(j(s_1)))=B_0(A_0(j(s_1)))\\
&=B_0(u)<B_0(\gamma_{16})=\Sigma.
\end{aligned}
$$

再令 $t=A_0(s_2)=B_0(<\kappa_3)$。这里 $\kappa_3=A_0(\kappa_2)$，故该等式是 application 在实际像点的上确界公式。由严格单调性和 $\mu$ 的正则性，

$$
\gamma_{16}<t<\mu.
$$

将同一公式用在 $t=A_0(s_2)$，得到

**式 (3)**

$$
\begin{aligned}
B_0(<t)&=A_0(j(<s_2))=A_0(K(<\kappa_2))\\
&<A_0(\mu)=\Theta.
\end{aligned}
$$

中间等式由 $K\equiv_\mu j\circ j$ 在 $\kappa_2$ 以下的点像以及上确界的共尾性得到。$t$ 是极限序数且 $\gamma_{16}<t$，故

**式 (4)**

$$
\boxed{\Sigma=B_0(\gamma_{16})<B_0(<t)<\Theta=J_{11}(\kappa_3).}
$$

另由 $\gamma_3>\kappa_2$ 有 $\mu=K(\kappa_2)<\chi$。以上尚未使用新的低端点构造，因而不循环依赖后面的搬运。

## 3. 有相同低背景、但更小终点的新入口

定义

$$
\begin{gathered}
P=B_0(B_0),\quad U=A_0(A_0),\quad X=B_0(E_0),\\
q=X(A_0),\qquad q_{\rm old}=K(J_3)=U(A_0).
\end{gathered}
$$

沿 $A_0$ 搬运 $A_0\equiv_\mu j(J_2)$，再用 LD，得

**式 (5)**

$$
\begin{aligned}
U&\equiv_\Theta A_0(j(J_2))\\
&=B_0(A_0(J_2))=B_0(P)=P(P).
\end{aligned}
$$

由于 $B_0=A_0(j)\equiv_{\kappa_2}j$，沿 $B_0$ 搬运给
$P\equiv_{\gamma_{16}}E_0$。又

$$
P(\gamma_{16})=\Sigma,\qquad P(E_0)=B_0(E_0)=X.
$$

沿 $P$ 搬运上述截断，得到 $P(P)\equiv_\Sigma X$。结合 (4)、(5) 并在 application 的第一参数中保留截断，

**式 (6)**

$$
\boxed{q\equiv_\Sigma q_{\rm old}.}
$$

由第 1 节的点像，$X$ 的临界序列开始于
$\kappa_3\mapsto\mu\mapsto\Sigma$，且 $X$ 固定 $\kappa_2$。因此

$$
\operatorname{crit}q=\kappa_2,\qquad
q(\kappa_2)=\mu,\qquad q(\mu)=\Sigma.
$$

旧入口有 $q_{\rm old}(\kappa_3)=\chi$。因为已独立证明 $\chi<\Sigma$，可以由 (6) 严格读取

**式 (7)**

$$
\boxed{q(\kappa_3)=\chi.}
$$

注意 $q(\mu)=\Sigma<\Theta=q_{\rm old}(\mu)$；(6) 绝不是全局等式。

## 4. 两个更小端点及其短表达式

令 $b_0=q(J_7)$。application 协变和 $q$ 固定 $\kappa_1$ 给

$$
\begin{aligned}
b_0(\kappa_1)&=q(J_7(\kappa_1))=\chi,\\
b_0(\mu)&=q(J_7(\kappa_2))=q(\mu)=\Sigma.
\end{aligned}
$$

定义 $\xi=b_0(\kappa_2)$、$\eta=b_0(\gamma_3)$。直接对
$\kappa_1<\kappa_2<\gamma_3<\kappa_3<\mu$ 使用 $b_0$ 的严格单调性，得到

**式 (8)**

$$
\chi<\xi<\eta<b_0(\kappa_3)<\Sigma<\Theta.
$$

由 (6)，$b_0\equiv_\Sigma q_{\rm old}(J_7)$。因为 $\xi,\eta<\Sigma$ 已经证明，两个点像均可合法读取，从而

**式 (9)**

$$
\boxed{\begin{aligned}
\xi&=((J_{11}(J_3))(J_7))(\kappa_2),\\
\eta&=((J_{11}(J_3))(J_7))(\gamma_3).
\end{aligned}}
$$

这证明总览中的完整严格比较链，既包括两个构造端点小于 $J_{13}(\gamma_{16})$，也包括后者小于 $J_{11}(\kappa_3)$。

## 5. 两条构造共用的低背景

令

$$
\begin{gathered}
g=q(j),\quad g_i=q(J_i),\quad\delta=q(\gamma_3),\\
e=b_0(j),\quad J=e(g_2),\quad k=J(g),\quad x=e(g).
\end{gathered}
$$

LD 给 $J=x(x)$。直接点像为

**式 (10)**

$$
\begin{gathered}
\mu<\delta<\chi<\xi<\eta<\Sigma,\\
g:\kappa_0\mapsto\kappa_1\mapsto\mu\mapsto\chi,\\
\operatorname{crit}J=\kappa_1,\quad J(\kappa_1)=\mu,\quad J(\mu)=\xi,\\
k(\kappa_0)=\mu,\quad k(\kappa_1)=\chi,\quad k(\mu)=\xi.
\end{gathered}
$$

其中 $k(\kappa_1)=\chi$ 需要截断读取：$e$ 的临界点为 $\delta$，因此 $e(g)\equiv_\delta g$。沿 $J$ 搬运并用 LD，

$$
e(g_3)=J(e(g))\equiv_{J(\delta)}J(g)=k.
$$

已知 $e(g_3)(\kappa_1)=e(\delta)=\chi<\xi=J(\mu)<J(\delta)$，故读取合法。降低截断后又得 $k\equiv_\delta g_3$。

最后固定一个实际的 8-line $(\kappa_0;\kappa_1,\mu)$。这里 $\mathcal L(a;b,c;m)$ 表示存在 $b=x_0<\cdots<x_m=c$ 及同一代数的嵌入 $h_i$，满足

$$
\operatorname{crit}h_i=a,\qquad h_i(a)=x_i,\qquad h_i(x_i)=x_{i+1}.
$$

$j,J_3$ 给出 $\mathcal L(\kappa_0;\kappa_1,\kappa_3;2)$；取 $B_0$ 像给 $\mathcal L(\kappa_1;\kappa_3,\mu;2)$。链乘法 $\mathcal L(a;b,c;m)$ 与 $\mathcal L(b;c,d;n)$ 合成 $\mathcal L(a;b,d;m2^n)$，故得到 $2\cdot2^2=8$。这是实际见证的构造，而不是从 $\mu=\gamma_{256}$ 反推链长。[Qi，Lemma 2.3](https://arxiv.org/html/2501.06733v5#S2)

两篇后续证明分别使用这一低背景及同一条 8-line：[BLP](blp.zh-CN.md)、[BMS](bms.zh-CN.md)。
