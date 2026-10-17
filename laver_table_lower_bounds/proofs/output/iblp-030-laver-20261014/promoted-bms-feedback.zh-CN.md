# 同一 Laver 周期阈值下的两次 BMS 行数反馈

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

在 I3 假设下，沿用[第一轮反馈](<root-lowered-bms-feedback.zh-CN.md>)的定义

$$
D(h)=D_2((0^h)(1^h)(1^h)),\qquad T(h)=D(h)+2,
\qquad H_0=g^{258}(1)+2,\quad g(n)=n2^n.
$$

这里 $h$ 是 BMS 行数；$D_2$ 是父表新指标反复取 $[2]$ 到空的步数，等于原 BM4 反复取 $[1]$ 的步数。可将行数反馈再做一次，得到

$$
\boxed{q(5)>D(T(T(h)))=D\bigl(D(D(h)+2)+2\bigr)
\qquad(3\le h\le H_0).}
\tag{1}
$$

两次反馈都在固定 $\operatorname{Iter}(j)$ 内，封口最终仍低于 $\kappa_4$。这不是任意多次反馈的结论，也没有建立原 IBLP $I[0][3][0]$ 的 Hardy 下界。

## 允许起点移动的反馈引理

称 $(P,a,b,c)$ 满足本引理的条件，是指

$$
\begin{gathered}
\theta_6\le a<b<c<\kappa_4,\qquad
P(\gamma_0)=a,\quad P(\gamma_1)=b,\quad P(b)=c,\\
(\kappa_2,a,b)\text{ 是 2-lined}.
\end{gathered}
\tag{2}
$$

若高度 $h\ge3$ 的闭合相容组封口为 $C<b$，则存在高度 $T(h)$ 的闭合相容组，其封口严格小于 $c$。

证明与第一轮相同，但允许 $a>\theta_6$。令 $N=D(h)$、$m=\lfloor\log_2N\rfloor$。带实现的删端点计数给出 $\gamma_N<C$。Dougherty 的标准链是 $m$-lined 的 $(\gamma_0,\gamma_1,\gamma_{2^m})$。将它取 $P$-像，得到 $m$-lined 的 $(a,b,Z)$，其中

$$
Z=P(\gamma_{2^m})<P(C)<P(b)=c.
$$

与 (2) 的两段链相乘，得到 $2^{m+1}>N$ 段的 $(\kappa_2,a,Z)$ 链。保端点收缩至 $N$ 段，再用[统一前端插入](<../iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md>)，得到高度 $N+2=T(h)$、封口低于 $Z<c$ 的组。统一插入原本就允许起点 $a\ge\theta_6$，所以这里没有新加未经证明的插入规则。

一个方便的搬运条件如下。若 $H$ 固定 $\kappa_2$，且

$$
c\le H(b),\qquad H(c)<\kappa_4,
\tag{3}
$$

那么

$$
\bigl(H(P),H(a),H(b),H(c)\bigr)
\tag{4}
$$

也满足 (2)。两段链整体取 $H$-像；$H$ 固定 $\gamma_0,\gamma_1,\kappa_2$，所以三个点像等式由 application 恒等式得到。且第一轮的输出封口低于 $c\le H(b)$，可以输入第二轮。条件 (3) 是真正需要检查的端点预算，不能由 $c<\kappa_4$ 自动推出。

## 比原有端点界更强的一条比较

仍写 $K=j_{(11)}$、$\mu=\theta_4$，令

$$
\nu=j_{(9)}(\gamma_3),\qquad \theta_8=j_{(9)}(\kappa_3).
$$

需要证明

$$
\boxed{\theta_7<\nu<\theta_8<\kappa_4.}
\tag{5}
$$

后两项来自严格单调性及既有的 $\theta_8<\kappa_4$。第一项可由 membership 截断直接推出，先前的五层有限证书（历史参考：`five_row_certificate.py`）也用过这个比较。

为避免与列高度函数 $D$ 混淆，以下辅助嵌入记作 $V,A,B,Q$：

$$
V=j_{(10)}(j_{(10)}),\quad
A=j_{(9)}(j_{(3)})=V(j_{(10)}),\quad
B=V(j),\quad Q=j_{(10)}(K).
$$

LD 恒等式给出

$$
Q=V(K)=A(B).
\tag{6}
$$

这里的等号是 application 项恒等式，不是根据有限点像认同嵌入。由 $\operatorname{crit}(V)=\kappa_2$，有 $B\equiv_{\kappa_2}j$。同时

$$
A(\kappa_1)=\mu,\qquad A(\kappa_2)=\nu.
$$

搬运截断后，(6) 给出 $Q\equiv_\nu A(j)$。因为 $\kappa_3<\mu=A(\kappa_1)$，

$$
A(j)(\kappa_3)<A(j)(A(\kappa_1))
=A(\kappa_2)=\nu.
\tag{7}
$$

因此可在严格低于截断的位置读取 $Q(\kappa_3)=A(j)(\kappa_3)<\nu$。另一方面，Dougherty 第一篇第 5 节的 $K\equiv_\mu j\circ j$ 搬运为

$$
Q=j_{(10)}(K)\equiv_{\theta_8}K\circ K.
$$

使用已知 $K(K(\kappa_3))=\theta_7<\theta_8$，得到 $Q(\kappa_3)=\theta_7$。结合 (7) 即证 (5)。这一推导只使用已有初始化的点像和截断规则；来源见 [Dougherty 的原文](https://arxiv.org/pdf/math/9205202)。

## 搬运第一轮反馈

第一轮已构造

$$
P=L_3(f),\qquad a=\theta_6,\qquad
b=\tau=L_3(\theta_5),\qquad c=\theta_7.
$$

它满足 (2)，且 $\mu<\theta_6<\tau<\theta_7$。现在取

$$
\boxed{H=j_{(9)}(j_{(4)}).}
\tag{8}
$$

由 $j_{(4)}:\kappa_2\mapsto\gamma_3\mapsto\kappa_3$，

$$
\operatorname{crit}(H)=\mu,\qquad H(\mu)=\nu,\qquad H(\nu)=\theta_8.
\tag{9}
$$

故 $H$ 固定 $\kappa_2$。用 (5) 和 $\mu<\tau$，可得

$$
\theta_7<\nu=H(\mu)<H(\tau),
\qquad H(\theta_7)<H(\nu)=\theta_8<\kappa_4.
\tag{10}
$$

这正是 (3)。对任意既有高度 $h\le H_0$ 的输入，第一轮给出高度 $T(h)$、封口低于 $\theta_7$ 的组；第二轮使用 (4)，给出高度 $T(T(h))$、封口低于 $H(\theta_7)<\kappa_4$ 的组。带实现的计数再给出 (1)。

因 $D(n)\ge n+3$，新下界还严格超过第一轮：

$$
D(T(T(h)))\ge D(T(h))+5>D(T(h)).
$$

无需假设固定指标下降长度对一般序数比较单调。

## 核验与原 IBLP 目标的距离

promoted_feedback_certificate.py（历史参考：`promoted_feedback_certificate.py`） 对 (5)—(10) 和搬运后的两段链作有限代数核验。本次运行通过，用时约 1.8 秒，65 个点名、120 个嵌入项、910 条点像记录；设有 35 秒及继承的点数、项数、事实数上限。它不计算 $D(h)$，不枚举 BMS 完整下降，也不将有限测试当作一般反馈引理的证明。

两轮构造只给出 (1)，没有提供每个原 IBLP 后继展开所需的见证。尤其不能把两轮或任意固定轮反馈直接称作 $I[0][3][0]$ 级增长。要完成总目标，仍须将原规则的整尾复制与补全定量模拟进保端点过程，或证明另一个已实现过程支配原规则的明确增长函数。
