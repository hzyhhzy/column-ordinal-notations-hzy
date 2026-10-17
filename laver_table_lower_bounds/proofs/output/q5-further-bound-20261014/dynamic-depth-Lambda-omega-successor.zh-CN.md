# 动态深度模板把 q5 下界提高到 Lambda 加 omega 加一

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。在与既有下界相同的 ZFC + I3 假设下，固定同一个
$\operatorname{Iter}(j)$。设 $\Lambda=\lim(\mathrm{BMS})$、
$g=F_\Lambda$。采用
$(\Lambda+\omega)[x]=\Lambda+(x+1)$，可以证明

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(
F_{\Lambda+\omega}\bigl(g(g(2^{C_{\rm line}}))\bigr)\right).}
\tag{A}
$$

这严格提高了此前同一输入上的 $F_{\Lambda+\omega}$ 下界。
新增步骤是把“先依输入选择有限模板深度”本身变成自然模板，随后将这个
动态深度模板沿实际长链反复执行。它没有假定原 IBLP 02 或完整 Y 序列
已嵌入 pIBLP。

## 所用的实际端点与计数接口

沿用
[短搬运端点证明](<../iblp-030-laver-20261014/small-period-endpoint-Sf.zh-CN.md>)
和
[递归 corridor](<../iblp-030-laver-20261014/small-period-recursive-corridor.zh-CN.md>)。
为免与 pIBLP 种子 $S$ 混淆，本文把实际搬运嵌入记为 $H$：

$$
\begin{gathered}
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7<\kappa_4,\\
H=j_{(9)}(j_{(4)}),\qquad c<H(a)<H(b)<H(c)<\kappa_4,\\
A=H(f),\qquad r=\kappa_3,\qquad u=H(\theta_5),\\
A(\gamma_0)=r,\quad A(\gamma_1)=u,\quad
k<r<a<c<u,\quad A(u)=H(a).
\end{gathered}
\tag{1}
$$

$H$ 固定 $\kappa_0,\kappa_1,k$。所有式中的括号均表示
application；不把普通复合冒充 application 项。

令 $D(h)$ 为三列 BMS 矩阵
$(0^h)(1^h)(1^h)$ 反复取原 BM4 $[1]$ 到空的总步数，
$T(h)=D(h)+2$。既有自然模板 $T$ 把入口封口低于 $b$ 的 fan
变为高度 $T(h)$、封口低于 $c$ 的 fan。

另沿用强缓冲估计

$$
e_0=1,\quad e_{n+1}=2^{e_n},\qquad
\rho(x)=x+3+\lceil\log_2(x+2)\rceil,
$$

$$
h\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad
D(h)\ge e_{g(x)},\qquad T(h)\ge\rho(g(x)).
\tag{2}
$$

这些接口的来源与 pIBLP 初始化
$h_*=f_{\rm PP}(S,1)+2\ge\rho(2^{C_{\rm line}})$，见
[上一轮完整推导](<../piblp-q5-enhancement-20261014/q5-piblp-enhanced-bound.zh-CN.md>)
第 1 至 4 节。以下先对任意已有实际入口 fan 的高度 $h$ 证明，最后才取
$h=h_*$。

## 动态有限深度有一个统一的较低出口

定义整数函数

$$
U_0=T,\qquad
U_{i+1}(h)=U_i^{\circ(D(U_i(h))+1)}(h),
\qquad m(h)=\lfloor\log_2D(T(h))\rfloor,
$$

$$
V(h)=U_{m(h)}(h).
\tag{3}
$$

关键强化不是旧的数值界，而是以下**统一出口**：$V$ 是入口 $b$、
出口

$$
d=A(c)<A(u)=H(a)
\tag{4}
$$

的自然模板。

证明如下。给定高度 $h$ 的实际入口 fan，另外保存一份副本并执行一次
$T$，其封口记为 $C<c$。令 $N=D(T(h))$、$m=\lfloor\log_2N\rfloor$。
带计数给 $\gamma_{2^m}\le\gamma_N<C$。全局 Dougherty 的
$m$-lined $(\gamma_0;\gamma_1,\ldots,\gamma_{2^m})$ 链逐点、逐拥有者
取 $A$-像，得到

$$
(r;u,\ldots,A(\gamma_{2^m})),\qquad
A(\gamma_{2^m})<A(C)<A(c)=d.
\tag{5}
$$

用它的各段逐次升级 $U_0$，得到 $U_m$。每次新出口低于当前链段的
末端，因而最后出口仍严格低于 $d$。若 $m=0$，直接用 $U_0=T$
即可，因为 $c<u<A(c)=d$。整个过程只使用已经构造的一条有限链，
没有要求固定端点下存在任意长度的链。

自然性同样成立。对于任何固定 $\gamma_0,\gamma_1$ 的环境嵌入 $Q$，
搬运后的背景使用 $Q(A),Q(r),Q(u),Q(c)$。输入 fan 可以是全局
$\operatorname{Iter}(j)$ 中任意符合守卫的 fan，无须是某份旧 fan 的
逆像。全局带计数仍给 $\gamma_N<C<Q(c)$，故链的终点低于
$Q(A)(Q(c))=Q(d)$。数值函数 $m(h)$ 保持不变，因 fan 高度不变。
于是 (4) 是整背景自然模板，而非仅一项偶然的输入输出见证。

## 再升级一次动态模板

既有 corridor 升级引理说：若自然模板 $F$ 的入口为 $b$、出口为
$d'\ge c$，而实际嵌入 $R$ 固定 $\kappa_0,\kappa_1,k$，满足
$d'<R(a)$，则

$$
\mathcal U(F)(h)=F^{\circ(D(F(h))+1)}(h)
\tag{6}
$$

有入口 $b$、出口 $R(c)$ 的自然实现。

在这里取 $F=V$、$R=H$。由 (4) 有 $d<H(a)$，而
$H(c)<\kappa_4$。因此

$$
W(h)=V^{\circ(D(V(h))+1)}(h)
\quad\Longrightarrow\quad q(5)>D(W(h)).
\tag{7}
$$

注意 $W$ 每次调用 $V$ 都重新根据当前高度选择深度。
它不同于一次性确定 $m(h)$ 后始终调用固定 $U_{m(h)}$ 的旧模板
$U_{m(h)+1}(h)$。这一区别正是新增的增长来源。

## 逐级缓冲模拟

记

$$
J_i(x)=F_{\Lambda+i}(x),\qquad
K(x)=F_{\Lambda+\omega}(x)=J_{x+1}(x).
$$

已有有限层归纳给

$$
h\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad U_i(h)\ge\rho(J_i(x)).
\tag{8}
$$

该归纳只反复使用 (2) 及
$J_{i+1}(x)=J_i^{\circ(x+1)}(x)$。各函数严格增值；在同一输入处，
$J_{i+1}(x)>J_i(x)$（$x\ge1$）。不需要假定这些函数对输入单调。

若 $h\ge\rho(x)$，两次 (2) 给

$$
D(T(h))\ge e_{g(g(x))},\qquad
m(h)\ge e_{g(g(x))-1}\ge g(g(x))+1\ge x+1.
\tag{9}
$$

这里 $g(g(x))\ge4$。故由 (8)、同一输入上的有限层比较，

$$
\boxed{h\ge\rho(x),\ x\ge2
\quad\Longrightarrow\quad V(h)\ge\rho(K(x)).}
\tag{10}
$$

这把动态深度模板与 $F_{\Lambda+\omega}$ 真正接上，而不是从符号上的
“可变有限层”直接猜测 FGH 级别。

## 在动态模板内部保留一次极限层预热

固定 $h\ge\rho(x)$、$x\ge2$，置

$$
x_2=g(g(x)),\qquad m=m(h).
$$

由 $x_2\ge4$ 和初等塔估计 $e_{x_2-1}\ge x_2+2$，(9) 实际给出

$$
m-1\ge x_2+1.
\tag{11}
$$

展开 $V(h)=U_m(h)=U_{m-1}^{\circ M}(h)$，其中
$M=D(U_{m-1}(h))+1$。第一轮由 (8) 给

$$
U_{m-1}(h)\ge\rho(J_{m-1}(x))
\ge\rho(J_1(x))\ge\rho(x_2).
\tag{12}
$$

最后一步来自 $J_1(x)=g^{\circ(x+1)}(x)$ 的同一严格增值轨道。
由 (2)，$M\ge2$。第二轮重新将 (8) 用于固定输入 $x_2$，得到

$$
U_{m-1}^{\circ2}(h)\ge\rho(J_{m-1}(x_2))
\ge\rho(J_{x_2+1}(x_2))=\rho(K(x_2)).
\tag{13}
$$

后续每轮仍可对固定输入 $x_2$ 使用 (8)，因为 (13) 右端至少为
$\rho(x_2)$。所以令 $y=K(x_2)$，便有

$$
V(h)\ge\rho(y),\qquad N=D(V(h))+1\ge e_{g(y)}+1\ge y+2.
\tag{14}
$$

在 $W(h)=V^{\circ N}(h)$ 中，首轮之后至少还剩 $y+1$ 轮。
反复使用基本缓冲 (10)，跟踪同一条严格增值的 $K$ 轨道，得到

$$
W(h)\ge\rho\bigl(K^{\circ(N-1)}(y)\bigr)
\ge\rho\bigl(K^{\circ(y+1)}(y)\bigr).
\tag{15}
$$

置 $Y=K^{\circ(y+1)}(y)=F_{\Lambda+\omega+1}(y)$，由 (2)、(7) 得

$$
\boxed{q(5)>D(W(h))\ge e_{g(Y)}>Y
=F_{\Lambda+\omega+1}\!\left(F_{\Lambda+\omega}(g(g(x)))\right).}
\tag{16}
$$

取 pIBLP 已经实际初始化的 $h=h_*$、$x=2^{C_{\rm line}}$，即得到 (A)。
如果沿用已审计的 BMS 对角输入严格递增性质，也可把其中的
$2^{C_{\rm line}}$ 放松成 $2^{F_3(256)}$。

同一输入 $z\ge1$ 上，

$$
F_{\Lambda+\omega+1}(z)=K^{\circ(z+1)}(z)>K(z),
$$

并且 $F_{\Lambda+\omega+1}(z)>z$。因此 (A) 的右端严格超过此前
$F_{\Lambda+\omega}(g(g(2^{C_{\rm line}})))$；这一比较甚至不需要
比较不同输入处的 FGH 值。

## 进一步升级的端点缺口

新增模板 $W$ 的统一出口是 $H(c)$，不是低于 $H(a)$。同一个
$H$ 因而不能直接再次使用。一个充分的新资源是实际 application 项
$R\in\operatorname{Iter}(j)$，固定 $\kappa_0,\kappa_1,k$，满足

$$
H(c)<R(a),\qquad R(c)<\kappa_4.
\tag{17}
$$

现有严格点像表没有给出 (17)。普通复合 $H\circ H$ 的候选端点
$H(H(c))$ 仅知位于 $\theta_8$ 与 $H(\theta_8)$ 之间，
而后者不低于 $\kappa_4$，不能由此确认新出口。还必须另行验证其
拥有者确实属于所要求的环境代数，不能把 application $H(H)$ 与
普通复合混同。

本篇没有据此宣布 $F_{\Lambda+\omega\cdot2}$ 或 Y 级的 FGH 下界；
(A) 仅使用已经闭合的实际有限端点和自然模板引理。
