# 第二组：BMS 动态深度反馈，直到 Λ＋ω＋1

本篇在 ZFC + I3 的同一个 $\operatorname{Iter}(j)$ 内工作，采用原 BM4 基本列和 $(\Lambda+\omega)[x]=\Lambda+(x+1)$。BMS 计数和反馈主干直接用有限嵌入构造；强化初始化另用 pIBLP 的父包定量桥。

## 1. 保留原始自然参数的三个版本

记 $\Lambda=\lim(\mathrm{BMS})$、$g=F_\Lambda$、$K=F_{\Lambda+\omega}$，并置

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil.
$$

实际长链长度 $C_{\rm line}$ 来自 Qi 的具体构造，也有纯有限递归定义：

$$
u_0(x)=x2^x,\quad u_{r+1}(x)=u_r^{\circ2^x}(x),\quad
v(x)=u_{2^x}(x),\quad w(x)=v^{\circ2^x}(x),\quad C_{\rm line}=w(w(1)).
\tag{1}
$$

**A．直接长链。** 直接初始化提供高度 $h=C_{\rm line}+2$ 的入口 fan。取

$$
z_{\rm dir}=\max\{z\ge2:\rho(z)\le C_{\rm line}+2\},
$$

则

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(z_{\rm dir})))\right).}
\tag{2}
$$

集合非空且有限，因为 $\rho$ 严格增加，(1) 立即给 $\rho(2)\le C_{\rm line}+2$。这个入口不使用 pIBLP；BMS 的计算编译仍用与 BLP 带实现相同的实际嵌入操作。

**B．较简洁的强化输入。** 令

$$
X=F_{\,2^{C_{\rm line}}+1}(C_{\rm line}),
$$

这里下标是自然数，只用经典有限层 FGH。父包初始化给

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(X)))\right).}
\tag{3}
$$

保留实际长链常数，无须换成任意选定的十进制输入。

**C．保留更多原递归结构。** 令 $H_0=u_{\omega^\omega}$，其中在 $\varepsilon_0$ 以下采用通常 Cantor 基本列：

$$
u_0(m)=m2^m,\quad u_{\alpha+1}(m)=u_\alpha^{\circ2^m}(m),\quad
u_\lambda(m)=u_{\lambda[2^m]}(m).
\tag{4}
$$

有 $H_0(1)=C_{\rm line}$。再以 $H_0$ 为底定义

$$
U_0^{H_0}=H_0,\quad
U_{\alpha+1}^{H_0}(m)=(U_\alpha^{H_0})^{\circ2^m}(m),\quad
U_\lambda^{H_0}(m)=U_{\lambda[2^m]}^{H_0}(m),
$$
$$
\widehat J=U_{\omega+1}^{H_0}(1),\qquad X_*=2^{\widehat J}.
$$

共享端口初始化进一步给

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(X_*)))\right).}
\tag{5}
$$

这些辅助递归下标不是 pIBLP 整体的序型。本篇主干对实际入口成立；(2)、(3)、(5) 代入不同的已证明入口。

## 2. BMS 计数与实际反馈接口

令 $D(h)$ 统计 $(0^h)(1^h)(1^h)$ 固定取原 BM4 $[1]$ 到空的全部步骤，$T(h)=D(h)+2$，$e_0=1,e_{n+1}=2^{e_n}$。[共享完整引理](common/bms-fixed-index.zh-CN.md)给出

$$
h\ge\rho(x),\ x\ge2\Longrightarrow
D(h)\ge e_{g(x)},\qquad T(h)\ge\rho(g(x)).
\tag{6}
$$

这来自固定指标轨道、祖先覆盖、森林编译及明确的行数预算。

固定有限背景

$$
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7<\kappa_4.
$$

高度 $h$ 的闭合相容 fan 含两排递增端口及对应 owners，具有共同低源与封口。它实现三列 BMS 种子；沿固定下降追踪，删端点的临界下标预算严格超过 $D(h)$。

具体项 $P=L_3(f)$ 满足

$$
P(\gamma_0)=a,\quad P(\gamma_1)=b,\quad P(b)=c,
$$

且有实际两段 $L(k,a,b;2)$。计算 BMS 得到位于封口下方的 $\gamma_{D(h)}$；搬运标准有限链、缩至所需长度，再统一前端插入，得到自然模板

$$
T:(h,\ \text{封口}<b)\longmapsto(D(h)+2,\ \text{封口}<c).
\tag{7}
$$

“自然”表示整个有限背景同时取允许的环境像后，同一构造适用于该环境中任意合法入口 fan；不要求入口是旧 fan 的像。这个量词保证后续调用合法。

初始长链整体取 $L_3(K)$ 像，再前端插入，提供 $3\le h\le C_{\rm line}+2$ 的入口。所有隐含边、membership 截断和闭合 owner 在[单文件基础证明](proofs/output/iblp-030-laver-20261014/q5-BMS-successor-single-file-proof.zh-CN.md)第 3–8 节；[递归 corridor](proofs/output/iblp-030-laver-20261014/small-period-recursive-corridor.zh-CN.md)给出整背景自然性。

## 3. 动态选择有限深度，保留统一出口

定义

$$
U_0=T,\qquad U_{i+1}(h)=U_i^{\circ(D(U_i(h))+1)}(h),
$$
$$
m(h)=\lfloor\log_2D(T(h))\rfloor,\qquad V(h)=U_{m(h)}(h).
\tag{8}
$$

实际项 $H=j_{(9)}(j_{(4)})$、$A_*=H(f)$ 满足

$$
c<H(a)<H(b)<H(c)<\kappa_4,\quad
A_*(\gamma_0)=r=\kappa_3,\quad A_*(\gamma_1)=u,
$$
$$
c<u,\quad A_*(u)=H(a),\qquad d=A_*(c)<H(a).
\tag{9}
$$

另存一份输入，执行一次 $T$，封口为 $C'<c$。置 $N=D(T(h))$、$m=\lfloor\log_2N\rfloor$，则 $\gamma_{2^m}\le\gamma_N<C'$。把标准 $m$-line 整体取 $A_*$ 像，得到从 $u$ 出发、最终端点低于 $A_*(C')<d$ 的实际链。沿此链逐次升级 $U_0,\ldots,U_m$，每个新出口低于当前段末端，所以所有动态有限深度统一封口在 $d$ 以下。

深度预算来自另一份已经终止的 BMS 计算，没有依赖最终输出来反选深度。环境搬运时所有 actors、根、端点一起移动，数值函数 $m(h)$ 不变。

由 (9) 可再升级整个动态模板：

$$
W(h)=V^{\circ(D(V(h))+1)}(h),\qquad q(5)>D(W(h)).
\tag{10}
$$

每次调用 $V$ 都按当时高度重选深度；最后实际出口为 $H(c)<\kappa_4$。[动态深度完整证明](proofs/output/q5-further-bound-20261014/dynamic-depth-Lambda-omega-successor.zh-CN.md)逐项检查端点、守卫和自然性。

## 4. 逐轮比较到 FGH

记 $J_i=F_{\Lambda+i}$，于是 $K(x)=J_{x+1}(x)$。(6) 归纳给出

$$
h\ge\rho(x)\Longrightarrow U_i(h)\ge\rho(J_i(x)).
\tag{11}
$$

置 $x_2=g(g(x))$。两次缓冲还给

$$
D(T(h))\ge e_{x_2},\qquad m(h)-1\ge x_2+1.
\tag{12}
$$

在 $V(h)=U_{m-1}^{\circ(D(U_{m-1}(h))+1)}(h)$ 内保留前两轮：第一轮至少到 $\rho(x_2)$，第二轮达到

$$
\rho(J_{m-1}(x_2))\ge\rho(J_{x_2+1}(x_2))=\rho(K(x_2)).
$$

令 $y=K(x_2)$。外层调用预算 $D(V(h))+1\ge y+2$。首轮 $V$ 到达 $\rho(y)$，余下至少 $y+1$ 轮逐次模拟同一条 $K$ 轨道，故

$$
W(h)\ge\rho(K^{\circ(y+1)}(y))
=\rho(F_{\Lambda+\omega+1}(y)).
$$

最后用 (6)、(10)，得到通用入口定理

$$
\boxed{h\ge\rho(x),\ x\ge2
\Longrightarrow q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(x)))\right).}
\tag{13}
$$

这里始终跟踪具体增值轨道，不要求 $U_i,V$ 或 pIBLP 的全域输入单调性。

## 5. 强化初始化的实际来源

九行实际种子 $S$ 的封口是 $\theta_6<\kappa_4$。令

$$
G(m)=f_{\rm PP}(S,m),\quad
H_0(m)=f_{\rm PP}(S[0]^5,m),\quad L=G(1).
$$

父包有限参数桥在该实际实现及所用参数上，同时证明递归定义性和 $L$-linedness。把真实链送入前端插入，得到实际入口高度 $h_*=L+2$。

纯 E 恒等式给 $H_0=u_{\omega^\omega}$。有限 transient 路径、辅助 E 及前缀抽取给

$$
L\ge H_0(C_{\rm line}),\qquad
L\ge H_0(\widehat J)\ge\widehat J\,2^{\widehat J}.
\tag{14}
$$

第一式经两轮纯 E 的有限 FGH 比较给 $h_*\ge\rho(X)$，证明 (3)；第二式给 $h_*\ge\rho(2^{\widehat J})$，证明 (5)。$\widehat J$ 来自共享 0、1、2 端口 graft 的逐行参数化代入。

完整输入依次为[九行种子](proofs/output/iblp-030-laver-20261014/same-owner-L3-sat-closure.zh-CN.md)、[父包定量桥](proofs/output/iblp-030-laver-20261014/parent-packet-quantitative-transfer.zh-CN.md)、[纯 E 归约](proofs/output/piblp-external-FGH-20261014/P4-pure-E-collapse.zh-CN.md)、[有限 FGH 初始化](proofs/output/q5-further-bound-20261014/P5-uniform-and-large-input.zh-CN.md)和[共享端口强化](proofs/output/q5-further-bound-20261014/active-port-stronger-initialization.zh-CN.md)。

## 6. 依赖范围

直接长链版 (2) 不经 pIBLP；更大输入 (3)、(5) 使用父包有限参数递归，但不假设整个父包记号良序或它与原 IBLP 同序。

本组没有证明整个原版 $I[0][2]$ 或 $R$ 的大输入 Hardy／FGH。与第一组具体数值谁大也不单凭序数下标命名判断。[逐项依赖表](PROOF_DEPENDENCIES.zh-CN.md)
