# 递归 corridor 的 FGH 数值转换审计

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

在已有 corridor 端点定理与 BMS 强缓冲估计成立的前提下，可以严格推出

$$
\boxed{q(5)>F_{\Lambda+\omega}\!\left(F_\Lambda(F_\Lambda(F_3(256)))\right).}
$$

这里约定 $(\Lambda+\omega)[x]=\Lambda+(x+1)$。这个明确数值严格超过此前的
$F_{\Lambda+1}(F_\Lambda(F_\Lambda(F_3(256))))$。证明不使用
$F_\Lambda$ 对输入的单调性，也不从记号序型直接推断计算长度。

## 已有输入

从 [短搬运端点证明](<../iblp-030-laver-20261014/small-period-endpoint-Sf.zh-CN.md>)
第4节使用以下已经建立的自然数结论。对已有入口 fan 所支持的高度 $h\ge3$，令

$$
R_0=T,\qquad
R_{i+1}(h)=R_i^{\circ(D(R_i(h))+1)}(h),\qquad
m(h)=\lfloor\log_2 D(T(h))\rfloor,
$$

则

$$
q(5)>D(R_{m(h)+1}(h)). \tag{1}
$$

从 [强计数缓冲](<../iblp-030-laver-20261014/nested-bms-FGH-bound.zh-CN.md>)
使用

$$
\begin{gathered}
e_0=1,\quad e_{n+1}=2^{e_n},\quad
\ell(x)=\lceil\log_2(x+2)\rceil,\quad \rho(x)=x+3+\ell(x),\\
x\ge2,\ h\ge\rho(x)
\quad\Longrightarrow\quad
D(h)\ge e_{F_\Lambda(x)},\quad T(h)\ge\rho(F_\Lambda(x)). \tag{2}
\end{gathered}
$$

最后使用已有初始化

$$
t=F_3(256),\qquad h_0=C_{\rm line}+2\ge\rho(t), \tag{3}
$$

其中高度 $h_0$ 的入口 fan 是此前实际构造的有限见证。以下只对这个合法入口应用(1)。

## 有限后继层的缓冲模拟

定义

$$
G_0(x)=F_\Lambda(x),\qquad G_{i+1}(x)=G_i^{\circ(x+1)}(x).
$$

因此 $G_i(x)=F_{\Lambda+i}(x)$。良基归纳及有限迭代给出

$$
G_i(x)\ge x+1. \tag{4}
$$

对于 $x\ge1$，迭代次数 $x+1\ge2$，所以

$$
G_{i+1}(x)>G_i(x). \tag{5}
$$

这里仅使用 $G_i(y)>y$：一次调用后得到 $G_i(x)$，第二次调用的结果严格大于这个数。
这不需要比较 $G_i$ 在两个不同输入处的值。

**缓冲引理。** 对所有有限 $i$、$x\ge2$ 和 $h\ge\rho(x)$，

$$
R_i(h)\ge\rho(G_i(x)). \tag{6}
$$

对 $i$ 归纳。零层是(2)。设第 $i$ 层成立，置

$$
N=D(R_i(h))+1,\qquad h_j=R_i^{\circ j}(h),\quad
y_j=G_i^{\circ j}(x).
$$

通过反复应用归纳假设，得到所有有限 $j$ 上的同一不变量

$$
h_j\ge\rho(y_j). \tag{7}
$$

特别是 $R_i(h)\ge\rho(G_i(x))$。将(2)应用于输入 $G_i(x)$ 得

$$
N\ge e_{G_0(G_i(x))}+1\ge x+1. \tag{8}
$$

又由(4)，$y_j$ 随 $j$ 严格增加；由 $\rho$ 的普通整数单调性，

$$
R_{i+1}(h)=h_N\ge\rho(y_N)
\ge\rho(y_{x+1})=\rho(G_{i+1}(x)).
$$

这证明(6)，并明确处理了额外迭代。整个证明没有假定 $R_i$ 或 $G_i$ 对输入单调。

## 用计算出的层数保留两次预热后的输入

以下固定 $h=h_0$，并记

$$
x_0=t,\quad x_1=G_0(t),\quad x_2=G_0(G_0(t)),\quad m=m(h).
$$

由(2)两次应用，

$$
T(h)\ge\rho(x_1),\qquad D(T(h))\ge e_{x_2}.
$$

因 $e_{x_2}=2^{e_{x_2-1}}$，

$$
m\ge e_{x_2-1}\ge x_2+1. \tag{9}
$$

最后一个初等估计对 $x_2\ge4$ 成立：$e_3=16\ge5$，并由
$e_{n+1}=2^{e_n}$ 归纳。这里 $t\ge2$，故 $x_2\ge4$。

现在展开最外层

$$
R_{m+1}(h)=R_m^{\circ N}(h),\qquad N=D(R_m(h))+1.
$$

第一轮由(6)给出 $R_m(h)\ge\rho(G_m(t))$。由(5)、$m\ge1$ 以及
$G_1(t)=G_0^{\circ(t+1)}(t)$，有

$$
G_m(t)\ge G_1(t)\ge G_0^{\circ2}(t)=x_2. \tag{10}
$$

这里最后一个比较沿同一 $G_0$ 轨道进行，只用每步严格增值。
所以第一轮已经使当前高度至少为 $\rho(x_2)$。又由(2)，$N\ge2$。

从第二轮开始，每一轮都可以把(6)重新用于**固定目标输入 $x_2$**，得到

$$
R_m^{\circ j}(h)\ge\rho(G_m(x_2))\qquad(2\le j\le N). \tag{11}
$$

归纳所需条件保持成立，因为 $G_m(x_2)>x_2$，故右端至少为 $\rho(x_2)$。
将(2)最后一次用于(11)，结合(1)，得到

$$
q(5)>D(R_{m+1}(h))\ge e_{G_0(G_m(x_2))}>G_m(x_2). \tag{12}
$$

再由(5)、(9)，

$$
G_m(x_2)\ge G_{x_2+1}(x_2)
=F_{\Lambda+\omega}(x_2).
$$

因此

$$
\boxed{q(5)>F_{\Lambda+\omega}\!\left(F_\Lambda(F_\Lambda(F_3(256)))\right).} \tag{13}
$$

## 与原数值界的严格比较

旧右端是 $G_1(x_2)$。新右端是 $G_{x_2+1}(x_2)$。因为 $x_2+1>1$，
反复使用同一输入上的(5)得到

$$
F_{\Lambda+\omega}(x_2)=G_{x_2+1}(x_2)>G_1(x_2)
=F_{\Lambda+1}(x_2). \tag{14}
$$

所以(13)在此处的具体输入上确实严格更强。严格性只使用有限后继层的点态增长，
没有用未经证明的 $F_\Lambda$ 输入单调性。

这是一项已有递归 corridor 的数值强化；它没有把 pIBLP 的所有指标良序、
完整 $I[0][2]$ 嵌入或某个结构性超 BMS 记号当作已证前提。
