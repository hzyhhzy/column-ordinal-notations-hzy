# pIBLP 的 P5 递归与更大的 FGH 初始化

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。假设 ZFC + I3，沿用同一个实际嵌入代数和已经证明的 pIBLP 有限参数定量桥。记

$$
G(m)=f_{\rm PP}(S,m),\qquad H(m)=f_{\rm PP}(P_4,m),\qquad C=H(1),
$$

其中 $P_i$ 是九行实际种子 $S$ 的前 $i$ 行。以下给出一个不依赖未知外部记号嵌入的新显式下界：令

$$
\Lambda=\lim(\mathrm{BMS}),\quad g=F_\Lambda,\quad
X=F_{2^C+1}(C),
$$

则

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(g(g(X))\bigr).}\tag{1}
$$

这里 $(\Lambda+\omega)[x]=\Lambda+(x+1)$。这是对原来以 $2^C$ 为初始化输入的明确数值界的严格增强，不是将一个序型严格大于 BMS 的记号嵌入 pIBLP 的证明。

## 1 已有接口

[严格 P5 前缀计算](<../piblp-q5-enhancement-20261014/audit-piblp-strict-Cline.zh-CN.md>)给出实际定义的调用

$$
L=G(1)\ge H(H(1))=H(C).\tag{2}
$$

[纯 E 闭族](<../piblp-external-FGH-20261014/P4-pure-E-collapse.zh-CN.md>)给出准确恒等式

$$
H(m)=u_{\omega^\omega}(m),\tag{3}
$$

其中

$$
u_0(m)=a(m)=m2^m,\quad
u_{\alpha+1}(m)=u_\alpha^{\circ2^m}(m),\quad
u_\lambda(m)=u_{\lambda[2^m]}(m).
\tag{4}
$$

下标小于 $\varepsilon_0$，使用通常的 Cantor 正规形基本列。式 (3) 是语法递归的全参数恒等式；(2) 中的实际调用定义性另由有限参数桥保证。

[递归 corridor 的编译](<../piblp-q5-enhancement-20261014/q5-piblp-enhanced-bound.zh-CN.md>)已经证明：实际输出长度 $L$ 供应高度 $h_*=L+2$ 的合法入口 fan，并且对

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil
$$

有

$$
h_*\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad
q(5)>F_{\Lambda+\omega}\bigl(g(g(x))\bigr).
\tag{5}
$$

因此新增证明的任务只是严格建立 $H(C)\ge\rho(X)$。

## 2 固定参数的基本列下降比较

对全部 $\alpha<\varepsilon_0$，由下标归纳，$u_\alpha(m)\ge a(m)\ge m$。对固定 $m\ge1$ 置 $n=2^m$。若

$$
\beta=\alpha[n]\quad(\alpha\text{ 为极限}),
\qquad\text{或}\qquad
\beta=\alpha-1\quad(\alpha\text{ 为后继}),
$$

则 $u_\alpha(m)\ge u_\beta(m)$。极限情形是定义；后继情形因为 $u_\beta$ 的每次迭代都不减当前数值，故迭代 $n$ 次的结果至少是第一次的结果。这个论证没有假设 $u_\beta$ 对输入单调。

当 $m\ge1$ 时 $n\ge2$，从 $\omega^\omega$ 沿上述固定 $n$ 的操作可达到 $\omega+1$：第一步是 $\omega^n$，依次到达 $\omega^{n-1},\ldots,\omega^2$，再到 $\omega n$，去掉尾部的 $n-2$ 个 $\omega$ 块到 $\omega\cdot2$，接着到 $\omega+n$，最后删去 $n-1$ 个后继。

这里“去掉尾部一个块”是一个有限固定指标下降过程：只操作该尾块，前面的 Cantor 前缀不变；$\varepsilon_0$ 以下的通常序数下降保证尾块最终为零。该过程不需要计算其巨大的实际长度。

因此

$$
H(m)=u_{\omega^\omega}(m)\ge u_{\omega+1}(m)
=u_\omega^{\circ2^m}(m).
\tag{6}
$$

## 3 只在有限层使用经典 FGH 比较

这里经典有限层约定为 $F_0(x)=x+1$、$F_{r+1}(x)=F_r^{\circ(x+1)}(x)$。对于 $x\ge2$，

$$
a(x)=x2^x\ge2x+1=F_1(x).
$$

有限自然数下标上的通常归纳给出 $F_r$ 对输入单调。再对 $r$ 归纳，使用 $2^x\ge x+1$，得到

$$
u_r(x)\ge F_{r+1}(x),\qquad r<\omega,\ x\ge2.
\tag{7}
$$

归纳步骤确实需要比较迭代，但此处只用已经证明单调的有限层 $F_{r+1}$：若当前 $u_r$ 轨道输入不小于相应 $F_{r+1}$ 轨道输入，点态下界 (7) 和后者的单调性保持该关系。这里没有使用 $u_r$、$H$ 或 $G$ 的未知全域输入单调性。

在 $x=C\ge2$ 处，令 $n=2^C$。由 $\omega[n]=n$，

$$
y_1=u_\omega(C)=u_n(C)\ge F_{n+1}(C)=X.
\tag{8}
$$

又因 $u_\omega(y)\ge a(y)$，以及 $a$ 对输入严格递增，第二次迭代满足

$$
y_2=u_\omega(y_1)\ge a(y_1)\ge a(X)\ge\rho(X).
\tag{9}
$$

最后一个不等式对整数 $X\ge2$ 成立：$\lceil\log_2(X+2)\rceil\le X$，故 $\rho(X)\le2X+3\le X2^X$。式 (6) 的迭代次数至少为 2，其余迭代不减当前值。因此

$$
\boxed{L\ge H(C)\ge\rho\bigl(F_{2^C+1}(C)\bigr).}\tag{10}
$$

把 (10) 代入 (5) 即得 (1)。

由于有限层下标单调性给 $X\ge F_2(C)>2^C$，[BMS 对角和有限后继层的输入严格单调性](<../piblp-q5-enhancement-20261014/audit-BMS-diagonal-input-monotonicity.zh-CN.md>)证明 (1) 的右端严格超过原来的 $F_{\Lambda+\omega}(g(g(2^C)))$。

如果希望去掉文献常数 $C$，已有 $C>4t$、$t=F_3(256)$，所以也可保守写成

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(g(g(F_{2^t}(t)))\bigr),
\qquad t=F_3(256).}\tag{11}
$$

这里仍只使用有限 FGH 层的输入和下标单调性来比较两个初始化整数。

## 4 P5 的全参数可用块结构

另一个可以重复使用的准确结构是：令 $Q_l$ 为 $l$ 对以下两行组成的图案，首两行固定为 $01:1$、$012:1$：

$$
(0,1,2,2i+1):2,\quad
(0,1,2,2i+1,2i+2):2\ \text{并标记 }2i+1,
\qquad1\le i\le l.
$$

于是 $Q_1=P_4$。P5 的 E 阈值为 3；它的第 $m$ 次辅助 raw 复制恰将现有块数加倍，因此对所有 $m\ge0$，

$$
\boxed{E_{P_5}(m)=Q_{2^m}.}\tag{12}
$$

逐坐标看，每轮源块从地址 3 开始，共有 $2l$ 行；共享的 0、1、2 固定，其余地址统一增加 $2l$，marks 按同一平移保留。这里不进行 PP 或 native 扫描。

$Q_{l+1}$ 的删尾前缀 $R_{l+1}$ 是 $Q_l$ 接一条 E-successor，完整 guard 通过。实际定义的参数处有

$$
f_{\rm PP}(Q_{l+1},m)
\ge f_{\rm PP}(R_{l+1},m)
=[x\mapsto f_{\rm PP}(Q_l,x)]^{\circ2^m}(m).
\tag{13}
$$

可安全提取一个全参数单调下包络。定义

$$
B_0(m)=m2^m,\qquad B_{r+1}(m)=B_r^{\circ2^m}(m).
$$

每个 $B_r$ 均单调且不小于输入。用 (13) 和本次 E-successor 调用的有限定义证书归纳，

$$
f_{\rm PP}(Q_l,m)\ge B_{l-1}(m),\qquad
\boxed{G(m)\ge B_{2^m-1}(m)}
\tag{14}
$$

在 $G(m)$ 有实际证书的每个参数成立。式 (14) 并未宣称任意手写 $Q_l$ 在固定 cap 下可取任意 linedness 参数。

若想将式 (14) 的 $B_0$ 换为 $H$，还必须补充 $H$ 的输入单调性或另给一个单调下包络。点态不等式不足以在未知非单调函数之间直接传递多次迭代；本篇没有作这个替换。式 (1) 的主结论完全不依赖它。

## 5 结论范围

新增结论是 (10) 的初始化缓冲、(1) 的明确 FGH 下界，以及 (12) 至 (14) 的统一 P5 接口。没有由纯 E 的 $\varepsilon_0$ 控制族推断 pIBLP 整体很小，也没有将这次初始化增强称为一个严格超 BMS 序型的 FGH 控制。真正的外部大记号嵌入和其 FGH 编译仍需保持 transient 复制与全局 E 端口。

有限块证书（历史参考：`P5-block-audit.py`）核验 m=0 至 6 的全部 E 数组恒等式，以及 39 个块数的后继 cut 与完整 guard，共 124 项检查，峰值 130 行、775 个条目、约 0.02 秒。它不求值任何巨大的数值函数；第 2 至第 3 节的全称结论由上述纸面归纳给出。
