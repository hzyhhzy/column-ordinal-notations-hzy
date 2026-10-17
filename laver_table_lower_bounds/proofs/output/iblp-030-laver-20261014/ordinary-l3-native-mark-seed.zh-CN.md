# 普通 L=3 种子：一次真实 native 补全及正源标记传播

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。在 ZFC + I3 下固定原来的 $\operatorname{Iter}(j)$。
本文给出八行种子的全部实际拥有者，证明其第一次 native 补全确实非空，
并证明该包通过一个**正源标记**传入下一行。一次扫描后的所有行仍有实际拥有者，
总末端仍为 $\theta_6<\kappa_4=j(\gamma_4)$。

这不是全规则闭包定理，也不是比 BMS 更强的下界；不假定这个手工种子从原始 IBLP 顶端可达。

## 1. 已有实际项与唯一新增项

沿用 $K=j_{(11)}$，以及 $K(\theta_i)=\theta_{i+2}\;(0\le i\le5)$，
$\theta_i=\kappa_i\;(0\le i\le3)$、$\theta_4=\mu$。实际 application 项为
$$
a_*=K(K),\quad b_*=K(j),\quad c_*=a_*(b_*),\quad
d_*=c_*(K),\quad e_*=d_*(j),\quad f=e_*(K),
$$
$$
g=f(K),\qquad H=g(f),\qquad
\alpha=e_*(\mu),\quad\beta=f(\kappa_2),\quad
\zeta=f(\mu),\quad\eta=H(\kappa_3).
\tag{1}
$$
所有括号均为 application。既有有限点像证明见
[实际 native／mark 桥种子](<small-period-native-mark-seed.zh-CN.md#1-实际有限项>)。
需要的结果为
$$
\begin{gathered}
\kappa_0<\kappa_1<\kappa_2<\kappa_3<\mu<\theta_5
<\beta<\alpha<\zeta<\eta<\theta_6<\kappa_4,\\
\operatorname{crit}(f)=\operatorname{crit}(H)=\kappa_0,
\qquad\operatorname{crit}(g)=\kappa_3,\\
f(\kappa_0)=\kappa_3,\quad f(\kappa_1)=\theta_5,\quad f(\kappa_2)=\beta,\\
g(\kappa_3)=\beta,\quad g(\theta_5)=\alpha,\\
H(\kappa_0)=\beta,\quad H(\kappa_1)=\alpha,\quad
H(\kappa_2)=\zeta,\quad H(\kappa_3)=\eta,\quad H(\beta)=\theta_6.
\end{gathered}
\tag{2}
$$
$\zeta<\eta<\theta_6$ 也直接来自
$\kappa_2<\kappa_3<\beta$ 取 $H$-像。

用原先补行项内部的
$$
X=e_*(j_{(3)}),\qquad \boxed{D_\beta=g(X)}.
\tag{3}
$$
已有 $\operatorname{crit}(X)=\kappa_0$、
$X(\kappa_0)=\kappa_3$、$X(\kappa_3)=\theta_5$：
最后一式使用 $\kappa_3=e_*(\kappa_2)$ 和 $j_{(3)}(\kappa_2)=\kappa_3$。
$g$ 固定 $\kappa_0$，故
$$
\operatorname{crit}(D_\beta)=\kappa_0,\qquad
D_\beta(\kappa_0)=g(X(\kappa_0))=g(\kappa_3)=\beta.
$$
又因为 $\beta=g(\kappa_3)$，
$$
\boxed{D_\beta(\beta)=g(X)(g(\kappa_3))
=g(X(\kappa_3))=g(\theta_5)=\alpha.}
\tag{4}
$$
因此 $D_\beta:\kappa_0\mapsto\beta\mapsto\alpha$ 是明确真实项，
不是根据所需有限点像另设的抽象拥有者。

## 2. 八行初始化

点表及地址为
$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,\beta,\alpha,\eta,\theta_6),
\qquad 0,1,\ldots,9.
\tag{5}
$$
第 $i$ 行的隐含端点为地址 $i+1$。第 8 行的地址 $7$ 带标记。
$$
\begin{array}{c|c|c|c|c}
i&\text{core}&L&\text{隐含端点}&\text{实际 owner}\\\hline
1&(0,1)&1&2&j\\
2&(0,1,2)&1&3&j\\
3&(0,1,2,3)&2&4&K\\
4&(0,1,2,3,4)&2&5&K\\
5&(0,1,2,3,5)&3&6&f\\
6&(0,6)&1&7&D_\beta\\
7&(0,1,3,6,7)&3&8&H\\
8&(0,1,3,6,7^*,8)&3&9&H
\end{array}
\tag{6}
$$
每一行按步长配对，都恰好是 (2)、(4) 或原来的 $j,K$ 点像。
例如第 5 行的三条边是
$f(\kappa_0)=\kappa_3$、$f(\kappa_1)=\theta_5$、$f(\kappa_2)=\beta$。
第 7 行为 $H$ 的源 $\kappa_0,\kappa_1,\kappa_3$ 三条边；
第 8 行再加 $H(\beta)=\theta_6$。所有行的 owner 临界点都等于首地址对应的点。

第 8 行标记 $7$ 的源为地址 $1$：其位置为第 5 项，$L=3$，所以配对源是
core 的第 2 项。trace 为 $(7,1)$，末个拥有者即第 7 行的 $H$。
第 8 行也用完全相同的 $H$，故这条直接接缝的 owner 身份是真正相等，
不依赖任何未经验证的截断。特别地，标记源 $1$ 严格大于首地址 $0$。

## 3. 第一次 native 包恰为 {2}

采用本地原规则 `所固定的原版 iblp.py（见 SOURCE_MANIFEST.json）`：
对 core 长度不超过 $2L$ 的行，取
$p=A[-L-1]$、$a=A[-L]$，沿
$\delta(i)=A_i[-2]$ 收集第一跳以后仍严格大于 $p$ 的源点。

第 1—6 行均不产生包：第 2、4 行长度过长而跳过；其余行第一跳不超过阈值。
第 7 行 core 为 $(0,1,3,6,7)$、$L=3$，故
$$
p=1,\qquad a=3,\qquad \delta(3)=2>1,\qquad\delta(2)=1.
$$
所以
$$
\boxed{\text{native packet}=(2).}
\tag{7}
$$
该源对应 $\kappa_2$，其真实像是 $H(\kappa_2)=\zeta$，且
$\alpha<\zeta<\eta$。因此在原地址 $7$ 与 $8$ 之间插入 $\zeta$，
新点表为
$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,
\beta,\alpha,\zeta,\eta,\theta_6).
\tag{8}
$$

原生补全是非 mid 分支，因为原 core 长度 $5<2L=6$。按代码直接计算，
替换后的第 7、8 行为
$$
\begin{array}{c|c|c|c|c}
7&(0,1,2,6,7)&3&8&H\\
8&(0,1,2,3,6,7^*,8)&4&9&H.
\end{array}
\tag{9}
$$
第 7 行的三条边是 $H(\kappa_i)\;(0\le i\le2)$；
第 8 行有四条边 $H(\kappa_i)\;(0\le i\le3)$。故两行的隐含端点
也分别恰为 $\zeta,\eta$，不只是原桥行的部分边保持。
第 1—6 行未变，且它们的隐含端点均不越过此次插入位置。

## 4. 标记把同一包传播到后续行

原第 8 行变成第 9 行；在标记处理前，它为
$$
(0,1,3,6,7^*,9),\qquad L=3,\quad\text{隐含端点 }10.
$$
native 记录为 `record[7]=[2]`。此时标记 $7$ 的 trace 仍是 $(7,1)$，
所以 mark completion 确实读取该记录，加入源地址 $2$ 及配对新地址 $8$，
并将步长增加为 $4$。得到
$$
\boxed{A_9=(0,1,2,3,6,7^*,8^*,9),\qquad L_9=4,\quad
\text{隐含端点 }10=\theta_6.}
\tag{10}
$$
其五条边恰是
$$
H(\kappa_0)=\beta,\quad H(\kappa_1)=\alpha,\quad
H(\kappa_2)=\zeta,\quad H(\kappa_3)=\eta,\quad H(\beta)=\theta_6.
$$
因此仍用原来的同一个 $H$，且总末端没有移动。

完成后的两个标记 trace 分别为 $(7,1)$、$(8,2)$，对应第 7、8 行的 owner
都是真正的 $H$。两者的源地址 $1,2$ 均为正，并且严格大于首地址 $0$。
这不是依靠零源标记而发生的退化传播。

此时新增第 7、8 行，以及最终第 9 行均已 native 饱和：它们的
$(p,a)$ 分别为 $(1,2),(2,3),(3,6)$，第一跳分别为 $1,2,0$，不超过阈值。
一次从左到右、跳过 newly native-inserted 行的实际扫描到此结束。

## 5. 精确结论及未完成部分

这份有限种子有全部实际拥有者，发生了一个非空 native 包，且同一包沿正源标记
传播到后续行；所有新增行和隐含端点都已核对，末端仍低于 $\kappa_4$。

尚未由此证明：所有后续复制地址都有定义、任意多轮补全保持同类语义、
该种子从原始顶端可达，或者它提供了结构上超过 BMS 的统一计算下界。
尤其一次成功的 native／mark 扫描不代替后续复制及标记过滤的闭包证明。

有限证书（历史参考：`ordinary_l3_native_mark_seed_certificate.py`） 实际构造 $D_\beta$，
核验八行初始化，然后直接调用原代码进行一次扫描，并核验最终九行及全部标记。
程序设 10 秒、20 行上限；不运行下降到空，不执行无界 M 搜索。
