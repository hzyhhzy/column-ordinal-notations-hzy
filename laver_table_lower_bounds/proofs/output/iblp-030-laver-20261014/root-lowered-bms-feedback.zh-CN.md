# 由 BMS 计算确定行数的 Laver 表下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

本篇证明第一轮反馈。进一步的[端点搬运](<promoted-bms-feedback.zh-CN.md>)已支持第二轮，给出 $q(5)>D(D(D(h)+2)+2)$；不是在本篇的同一个 $\tau$ 窗口内直接重复。

在 I3 下，固定

$$
R_h=(0^h)(1^h)(1^h),\qquad D(h)=D_2(R_h),
$$

其中括号表示 BMS 的列，$h$ 是行数，$D_2$ 是父表表示反复取新 $[2]$ 到空的总次数，即原 BM4 反复取 $[1]$ 的次数。令

$$
g(n)=n2^n,\qquad B=g^{258}(1),\qquad H_0=B+2.
$$

结合此前的带实现及统一前端插入证明，可得

$$
\boxed{\quad
q(5)>D\bigl(D(h)+2\bigr)
\qquad(3\le h\le H_0).
\quad}
\tag{1}
$$

这里 $q(5)$ 是首行周期首次达到 32 的普通二元 Laver 表的阶参数。因此 (1) 控制的是阶数，不是元素个数。特别地，可以取 $h=11$、$h=18$，或 $h=H_0$。外层的行数是一次真正 BMS 计算的结果 $D(h)+2$，没有取对数的损失。

这是一个明确的嵌套数值下界，不是“某个有限行 BMS 的序型超过整个 BMS 极限”的断言。它没有完成原 IBLP $I[0][3][0]$ 的 Hardy 数值比较，也没有将固定指标下降次数换算成 FGH。

## 使用的已有结论

全篇在一个固定 I3 嵌入 $j$ 生成的 $\operatorname{Iter}(j)$ 内工作。$a(b)$ 表示 application；普通复合另写 $a\circ b$。$\gamma_0<\gamma_1<\cdots$ 枚举该代数的临界点，$\kappa_i=j^i(\gamma_0)$。特别地 $\kappa_0=\gamma_0$、$\kappa_1=\gamma_1$、$\kappa_2=\gamma_2$、$\kappa_3=\gamma_4$。

本证明使用三条此前已给出纸面证明的接口：

1. [带实现与删端点计数](<../iblp-laver-bms-20261013/ribbon-initialization.zh-CN.md>)：高度 $h\ge3$ 的闭合相容组、封口 $C=\gamma_r$，给出 $R_h$ 的带实现，并有 $D(h)<r$。
2. [统一前端插入](<../iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md>)：一条 $N$-lined 的 $(\kappa_2,\theta_6,Z)$ 链，给出高度 $N+2$、封口严格低于 $Z$ 的闭合相容组。
3. [已有参数输入](<../iblp-laver-bms-20261013/marked-prefix-rebase.zh-CN.md>)：在不提高原末端 $\theta_6$ 的情况下，构造 $B=g^{258}(1)$ 段的 $(\kappa_0,\kappa_1,x_B)$ 链，且 $x_B<\theta_6$。这些是实际嵌入见证，不只是某个递归函数的值。

旧的 [三行反馈](<bms-height-feedback.zh-CN.md>) 使用同一嵌入直接把链搬到根 $\kappa_2$，因而需要较强的额外端点条件。下面改为先搬到根 $\theta_6$，再将根降至 $\kappa_2$。

## 两个反馈嵌入

沿用[有限初始化](<../iblp-laver-bms-20261013/short-terminal-initialization.zh-CN.md>)的实际 application 项，记

$$
K=j_{(11)},\quad \mu=\theta_4,\quad b=K(j),\quad f=e(K).
$$

需要的点像是

$$
\begin{aligned}
b&:\kappa_2\mapsto\kappa_3\mapsto\mu\mapsto\theta_5,\\
f(\kappa_0)&=\kappa_3,\quad
f(\kappa_1)=\theta_5,\quad f(\theta_5)=\theta_6,\\
L_3&:\kappa_3\mapsto\theta_6\mapsto\theta_7,
\qquad \theta_7<\kappa_4.
\end{aligned}
\tag{2}
$$

这组 $b,f,L_3$ 正是既有证书中的项，没有根据有限点像相同而认同两个未知嵌入。定义

$$
E=L_3(K),\qquad P=L_3(f),\qquad
a=L_3(\mu),\qquad \tau=L_3(\theta_5).
\tag{3}
$$

这里将新的反馈嵌入记为 $P$，避免与 Laver 临界点计数函数 $F$ 混淆；核验程序中它的变量名是 `F`。由 (2) 和应用点像恒等式，

$$
\begin{gathered}
\theta_6<a<\tau<\theta_7<\kappa_4,\\
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,
\quad E(\theta_6)=\tau,\\
\boxed{P(\gamma_0)=\theta_6,\qquad
P(\gamma_1)=\tau,\qquad P(\tau)=\theta_7.}
\end{gathered}
\tag{4}
$$

例如，$\theta_6=L_3(\kappa_3)$，所以

$$
E(\theta_6)=L_3(K)(L_3(\kappa_3))
=L_3(K(\kappa_3))=L_3(\theta_5)=\tau.
$$

又因为 $\tau=L_3(\theta_5)$，

$$
P(\tau)=L_3(f)(L_3(\theta_5))
=L_3(f(\theta_5))=L_3(\theta_6)=\theta_7.
\tag{5}
$$

式 (5) 提供整个区间的端点控制：只要 $C<\tau$，便有 $P(C)<\theta_7<\kappa_4$。

## 将根降回 κ₂的两段链

令 $W=L_3(b)$。由 (2)，

$$
W:\kappa_2\longmapsto\theta_6\longmapsto a\longmapsto\tau.
$$

$W$ 与 $W(W)(W)$ 分别有临界序列

$$
\kappa_2\mapsto\theta_6\mapsto a,
\qquad \kappa_2\mapsto a\mapsto\tau.
$$

因此

$$
\boxed{(\kappa_2,\theta_6,\tau)\text{ 是 2-lined}.}
\tag{6}
$$

第二段可直接核对：$W(W)$ 的临界点为 $\theta_6$，它把 $\theta_6$ 送到 $a$，把 $a$ 送到 $\tau$，并固定 $\kappa_2$。对 $W$ 取它的 application，正好得到所需两条边。

若另有 $m$-lined 的 $(\theta_6,\tau,Z)$，则 [Qi 引理 2.3](https://arxiv.org/html/2501.06733v5#S2) 给出

$$
(\kappa_2,\theta_6,Z)\text{ 是 }2\cdot2^m\text{-lined}.
\tag{7}
$$

这里两段链的接口严格一致：第一条链的第二个点是第二条链的共同根，第一条链的末端是第二条链的起点。这正是原先直接搬运方案没有利用的空间。

## 由端点计数恢复足够长的链

设高度 $h\ge3$ 的闭合相容组封口为 $C=\gamma_r<\tau$。写

$$
N=D(h),\qquad m=\lfloor\log_2N\rfloor.
$$

带实现的计数接口给出 $N<r$，所以

$$
\gamma_{2^m}\le\gamma_N<C.
\tag{8}
$$

由 [Dougherty 第二篇定理 3.1(c)](https://arxiv.org/pdf/math/9503204)，各嵌入

$$
j_{(2^{2^s}-1)}:\gamma_0\mapsto\gamma_{2^s}\mapsto\gamma_{2^{s+1}}
\quad(0\le s<m)
$$

构成 $m$-lined 的 $(\gamma_0,\gamma_1,\gamma_{2^m})$ 链。将整条链取 $P$-像，并使用 (4)、(8)，得到

$$
(\theta_6,\tau,Z)\text{ 是 }m\text{-lined},
\qquad Z=P(\gamma_{2^m})<P(C)<\theta_7.
\tag{9}
$$

将 (9) 与两段链 (6) 拼接，由 (7) 得到 $2^{m+1}$-lined 的 $(\kappa_2,\theta_6,Z)$ 链。由于

$$
N<2^{m+1},
$$

可以将它缩短为恰好 $N$ 段，同时保留共同根、起点及末端。具体地，对相邻两段 $u:c\mapsto x\mapsto y$、$v:c\mapsto y\mapsto z$，用 $v(v)(u):c\mapsto x\mapsto z$ 替代；这样每次只减少一段。进行指定的有限次替换即可。

统一前端插入于是给出高度 $N+2=D(h)+2$ 的闭合相容组，封口严格低于 $Z<\theta_7<\kappa_4$。再用带实现计数及 $q(5)=F(4)+1$，得到

$$
\boxed{q(5)>D(D(h)+2).}
\tag{10}
$$

这证明了一个统一反馈引理：输入只须是封口在 $\tau$ 以下的闭合组。既没有要求计算出 $D(h)$ 的十进制表示，也没有把它当成未经证明可用的 linedness 参数。

## 既有高行数输入满足区间条件

已有的 $B$-lined 链为 $(\kappa_0,\kappa_1,x_B)$，其中 $x_B<\theta_6$。取其任意前 $h-2$ 段，$3\le h\le B+2$，端点记为 $x_{h-2}$。整体取 $E$-像后，得到

$$
(\kappa_2,\theta_6,E(x_{h-2}))
\text{ 是 }h-2\text{-lined},
$$

并且

$$
E(x_{h-2})\le E(x_B)<E(\theta_6)=\tau.
\tag{11}
$$

由统一前端插入，所构造的高度 $h$ 闭合组封口 $C_h$ 满足

$$
C_h<E(x_{h-2})<\tau.
$$

所以 (10) 对全部 $3\le h\le H_0$ 适用，证明 (1)。十八行输入还可以使用单独的十六段有限链证书（历史参考：`high_start_lining_certificate.py`），不必数值展开 $B$。

## 相对原下界的严格增加

对每个 $n\ge1$，

$$
D(n)\ge n+3.
\tag{12}
$$

证明很简单：从 $R_n$ 出发，固定展开始终保留旧末列之前的前缀；一次非零末列展开不减少列数，一次零末列删除只减少一列。因此在完整下降中，必先经过两列前缀 $(0^n)(1^n)$，此前至少走了一步。该两列式的后续下降恰好需要 $n$ 次降低末列高度和两次零列删除，共 $n+2$ 步。

于是

$$
D(D(h)+2)\ge D(h)+5>D(h).
\tag{13}
$$

特别取 $h=H_0$，新的数值下界严格超过原来已得到的 $D(H_0)$。这一步只用基本列的前缀性质和精确的两列下降，不需要未证明的“一般序位越大，固定指标计算越长”。

## 核验范围与尚未完成的部分

root_lowered_feedback_certificate.py（历史参考：`root_lowered_feedback_certificate.py`） 实际构造了十一层闭合组，并逐项核验：

- $C_{11}<\tau$；
- $P(\gamma_0)=\theta_6$、$P(\gamma_1)=\tau$、$P(\tau)=\theta_7$；
- (6) 的两段见证；
- 一次有限的链乘法 $2\cdot2^2=8$，以及保端点收缩为五段。

本次程序通过，耗时约 99 秒；保留 476 个点名、625 个嵌入项和 3,302 条点像记录。运行有 180 秒时限及点数、项数、事实数上限，没有枚举目标 BMS 下降，没有计算巨大 Laver 表；进程正常结束。

程序核验的是有限代数接口。任意 $N=D(h)$ 的推论由 (8)—(11) 的纸面论证给出；目前不是 Lean 形式化。

本轮完成了“用 BMS 计算结果决定下一轮行数”的数值步骤，但没有完成原 IBLP 030 的总目标。另须注意，反馈输出只保证封口低于 $\theta_7$，不是低于 $\tau$。不能把 (10) 在同一预算内无限重复；进一步迭代必须重新证明端点条件。下一步需要建立更高阶段的有限反馈或其他原 IBLP 定量模拟，并与原规则下选定的增长函数作真正的数值比较。
