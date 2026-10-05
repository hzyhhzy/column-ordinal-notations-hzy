# X 与候选 C：加法封闭使事件秩归约不损失序数值

> 归档研究稿／Archived research manuscript — 2026-10-06。来源：`output/y1342585-multirow-20260929/ADDITIVE-CLOSURE-AND-EXACT-EVENT-RANK.zh-CN.md`。
> 本稿是有明确历史前提的纸面论证或局部接口，不是新增的 Lean 定理，也没有因归档而完成独立整链复核。文中“本轮／最新／目标”指原稿阶段；请以[现状总览](../../../README.zh-CN.md)为准。
> Proof/status guide: [English](../../../README.md). 实验／失败路线不单独展开；有删节时，原行区间及前后 SHA-256 见[清单](../../../manifest.json)。必要前提、适用范围和未完成方向仍保留。


**后续结论：** [新的标准上界](RENEWABLE-TWO-ROW-PORT.zh-CN.md) 已证明 `X<C`，排除本页候选。
本页两端分别的精确事件秩归约不变；因此它们的事件秩共尾值也严格不等，而非等待证明相同。

2026-09-29。接 [事件秩归约](EVENT-RANK-REDUCTION.zh-CN.md)。
**新结果：分别精确保留两端的序数值。没有证明两端事件树相等或可嵌入，因而仍未证明 X=C。**

仍记

\[
X=Y(1,3,4,2,5,8,5),\qquad
C=\operatorname{SRPD}(1,2,4,8,4,1,2,9,38,4,12,2),
\]

\[
\lambda_Y=\rho_Y(X),\quad \lambda_R=\rho_R(C),\quad
\alpha=\rho_Y(1,3),\quad \beta=\rho_Y(134258),\quad
\kappa=\alpha^2+\beta.
\]

这里 C 是实际标准候选，不是已经找出的等值项。
采用既有的下降秩、封闭分量序数和及早先的 β 校准。
未 Lean 形式化，未重审所有旧引理。

## 1. Y 基本列之间有比 β 间隔更强的关系

设 \(s_n=X[n]\)、\(\sigma_n=\rho_Y(s_n)\)。
原第一步公式是

\[
s_n=(1,3,4)\frown
\mathop{\frown}_{b=0}^{n}
  (2^{b+1},\,2^{b+2}+1,\,3\cdot2^{b+1}+2).
\tag{1}
\]

因此 sₙ₊₁ 删除最后两项，恰好成为

\[
s_n\frown(2^{n+2}).
\tag{2}
\]

在此仅作真实同宽局部下降 D，把末值减到2：

\[
s_{n+1}\ \longrightarrow^+\ R_n:=s_n\frown(2).
\tag{3}
\]

它的 D 次数恰是 \(2^{n+2}-2\)，是确定的有限整数。
论证使用原局部减一引理，而非猜测某条无限下降会终止。
实现用有限父 DAG 直接算终点及成本，不逐次跑大数次数。

还有一个更具体的父表描述：sₙ₊₁ 的最后一个普通根沿底祖先链到达
固定零基第3列 c₀，后者值为2，父表为 [0]、无高旗标。
把实际末根返回到 c₀ 的完整别名，正好实现(3)，并保留整个 sₙ。

### Rₙ 的基本列完全可读

sₙ 中只有最前一个1；其余项都≥2。
所以 Rₙ 的新末2是普通底行控制，唯一底父是最前的1，
没有高旗标。整个 sₙ 是坏块，原规则直接给

\[
R_n[k]=\underbrace{s_n\frown\cdots\frown s_n}_{k+1\text{份}}
\quad(k\ge0).
\tag{4}
\]

以1分开的 Y 分量互不干扰，秩为序数和；故

\[
\rho_Y(R_n)=\sigma_n\cdot\omega.
\]

(3)至少有两次原删除，所以是严格后代。于是得到统一结论

\[
\boxed{\sigma_n\cdot\omega<\sigma_{n+1}.}
\tag{5}
\]

这不是目标的最终对应式；它用于控制极限的闭包性质，
不是用“乘 ω”的小扩展冒充 X 的识别。

## 2. 两端都是加法主项

由 X 的基本列秩定义及严格递增性，

\[
\lambda_Y=\sup_n\sigma_n.
\]

若 ξ、η<λ_Y，取同一个 n 使二者都<σₙ，则

\[
\xi+\eta\le\sigma_n\cdot2
<\sigma_n\cdot\omega
<\sigma_{n+1}<\lambda_Y.
\]

所以 λ_Y 对两个较小序数的加法封闭，即是非零加法不可分序数。
因其无限，存在 δ_Y>0 使 \(\lambda_Y=\omega^{\delta_Y}\)。

SRPD 端已有 偏移填行及共尾证明（未随本次收录的来源：`output/y1342585-multirow-20260929/OFFSET-COFINAL-CANDIDATE.zh-CN.md`）：

\[
\lambda_R=\sup_{d\ge6}\mu_d,\qquad
\mu_d\omega\le\mu_{d+1},\qquad \mu_d<\mu_{d+1}.
\tag{6}
\]

同样，两个小于 λ_R 的序数都可被同一个 μ_d 控制，
它们的和<μ_dω≤μ_d₊₁<λ_R。于是

\[
\lambda_R=\omega^{\delta_R}\quad(\delta_R>0).
\tag{7}
\]

本节不是把两个加法主项认作相等；这样的序数有无穷多个。

## 3. 消除小左乘因子的准确理由

用既有

\[
\Lambda=\rho_Y(1342584)
=\rho_R(1,2,4,8,4,1,2,9,38,4,4).
\]

Λ 是严格大于 β 的最小 epsilon 数。
α<β，所以由 Λ 的有限加乘闭包有

\[
0<\kappa=\alpha^2+\beta<\Lambda.
\tag{8}
\]

原标准下降给 Λ<λ_Y；候选 C 严格大于 J12，而 J12 严格下降到上述 SRPD 的 Λ，
所以也有 Λ<λ_R。这些是不依赖本稿新归约的旧大小关系。

一般地，若 λ=ω^δ≥Λ，则 δ≥Λ：
若 δ<Λ，由 Λ 是 epsilon 数可得 ω^δ<Λ，矛盾。
设 κ 的 Cantor 正规形首指数为 ξ。κ<Λ 给 ξ<Λ。
由于 δ≥Λ、Λ 加法不可分，

\[
\xi+\delta=\delta,\qquad
\kappa\,\omega^\delta=\omega^{\xi+\delta}=\omega^\delta.
\]

因此

\[
\boxed{\kappa\lambda_Y=\lambda_Y,\qquad
       \kappa\lambda_R=\lambda_R.}
\tag{9}
\]

**不是**只因 κ<λ 就抹去左因子；第2节的加法主项性质和第3节的 epsilon 屏障都在使用。

## 4. 一条精确事件秩推论

沿用 [一般事件秩定理](EVENT-RANK-REDUCTION.zh-CN.md)：
若所有无事件段秩 r(s)<κ，则

\[
\varepsilon(s)\le\rho(s)
<\kappa(\varepsilon(s)+1).
\tag{10}
\]

**推论。** 若某状态的完整秩是非零极限 λ，且 κλ=λ，则 ε(s)=λ。

证明：若 ε(s)<λ，极限性给 ε(s)+1<λ。
κ>0 的左乘严格保序，于是

\[
\rho(s)<\kappa(\varepsilon(s)+1)<\kappa\lambda=\lambda,
\]

与 ρ(s)=λ 矛盾。故 ε(s)≥λ，再用 ε≤ρ 得等号。
这不声称后继节点的事件秩也等于完整秩。

## 5. Y 端可以精确保留 X

将“正第二尖端展开”作为事件时，上一稿证明所有无事件段秩<β≤κ。
由(9)–(10)及 λ_Y 的极限性，

\[
\boxed{\varepsilon_Y(X)=\lambda_Y.}
\tag{11}
\]

X 的所有第一步都不是事件：n>0时是原第一尖端的一致高展开，n=0是删除。
所以从 X 开始的宏事件后继集合，恰是各 X[n] 的宏事件后继集合的并。
按宏事件秩的定义，

\[
\boxed{\lambda_Y=\sup_n\varepsilon_Y(X[n]).}
\tag{12}
\]

又 ε_Y(X[n])≤ρ_Y(X[n])<λ_Y，故这是真正的严格共尾族，不存在某一项先达到 λ_Y。

## 6. SRPD 端精确保留 C 的共尾值

对每个 P_d 的相对后代系统：
初始一步均记事件；其后把已开块的正外部返回记为事件。
参数化闭包及投影势给所有无事件段秩<α²<κ。
记相应宏事件秩为 ε_d。

仅为证明组合，添一个抽象根 *，从它向每个完整 P_d 放一条事件边。
这**不是新增 SRPD 项，不改展开器规则**。
它的完整秩为

\[
\rho(*)=\sup_{d\ge6}(\mu_d+1)=\lambda_R.
\]

最后等号使用 μ_d 严格共尾，无最大项。
* 的无事件秩为0，仍适用统一 κ。
由(9)和第4节，

\[
\boxed{
\lambda_R=\varepsilon(*)
=\sup_{d\ge6}\bigl(\varepsilon_d(P_d)+1\bigr).
}
\tag{13}
\]

而且每个 ε_d(P_d)≤μ_d<λ_R，所以它们也没有提前达到极限。

## 7. 目标现在有一个不损失序数值的等价表述

结合(12)与(13)，

\[
\boxed{
\rho_Y(X)=\rho_R(C)
\iff
\sup_n\varepsilon_Y(X[n])
=\sup_{d\ge6}\bigl(\varepsilon_d(P_d)+1\bigr).
}
\tag{14}
\]

左边正是候选 C 的等号问题；右边只保留关键步骤的秩。
这次无需再补“小误差会不会影响等号”的猜想，第1至6节已经处理。

但右边仍是**完整状态**事件树的比较。
背景位置、保留的未开块及内部返回能力不能抹掉，只是若干连续小步骤可以整体归约。
没有完成右边的嵌入，也没有由事件名称或有限计数推断二者相等。
如果该候选最终不合适，主目标仍允许换其他标准 SRPD 项。

## 8. 原规则核验

check-x-multiples.cjs（未随本次收录的来源：`output/y1342585-multirow-20260929/check-x-multiples.cjs`） 核验 n=0至12：

- 原 X[n+1] 删两列后的完整父表／数值；
- 返回真实 c₀ 的有限 DAG 成本，正好为 \(2^{n+2}-2\)；
- 末列确为普通 [0]，没有高旗标；
- 40个未超宽的(4)式实例，整体数值及原数值山脉的完整父表；
- 成本≤70的前5个返回宏，完全回放114次 D。

13次宏的累计认证成本32,738，较大8次不逐D回放。
12个过宽的复制请求明确未执行，不算成功；没有改小所请求的指标。
共992次原 Y FS、1,018次原父表核验，最大宽90，约0.5秒、54MiB RSS。

本节只有实施核验，全 n、k 的论证是(1)–(5)。
完整记录见 EVENT-BURST-VERIFICATION.json（未随本次收录的来源：`output/y1342585-multirow-20260929/EVENT-BURST-VERIFICATION.json`）。
没有修改公开 NER、Lean 或发布仓库；未 commit/push。当前等值目标仍未完成。
