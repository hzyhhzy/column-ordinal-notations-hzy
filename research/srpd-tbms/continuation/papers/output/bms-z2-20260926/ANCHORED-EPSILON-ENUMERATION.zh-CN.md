# 带任意旧参数的星形索引：精确 epsilon 枚举

> 归档研究稿／Archived research manuscript — 2026-10-06。来源：`output/bms-z2-20260926/ANCHORED-EPSILON-ENUMERATION.zh-CN.md`。
> 本稿是有明确历史前提的纸面论证或局部接口，不是新增的 Lean 定理，也没有因归档而完成独立整链复核。文中“本轮／最新／目标”指原稿阶段；请以[现状总览](../../../README.zh-CN.md)为准。
> Proof/status guide: [English](../../../README.md). 实验／失败路线不单独展开；有删节时，原行区间及前后 SHA-256 见[清单](../../../manifest.json)。必要前提、适用范围和未完成方向仍保留。


2026-09-27。本文从零截断交织的完整原生规则，计算一个真正的二元／多元序数运算。它不是整个 BMS 与 PTO(Z₂) 的比较证明，也不假设一般高层包根具有秩同余。

## 1. 状态与结论

固定 H≥2，所有模式补到 H 行。令

\[
M_k=(0,0,\ldots,0)\,
\underbrace{(1,1,0,\ldots,0)\cdots(1,1,0,\ldots,0)}_{k\text{ 个}},
\qquad k\ge0.
\]

这是一个根同时在第 0、1 行指向 k 个互不相连的叶子的模式。使用已经定义的零截断交织 \(D_0\)，令

\[
S(A;Q_1,\ldots,Q_k)=D_0(M_k;A,Q_1,\ldots,Q_k).
\]

根孔 A 和所有叶孔 Q_i 都允许有全部 H 行内部结构。设

\[
\alpha=r(A),\qquad \beta_i=r(Q_i),\qquad
\eta=\omega^{\beta_1}+\cdots+\omega^{\beta_k}.
\]

这里是通常序数和，不要求输入列表已为 Cantor 正规形。令 \(\varepsilon_\xi\) 为 epsilon 数的通常严格递增连续枚举，并定义

\[
\iota(\alpha)=\min\{\xi:\alpha<\varepsilon_\xi\}.
\]

对正序数 η，再定义

\[
j(\eta)=
\begin{cases}
m-1,&\eta=m\in\mathbb N_{>0},\\
\eta,&\eta\ge\omega.
\end{cases}
\]

**精确公式：**

\[
\boxed{
rS(A;Q_1,\ldots,Q_k)=
\begin{cases}
\omega^\alpha,&k=0,\\
\varepsilon_{\,\iota(\alpha)+j(\eta)},&k>0.
\end{cases}}
\tag{1}
\]

右侧下标中的加法也是通常序数加法；不能换成自然和。本公式只断言给定有限模式的实际展开树秩，不声称每个任意序数参数都有固定 H 行表示。

## 2. 一个可直接核验的上下文引理

设 B 非空，最左根 o 在第零行指向 B 的全部其余点。定义 G_B(Q)：先放 B，再放 Q；Q 内部不变，从 B 到 Q 的边只有 \(oR_0q\)，对每个 q∈Q 都有这条边。

这个图相干。记 b=r(B)>0，则

\[
\boxed{rG_B(Q)=b\cdot\omega^{r(Q)}.}
\tag{2}
\]

证明按 r(Q) 归纳。Q 空时 G_B(Q)=B。Q 末点有内部父时，外部仅有零行入边，不能夺走内部最高父，因此每个原生孩子恰是 G_B(Q[n])。使用子秩严格递增共尾、指数及左乘对右参数连续，得到极限情形。

若 Q=R⊕1 的末点无内部父，整个状态的实际控制是零行的 o。坏块恰为 G_B(R)，而零行控制不产生跨副本连边，故

\[
G_B(R\oplus1)[n]=G_B(R)^{\oplus(n+1)}.
\]

并列秩是通常序数和，于是取所有 n 的上确界得到

\[
b\cdot\omega^{r(R)}\cdot\omega
=b\cdot\omega^{r(R)+1}.
\]

这证明 (2)。此处 B 内部的高行结构完全不受限制。

令 \(G_B^0(\varnothing)=\varnothing\)，迭代 (2) 的序数递推为

\[
x_0=0,\qquad x_{m+1}=b\cdot\omega^{x_m}.
\tag{3}
\]

只需以下两种 b：

- 若 \(b=\omega^\alpha\)，(3) 的上确界是最小的、严格大于 α 的 epsilon 数。
- 若 b 本身为 epsilon 数，(3) 的上确界是严格大于 b 的最小 epsilon 数。

第一点可如下自证。ε>α 且 ε 为 epsilon 数时，\(\omega^\alpha\omega^\varepsilon=\omega^{\alpha+\varepsilon}=\varepsilon\)，故 ε 是此函数不动点。从 0 迭代的最小不动点 λ 满足 \(\lambda=\omega^{\alpha+\lambda}\)。由 \(\alpha+\lambda\ge\lambda\) 及 \(\omega^\lambda\ge\lambda\)，可得 \(\omega^\lambda=\lambda\)，再由指数的严格性得 α+λ=λ。这推出 α<λ；反之任意 ε>α 均为不动点。函数严格递增且连续、迭代严格递增，所以其上确界确为该最小不动点。第二点取 \(\alpha=b\)，因为 b=ω^b。

## 3. 对叶孔权重 η 的同时归纳

固定根孔 A；同时对所有有限叶孔列表作 η 归纳。叶列表为空时，S(A;())=W₀(A)，已有精确指数定理给 ω^α。

### 3.1 最后叶孔为空

设 \(Q_k=\varnothing\)，故 β_k=0。令

\[
B=S(A;Q_1,\ldots,Q_{k-1}).
\]

末点是 M_k 的最后叶根，其实际控制为第 1 行的最左根 o。删除末点所得坏块就是整个 B；所有副本之间只添 o 到后来整个块的零行边。注意其他孔点、其他叶根都不是该末点的零行祖先，故它们不会成为跨块边的源。因此逐图有

\[
S(A;Q_1,\ldots,Q_{k-1},\varnothing)[n]
=G_B^{n+1}(\varnothing).
\tag{4}
\]

B 的最左根指向全部后续点，所以第 2 节适用。

- k=1 时 b=ω^α，(4) 的秩上确界是 ε_{ι(α)}。
- k>1 时归纳假设给 b=ε_{ι(α)+j(η')}, η'=Σ_{i<k}ω^{β_i}>0，故上确界是 ε_{ι(α)+j(η')+1}。

η=η'+1，而对正 η' 有 j(η'+1)=j(η')+1，因此得到 (1)。所有有限迭代的秩严格递增，加一不改变其上确界。

### 3.2 最后叶孔秩是后继 δ+1

由后继／末点无父引理，Q_k=R⊕1、r(R)=δ。完整原生 Feedback 把最后叶根换成 n+1 个克隆，每个孔都为 R。M_k 相应变成同类星形索引，早期孔不变。

孩子列表的权重为

\[
\eta_n=\eta'+\omega^\delta(n+1)
\nearrow\eta'+\omega^{\delta+1}=\eta.
\]

它们严格递增，η 是非零极限。归纳假设、epsilon 枚举连续性与通常序数加法的右连续性给

\[
\sup_n\bigl(\varepsilon_{\iota(\alpha)+j(\eta_n)}+1\bigr)
=\varepsilon_{\iota(\alpha)+\eta}.
\]

这里 \(\sup_nj(\eta_n)=\eta\)：若权重一直有限，所差的一有限项不影响上确界；否则 j 已是恒等。这恰为 (1)。

### 3.3 最后叶孔秩是非零极限 λ

所有原生孩子都是 Work，同一索引、同一早期孔，只把最后孔变成 Q_k[n]。其秩 \(\gamma_n\nearrow\lambda\)，故

\[
\eta_n=\eta'+\omega^{\gamma_n}
\nearrow\eta'+\omega^\lambda=\eta.
\]

再按上一小节取上确界即可。三个分支覆盖全部孩子，不是仅对选定协议计算秩。完成 (1) 的证明。

## 4. 真正可用的含义与边界

最简单的二元截面 \(E(\alpha,\beta)=rD_0(M_1;A,Q)\) 满足

\[
E(\alpha,0)=\varepsilon_{\iota(\alpha)},\qquad
E(\alpha,\beta)=\varepsilon_{\iota(\alpha)+\omega^\beta}\quad(\beta>0).
\tag{5}
\]

因此在同一 H≥2 行内，可以用固定两根索引取得“严格大于任意旧孔秩 α 的下一个 epsilon 数”，并沿真正的 ordinal 参数 β 枚举。这比仅说某个未标定 F_P 存在更具体；允许旧参数来自全部 H 行，并不限于小于 ε₀。

但不能把它当作高阶反射／坍缩已完成。这个新校准仍只有 epsilon 枚举规模，未证明对 Z₂ 共尾的源系统可持续模拟。

它还说明“最后参数连续”不能加强成“首参数连续”。固定 β=0，取任意已实现、严格递增共尾于 ε₀ 的 α_n<ε₀，则

\[
E(\alpha_n,0)=\varepsilon_0,
\qquad E(\varepsilon_0,0)=\varepsilon_1.
\]

这些 α_n 可直接取一行 ω 幂塔，ε₀ 可由两行种子表示。因此这是真正可实现参数上的不连续，不是把定义域无理由扩到全部序数后的人造现象。

没有使用本文来反过来证明 BMS 良基：全文在已有外部良基性下计算实际树秩。尚未 Lean 形式化。

## 5. 依赖与审计状态

- 并列、零行包根与子秩共尾（未随本次收录的来源：`output/bms-z2-20260926/COMPOSITION-ALGEBRA.zh-CN.md`）。
- 零截断交织定义和逐边相干性（未随本次收录的来源：`output/bms-z2-20260926/TYPED-INTERLEAVED-RESET.zh-CN.md`）。
- 穷尽所有孩子的原生三分支（未随本次收录的来源：`output/bms-z2-20260926/TERMINAL-WORK-INDEX-FEEDBACK.zh-CN.md`）。

本文由根代理推导；第 2 节的上下文引理与空根孔星形校准也由另一代理独立得到，见 S₂ 截面校准（未随本次收录的来源：`output/bms-z2-20260926/S2-SLICE-EXACT-CALIBRATION.zh-CN.md`）。任意根孔公式另经交织宏作者全文独立审计：核对了 k=1、α=0／epsilon、普通序数加法吸收、有限 j 修正与极限共尾性，并确认 A 的任意高行内部关系不产生新的跨副本边，未发现实质缺口。

有界诊断（未随本次收录的来源：`output/bms-z2-20260926/check_anchored_epsilon.py`） 以 300 个固定种子状态核对 3,411 个逐矩阵单步／上下文等式，包含任意根孔、空末叶、后继 Feedback、G_B 的两个分支，以及后续 zeta 上下文的有限迭代等式；全部通过，最大 51 列，进程约 0.42 秒退出。脚本有 10 秒、150 列硬上限，不估计无限秩、不进行基本列轨迹搜索。一般序数结论来自第 2–3 节证明，而不是有限测试。
