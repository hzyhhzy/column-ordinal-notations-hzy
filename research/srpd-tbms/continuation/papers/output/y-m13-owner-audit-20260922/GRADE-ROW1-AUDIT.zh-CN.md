# raw K 入口的 grade row1 放宽：独立审计

> 归档研究稿／Archived research manuscript — 2026-10-06。来源：`output/y-m13-owner-audit-20260922/GRADE-ROW1-AUDIT.zh-CN.md`。
> 本稿是有明确历史前提的纸面论证或局部接口，不是新增的 Lean 定理，也没有因归档而完成独立整链复核。文中“本轮／最新／目标”指原稿阶段；请以[现状总览](../../../README.zh-CN.md)为准。
> Proof/status guide: [English](../../../README.md). 实验／失败路线不单独展开；有删节时，原行区间及前后 SHA-256 见[清单](../../../manifest.json)。必要前提、适用范围和未完成方向仍保留。


2026-09-22。完整核对 `uniform-cover.cjs`、`tight-offset.cjs`、
`catalogue-middle.cjs` 的准备/背景更新与既有 raw K 证明链。
本稿只新增入口放宽引理，不改 U/T、其他代理稿件或实际目标，不作新的搜索。

**结论：可以把每个 marked grade 的背景支撑从 B(g)≥2 放宽为 B(g)≥1。**
必须继续要求 top=Q−1 的 B(top)≥2、真实共享背景、相邻 anchors 行1，
以及全部逐前缀 U 其余条件、强屏障费用 (P) 和高度差分 (O)。
在原 raw K 允许过程内，同一实际目标上的原 row1 宏和固定 family 传输仍闭合。
这不是 free-ordinary 闭合或每次都能重求 grade 的存在性定理。

## 1. 精确的放宽入口

沿用 RAW-K-COVER-THEOREM（未随本次收录的来源：`output/y-m13-ordinary-trigger-20260922/RAW-K-COVER-THEOREM.zh-CN.md`）
的 raw K 类、允许操作和真实有限严格 F 目标。
只将其入口第3项中的“全部使用 grade 与 top 的 B≥2”改为

\[
B(g^w(j))\ge1\quad(j\text{ marked，所有前缀 }w),
\qquad B(Q-1)\ge2. \tag{1}
\]

其余条件不变，特别是

\[
\max(1,h_j)\le g^w(j)\le Q-1,
\quad C(a_i,a_{i+1})\ge1,
\quad C(a,p)=B(a)
\]

中的真实共享等式仍对全部背景地址 a≤Q 和全部 mains/closer p 成立。
grades 和 top 仍是实际保留 anchors；若 grade 恰等于 top，它自然须满足较强的 row2。
不添加 `leafBudget`，也不扩大到 raw 非恒父 high 的正展开。

实现上的区别必须明说：原 `U.check` 仍逐个断言 B(g)≥2，会拒绝这种新入口。
所用实际宏是原 `T.step(...,{uniformRow:'one',after:t=>t})`；只需换用上述放宽检查。
T.step 内部的默认 factory 检查不构成隐藏障碍：raw K 每枚 high 恒父于其根，
故每个前缀的 `factoryRoot` 都是 null，不触发非一致 raw high 的 row2 工厂要求。

## 2. uniform-high 准备的实际背景公式

旧末 high 的根 c，活动等级 k=g_full(c)，旧真实 closer 为 e，源指标 n≥1。
原准备在物理背景地址 k 用 q=1，实际取 n+1 份并保留第 n 份旧 mains。
设

\[
\Delta=n(e-k),\quad Q'=Q+\Delta,
\qquad
G(a)=\begin{cases}a&a<k,\\a+\Delta&a\ge k,\end{cases}
\]

\[
\psi(t)=\begin{cases}t&t\le k,\\t+\Delta&t>k.\end{cases}
\]

准备合法只用到真实 C(k,e)=B(k)≥1，以及 q=1≤k；不需要 B(k)≥2。
因 k 是正 anchor，后一条件自动满足。
相对于准备后的所选 mains，整个新背景恰为

\[
B'(a)=
\begin{cases}
B(a),&a<k,\\
0,&k\le a<k+\Delta,\\
\psi(B(a-\Delta)),&k+\Delta\le a\le Q'.
\end{cases} \tag{2}
\]

这是实际影子容量公式，不是任意提高矩阵的操作：第一段外部精确继承；
中段属于较早影子，跨份接缝 q−1=0；最后一段与 mains 同份，容量按 ψ 反射。
`catalogue-middle.monitor` 中的 `clamp(...,row-1)` 与 `shift(tail,k,Δ)` 正是 (2)。

每个旧使用 grade a 都搬到 G(a)，于是

\[
B'(G(a))=
\begin{cases}B(a)&a<k,\\\psi(B(a))&a\ge k\end{cases}
\ge B(a). \tag{3}
\]

所以 row1 正支撑保持；没有任何使用 grade 留在中间的零支撑带。
top≥k 且 G(top)=Q'−1，故其旧 row2 也由 (3) 保持。
这包括活动等级恰等于 top：即使 B(top)≤k、容量没有增加，它仍不低于2。
若 k=1 且 B(1)=1，活动 grade 地址搬到1+Δ、支撑仍为1，同样足够下一次 row1 准备。
但旧物理地址1落在零带中；本引理没有生产可无限重复使用的固定低等级工厂。

## 3. 暂存 closer、最终 closer 与 anchors

准备后的暂存 closer 可以不共享 B'，甚至对内部 grade 只有0容量。
它随后被实际截去，不能拿它冒充下一次准备入口。

主高复制的物理切点 κ 是准备后的根 main，严格在全部背景位置右侧。
它用 q=Q'，实际多取一份主块。最终 closer 是额外份首根，记为 e'。
对任意背景地址 a≤Q'，外部精确继承给

\[
C'(a,e')=C_{prepared}(a,\kappa)=B'(a). \tag{4}
\]

每个新 main 同理；短前缀的 closer 是下一 main，故也共享 (2)。
式 (4) 对普通 grade 只需右侧≥1，对 top 仍需≥2，绝不借用弱暂存 closer。
该部分与既有 [最终接口审计](RAW-K-FINAL-INTERFACE-AUDIT.zh-CN.md) 的证明相同，
仅把非 top 的最后数值下界2改成1。

anchors 不分配到多个较早份，而是全部按同一个 G 搬运。
旧相邻 anchors 两者在 k 左侧时连接未改；两者在右侧时同份容量不减；
跨 k 时按外部公式精确继承。因此真实相邻容量≥1保持。
主复制位于它们右侧，不改变该前缀。若选删不用 anchors，行1链的传递性亦足够。
这里没有使用 q−1≥1；事实上本次 q−1=0。

## 4. 费用、offset 与 grade 高度没有 row2 依赖

既有强费用证明的严格余量来自需求

\[
g(d)+1+u-h_d>g(d),\qquad u\ge h_d,
\]

而非 B(g(d))≥2。因此若 grade≥k，旧容量必>k，容量反射增加 Δ；
若 grade<k，grade 不变，原费用足够。top 的 Q 储备仍有 Q>k，故总是反射到 Q'。
屏障搬运、前份新根链免除、partial/full 分类和 terminal 例外均是源结构事实，
也不读 B(g) 的数值2。

上升 marked j 的旧 full active-root offset 给

\[
g_{full}(j)-h_j\ge k-h_c,
\]

非首 j 有 h_j>h_c，所以 g_full(j)>k。
旧 partial grades 不小于 full，因而也反射增加 Δ，足以支付高度增加 b≤n≤Δ。
首根 grade≥k+Δ≥h_c+b；不上升根的高度不变。
所以 grade 范围保持，只须把旧证明中“最小值≥2”改为实际需要的“最小值≥1”。
G 单调，保留逐前缀不增性和既有 full/partial 拼接。

对未免除的外根 d<c、上升 ordinary j，旧 full 仍给

\[
g(d)-h_d\le k-h_c,\quad h_d<h_c,
\quad\text{从而 }g(d)<k.
\]

该估计在 k=1 时并未失效：正 grades 使这种未免除的外根分支根本不可能出现。
它或者已被屏障免除，或者入口不满足原 offset；不能据 k=1 捏造额外需支付的分支。
其他 high/卫星行继续由 Q' 储备覆盖。

## 5. ordinary、zero 与局部重新选 grade

ordinary 不准备背景。全部 grades 和 top 在实际 main cut 左侧，
新 mains 及额外份 closer 对它们精确继承同一 B；row1 和 top row2 均保持。
anchors、源高度与 grades 不变，family 仍按原 full/partial 规则搬运。
允许的 high-cut ordinary 只有 r=0，原 raw K 分支证明不变。
zero 恢复已经检查的旧短前缀，其 closer 是旧下一 main；空源终止。

由此获得以下独立局部推论：在同一实际目标、同一背景与主点上，
若另外选出一个全部前缀 family，满足 (1) 及所有其他入口条件，
那么它是合法的放宽入口，之后所有 raw K 允许步继续使用既有实际宏。
重新选 family 本身只是换覆盖见证，不改变实际 M 图，也不是一段 M 下降。
真正的非空下降仍必须由之前/之后的实际源步模拟提供。

row1 地址作为新 anchor 的可揭示性可用 `revealPositive` 的既有论证：
两个正背景祖先是同一 main 的行1祖先，在有限 F 中可比，故相邻真实连接至少行1。
但新 grade 仍必须逐项满足高度下界、全部前缀单调性、费用和 offset；
不能仅凭某地址 B=1 就直接把任意根的 grade 降到该地址。

本稿未独立重跑主代理报告的小例 actual-target 修复轨迹，也不以那条测试作为上述全称证明。
特别地，成功修复一次 FO 后的见证，不推出每次 FO 后总存在这样的 family。
完整 Y1343 的 FO 同目标连接仍需另外证明。
