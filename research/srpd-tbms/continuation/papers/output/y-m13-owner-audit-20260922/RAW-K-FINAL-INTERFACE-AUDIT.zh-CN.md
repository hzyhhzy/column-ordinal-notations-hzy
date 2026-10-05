# raw K 剩余接口最终独立审计

> 归档研究稿／Archived research manuscript — 2026-10-06。来源：`output/y-m13-owner-audit-20260922/RAW-K-FINAL-INTERFACE-AUDIT.zh-CN.md`。
> 本稿是有明确历史前提的纸面论证或局部接口，不是新增的 Lean 定理，也没有因归档而完成独立整链复核。文中“本轮／最新／目标”指原稿阶段；请以[现状总览](../../../README.zh-CN.md)为准。
> Proof/status guide: [English](../../../README.md). 实验／失败路线不单独展开；有删节时，原行区间及前后 SHA-256 见[清单](../../../manifest.json)。必要前提、适用范围和未完成方向仍保留。


2026-09-22。完整阅读
剩余接口稿（未随本次收录的来源：`output/y-m13-ordinary-trigger-20260922/RAW-K-REMAINING-INTERFACES.zh-CN.md`），
并核对 U/T、prefix state、background monitor 与真实影子容量公式。
纯纸面，无新测试、无其他代理文件或主代码修改。

**结论：未发现剩余接口中的数学反例。**
背景 row2 到最终 closer、相邻 anchors 的行1、raw K 结构与初始化均可按下述补充闭合。
结合此前新增费用和逐前缀审计，可收束为指定 raw K 允许过程的同目标下降覆盖，
但入口须保留真实共享背景契约，不能只写成“调用 U.check 通过”。
结论仍不涵盖原 Y 的 free-ordinary 正步。

## 1. 必须写入入口的实际背景条件

设保留 anchors 集为 A，包含全部 prefix family 用到的 grades 与 top=Q−1。
旧共享背景条件至少包括

\[
C(a,p)=B(a),\qquad
a\in A,\ p\in\{\text{所有 main}\}\cup\{e\}, \tag{1}
\]

其中 e 为实际 closer；所有使用 grade 及 top 的 B(a)≥2。
若采用既有全背景 B 契约，则 (1) 当然包含在其中。
相邻 anchors 另有真实 `C(a_i,a_(i+1))≥1`。

这是实际容量见证，不是可任意指定的抽象数表。
`U.check` 读取 B 的若干值、检查 top 的真实 row2 和相邻 anchors，却不检查 (1) 的全部等式；
`monitor.finish` 才会核对所有保留 anchors 对 mains/closer 的共享等式。
所以 theorem 的“旧 U 入口”必须按已文档化的共享背景含义理解，
而不能简化为未附加语义前提的程序布尔检查。
强初始化以及此前真实宏传输满足此要求。

## 2. 相邻 anchors：三种位置全部足够

ordinary 与 zero 不改背景 anchors 位置及它们之间的旧容量。
uniform-high 准备切在背景 k，选第 n 个旧影子；令 Δ=n(e−k)，

\[
G(a)=a\ (a<k),\qquad G(a)=a+\Delta\ (a\ge k).
\]

G 严格递增，保留 anchors 的相邻次序，且无新早份等级插入。
对一对旧相邻 a<b：

1. b<k：两点都留在旧保留部分，容量不变；
2. k≤a<b：两点选同一影子，容量是旧容量经同份行反射，至少保留旧行1；
3. a<k≤b：a 是旧外部父，b 选内部影子，外部容量公式给
   `C'(a,G(b))=C(a,b)≥1`。

主复制的物理 cut 在全部 anchors 右侧，之后的暴露、复制、截尾不改它们之间的前缀。
若删去不用的中间 anchor，原行1链的传递性也给新相邻点之间容量≥1；
现行 after:t=>t 不需要依赖这个可选删点动作。

这里没有借用 q−1 跨份行1：准备 q=1 确会让跨份容量降到0，
但使用的内部 anchors 全部同步选在最后同一影子，不分散在不同份。

## 3. 背景 row2 与真正 closer

### 3.1 准备后的 mains

对于每个旧 anchor a，a≥k 时与 mains 选同一影子，其共同容量由 B(a) 经同一行反射得到；
a<k 时依外部精确继承，容量仍为 B(a)。
因此准备后所有保留使用 grade 和 top 对全部所选 mains 都有 row2，且仍共享实际值 B'。
这也包括 a=k：虽然 grade 地址移动，容量等于 k 的行不反射，但原来的 row2 并不降低。

准备后暂存 closer 可以很弱，尤其内部 grade 到它的跨份容量在 row1 准备时可以为0。
本证明没有对这个暂存点要求 row2，也没有再次从它进行背景准备。
它随后被真正截去，旧最后 main 成为主复制的控制列。

### 3.2 主复制的最终 closer 是额外份首根

记准备后的 source cut main 为 κ，旧最后 main 为 z，主跨度 ℓ=z−κ。
源只需 n 份，实际 main FS 取 n+1 份。
输出最后 main 是第 n 份的最后模板，物理地址 `z−1+nℓ`，所以最终 closer 恰为

\[
e'=z+n\ell=\kappa+(n+1)\ell, \tag{2}
\]

即额外第 n+1 份的首根。该列确实由实际 FS 生成并保留，不是已被 FS 删除的临时末列。

所有背景 anchors 都小于 κ。对最终首根端点使用外部容量公式，得到

\[
C'(G(a),e')=C_{\rm prepared}(G(a),\kappa)=B'(G(a))\ge2. \tag{3}
\]

因此 row2 到新 closer 来自 prepared cut main 的原有外部接口，
不是来自弱暂存 closer，也不是来自 Q'−1 的内部接缝。
ordinary 步完全相同，只是不需要前面的背景准备。

### 3.3 每个短前缀的 closer

主点连续。每个非全长源前缀的 closer 就是下一 source main 的物理位置；
全长前缀的 closer 才是 (2)。
所有这些点均已拥有同一 B' 的接口，故 (1) 及 row2 同时适用于整个 prefix family。
某前缀选择不同的根 grade 不改变这一实际容量事实。

## 4. raw K 的结构与 O₂

marked ordinary 的父全 marked ordinary，所以其底祖先链不含 high，O₂ 为空。
恒父 high 的底链先到 marked 根，也无更早 high 祖先，O₂ 同样为空。
卫星的底链先到唯一配对 high，再到其 marked 根，其 O₂ 恰为该根单项。
卫星高度为根高+1，故此 owner 只使最高普通行需要 g(root)+1≤Q；
其余行仍是字面需求。恒父 high/卫星的单一实际父边有 Q 储备，覆盖其所有普通行。

允许的操作保持 K：

- ordinary cut marked ordinary：控制列也是 marked ordinary，首列低父与继承父仍 marked；
  high/卫星模板成对复制，不改变其恒父性和邻接；
- ordinary cut high 且 r=0：控制列是紧邻高度1卫星，块长1，仅复制该 high；
  控制卫星被删，不留下失配卫星；
- uniform-high：新首根 marked，父为前份 marked 根。
  若内部 high 上升，其根同步上升；其卫星又与 high 同步上升。
  常值父只重复/搬运，故同高、对齐、卫星相邻和不可被引用均保持；
- zero 只删除尾列，不产生失配的保留卫星。

上述同步性可直接从行链核查：high 的每行先到其根，卫星每行先到配对 high；
在活动行存在时，是否通到活动根因而一致；活动行不存在时双方都不上升。

因此在该域内不能隐藏一项未支付的 ordinary owner 差分。
若允许非恒父内部 high 或正行切 high，则不能直接沿用此段论证。

## 5. 字面、高度、等级与指标边界

marked ordinary 上升时，旧 full 的 active-root 费用严格大于准备等级 k，
故实际容量获得 Δ；它支付所有移位和插入行的字面需求。
marked 根等级的相同阈值保证由旧 full active offset 给出，
并通过 `g_partial≥g_full` 覆盖全部部分前缀。此前的
前缀审计（未随本次收录的来源：`output/y-m13-owner-audit-20260922/STRONG-BARRIER-PREFIX-TERMINAL-AUDIT.zh-CN.md`） 已给详细分类。

high/卫星旧 Q 储备因 Q>k 而得到 Δ，成为 Q' 储备。
marked 高度≤Q−1，high/卫星高度≤Q；新高度至多增加 n≤Δ，故字面行不超过 Q'。
新首根的全部边使用 Q'−1，且 `h_c+b≤k+Δ≤Q'−1`。

grade 上界 G(Q−1)=Q'−1；下界和前缀不增性按同步反射/旧 full-partial 拼接保持。
准备的 q=1≤k，主高复制的 q=Q'≤κ；普通主复制的真实最大行也≤其父物理地址。
所以所用有限严格 F 容量公式的控制行假设满足。

zero 恢复已有较短 prefix 的等级表和实际 closer；空源是终止边界，不再需要非空入口条件。
数学上每个有限 n 都是有限次实际操作；实现的 n/宽度护栏不限制纸面量词。

## 6. 初始化及收束范围

剩余接口稿给出的 `g(j)=h_j+2` 与 Q 选择正确：
所有组件费用为 `u+3≤H+2≤Q`，所有 marked 高度差分均为2；
真实种子主点间容量 Q，背景 B(a)=a，已使用 grades 至少为2。
相邻 anchors 有行1，所有 mains/closer 共享真实背景，因此无需先使用屏障也能初始化。
H=0 情形同样没有例外。

综合源屏障、新生屏障、费用分类、逐前缀 terminal 审计及本稿剩余接口，
对**真实共享背景入口上的 raw K 允许过程**，同目标闭合与每步严格有限 M 下降的纸面链条已齐全。
实际 F 保持与暴露宏的有限严格下降仍引用已有目标系统引理，本稿没有用实验替代它们。

这允许陈述 raw K 该过程的完整全指标/全后代覆盖，以及经已证 Ω 宏落入该过程的 V 受限覆盖。
它不允许把结论写为完整 Y1343 已解决：原 Y free-ordinary 正步及 Π/Ω 混合仍缺同一实际目标的连接。
也不能把“每个新入口可另初始化”当成已有真实下降的一部分。
