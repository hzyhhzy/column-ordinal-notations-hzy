# SRPD 与 TBMS、Y：结论及证明过程归档 · [English](README.md)

整理日期：**2026-10-06**。研究已按用户要求暂停；本次只保存已有成果，不产生新的比较定理，不修改记号规则，不新增 Lean 证明。

本目录续接 [2026-09-28 档案](../archive/README.zh-CN.md)。下面先给暂停时的准确状态，再指向完整推导。原语言证明稿见[分类目录](CATALOGUE.md)，来源与删节范围见[清单](manifest.json)。失败路线、失败程序和逐轮 `STATUS`／`CONTINUE` 日志不另行收录；证明所需的前提、适用边界及尚缺方向不能随之删除。

## 先读什么

- [证明路线与关键引理](PROOF-ROUTES.zh-CN.md)：从容量模拟、等号校准，到完整 Y 下界和最新局部接口。
- [证据、浏览器与复验边界](EVIDENCE.zh-CN.md)：哪些只是有限记录，哪些程序可直接使用，哪些没有交付通用转换器。
- [全部证明稿目录](CATALOGUE.md)：保存各阶段正向论证及支撑引理，避免只留下最终公式而丢失推导。
- [旧的可复现档案](../archive/README.zh-CN.md)：73 份既有材料、25 篇证明稿及其运行依赖，保持原版本和校验清单不动。

## 比较口径与证据等级

本文用 `S(s)` 表示计数显示为 s 的**现行隐含首根版 SRPD 标准项**；计数本身不替代完整父表。设

\[
R=\rho(\lim\mathrm{SRPD}),\quad
I_N=S(1,2,4,\ldots,2^{N-1}),\quad
L=\rho(\mathrm{TBMS\ Limit}).
\]

`I_N` 有 N 个可见列。普通 e0MN 的 M13 与这里的 SRPD 严格初段相对应，顶端须对齐为 `SRPD[n+1]=M13[n]`；不要给现行 SRPD 再补旧版冗余的首项 1。整个 RPD 不等于 SRPD，准确初段关系见[仓库对应说明](../../../notations/SRPD/correspondence.zh-CN.md)。

TBMS 指原默认基本列的普通 TBMS，允许任意有限递归行标；不是 strong 版，也不是只到普通行标 ε₀。记 `B_H=()(1^H)` 为空根后接一枚恒值 1、总行高 H 的列；复合 H 按原生行段表达。**H 是行高，不是整个 TBMS 项的序数值。**

`ρ` 是非零原式在全部原基本列步骤下的良基下降秩，空式为零，排除零的自环。文中大小比较采用这一口径。沿用标准域的秩—序型解释时才能相应读作序数值比较；不据此识别任意手写非标准图。

本次区分四类证据：

| 类别 | 含义 | 不能据此声称 |
|---|---|---|
| 纸面比较 | 写出了全参数、全部后代的论证，引用明确的旧引理 | 已经 Lean 化或独立复核整条历史链 |
| 条件性纸面下界 | 在明列历史接口成立的前提下给出新增归纳 | 已经消除这些前提或完成目标 B |
| 局部接口 | 在特定资源、标签或阶段条件下成立 | 覆盖原系统全部合法后代 |
| 有限核验 | 原公式、实现、选定路径或文件身份的有限检查 | 全称数学定理、精确序数值或无限持续供应 |

即使称为“纸面等号”，也不是同指标基本列交换，更不是自动给出规范、与历史无关的保序转换器。此次整理不是新的数学审计。

## 1. TBMS 的整体承载界

最新收录的较小固定承载式为

```text
D44 = S(1,2,4,8,4,1,2,9,38,4,12,42,44)
W   = S(1,2,4,8,4,2)
```

[有限最高行库证明](papers/output/tbms-srpd-equalities-20260929/FINITE-ROOF-WHOLE-TBMS-LOWER.zh-CN.md)给出

\[
\boxed{L\le\rho(D44)<\rho(W)<R.}
\]

关键不是给每一步换一个大目标：对每个有限递归深度，先在 `D44` 的一个后代中建立全部有限最高行库，随后同一实际目标持续模拟源的所有后代。最后对递归深度取上确界。`L≤D44` 的反向尚未完成；不能写 `L=D44`，也不能把逐项严格号直接升成 `L<D44`。

旧档案中的更宽承载式、`W[1]` 内的固定承载和 `B_(ε₀)` 专用界仍保存。改进过程为：完整归档与有限调用券 → 单行返回 → 连续主区 → 弱最高模板 → **取消无穷模板，仅保留已登记有限最大值**。详见[路线说明](PROOF-ROUTES.zh-CN.md)。

因此，旧候选 `W=B_(ω^ω)` 和 `lim(SRPD)=B_(ε₀)` 已被这些纸面比较链排除，不再列作当前等号目标。这里不重复收录探索这些候选的失败路线。

## 2. TBMS 的等号校准

以下均为有历史引理依赖的纸面秩等号，未 Lean、未整链独立重审。令

```text
P = 1,2,4,8,4,1,2,9,38,4
J6 = S(P,6)
J7 = S(P,7)
```

`S(P,…)` 是连接计数列，不是乘法。

| SRPD | TBMS | 证明 |
|---|---|---|
| `S(1,2,4,8,4)` | `B_(ω²)` | [第一五列块](papers/output/tbms-e0mn-bridge-20260925/FIRST-FIVE-COLUMN-EQUALITY.zh-CN.md) |
| `S(P,5,12,41,42)` | `()(1^(ω²))(2)` | [平行叶极限](papers/output/y13425858-srpd-equality-20260929/TBMS-SIBLING-LIMIT-SRPD-EQUALITY.zh-CN.md) |
| `S(P,5,12,42)` | `B_(ω²+1)` | [完整链极限](papers/output/tbms-srpd-equalities-20260929/OMEGA2-FULL-CHAIN-EQUALITY.zh-CN.md) |
| `S(P,5,12,43)`、`S(P,5,12,44)` | `B_(ω²+2)`、`B_(ω²+3)` | [指标空根行带](papers/output/tbms-srpd-equalities-20260929/COMPONENT-ROOT-OMEGA-EQUALITY.zh-CN.md) |
| `S(P,5,12,45)` | `B_(ω²+ω+1)` | [同稿](papers/output/tbms-srpd-equalities-20260929/COMPONENT-ROOT-OMEGA-EQUALITY.zh-CN.md) |
| `S(P,5,12,45,7)=J6[1]` | `B_(ω²·2)` | [双行带](papers/output/tbms-srpd-equalities-20260929/DOUBLE-OMEGA2-ROW-EQUALITY.zh-CN.md) |
| `J6[k]`，k≥1 | `B_(ω²(k+1))` | [递归冠带](papers/output/tbms-srpd-equalities-20260929/RECURSIVE-CROWN-OMEGA3-EQUALITY.zh-CN.md) |
| `J6` | `B_(ω³)` | [同稿](papers/output/tbms-srpd-equalities-20260929/RECURSIVE-CROWN-OMEGA3-EQUALITY.zh-CN.md) |

其中 `B_(ω²·2)` 是**同一列**里的两个 ω² 行段，不是两枚平行 ω² 叶。后者有[单向承载](papers/output/y13425858-srpd-equality-20260929/TBMS-DOUBLE-OMEGA2-SRPD.zh-CN.md)，不得混用。

再往上，目前是

\[
\rho(B_{\omega^{n+2}})\le\rho(J7[n])\quad(n\ge1),
\qquad \rho(B_{\omega^\omega})\le\rho(J7),
\]

见[有限阶行库](papers/output/tbms-srpd-equalities-20260929/FINITE-RANK-PORT-LOWER.zh-CN.md)。尚无反向上界。`J7[2]=S(P,6,8)` 仍是未解决的完整子锥；已经有若干局部返回协议的上界，不代表它的全部后代都受同一个 TBMS 节点控制。

对称塔 `1,2,4,…,2^(h+1),2^h,…,2` 仍可作为[承载族](papers/output/tbms-e0mn-bridge-20260925/SYMMETRIC-TOWER-BOUND.zh-CN.md)，但不是已证明的逐阶等值表。

## 3. Y 的精确等值点与较早下界

设

\[
\beta=\rho_Y(1,3,4,2,5,8)=\rho(S(1,2,4,8,4))=\rho(B_{\omega^2}).
\]

| Y 节点 | 结论 | 证明 |
|---|---|---|
| `134258`，亦有 `1258` | 等于 β | [Y—TBMS 校准](papers/output/y-tbms-epsilon0-20260927/Y134258-TBMS-OMEGA2.zh-CN.md)、[前缀吸收](papers/output/y1342585-equality-20260929/PREFIX-ABSORPTION.zh-CN.md) |
| `1342583` | 等于 `S(P,3)`，值为 β^ω | [花瓣幂证明](papers/output/y1342583-srpd-equality-20260929/EQUALITY.zh-CN.md) |
| `1342584` | 等于 `S(P,4)`，值为 `sup{β,β^β,β^(β^β),…}` | [带权森林与受保护乘方](papers/output/y1342584-srpd-equality-20260929/EQUALITY.zh-CN.md) |
| `1342585` | 尚未确定等值尾部；已有十列前缀 P 的定位及更紧固定上界 | [前缀定位](papers/output/y1342585-equality-20260929/SRPD-PREFIX-LOCATION.zh-CN.md)、[上界缩到 U[5]](papers/output/y1342585-equality-20260929/PREFIX-ABSORPTION.zh-CN.md) |
| `1,3,4,2,5,8,9,11` | `≤ B_(ε₀)` | [森林预算](papers/output/y-tbms-epsilon0-20260927/FOREST-BUDGET-UPPER.zh-CN.md) |
| `1,3,4,2,5,8,10` | `≤ TBMS Limit ≤ D44 < W` | [递归端口](papers/output/y-recursive-port-upper-20260927/RECURSIVE-PORT-UPPER.zh-CN.md)及上面的 TBMS 承载 |

这里 `a` 若出现在旧短写中表示单个数 10，不能把两位数展开成两列。`Y13425858=()(1^(ω²))(1^(ω²))` 曾按用户要求作工作假设，**不是本研究独立证明的结果**；因此不能借表中 TBMS 等号自动声称得到新的 Y 等号。

更早的 `133`、`134`、`134257…` 等承载、严格保序原型及其证明依赖也在[分类目录](CATALOGUE.md)中；它们对更小固定目标的定位仍有用，不因较大全局下界出现而删除。

## 4. 全体 SRPD 的 Y 下界推进

为避免长式误抄，固定

\[
C=(1,3,4,2,5,8,10,4,9,14,16).
\]

以下都是**依赖明列历史接口的纸面下界**。它们没有经过一次端到端的独立复核，也没有 Lean 比较证明；本次归档不提高证据等级。

| 完整 Y 节点／族 | 已记录的界 | 主要论证 |
|---|---|---|
| `Y(1,3,4,2,5,8,10,4)` | `< I20` | [普通端口提升](papers/output/y134259-owner-returns-20260928/ORDINARY-PORT-LIFT-FINITE-CARRIER.zh-CN.md) |
| `Y(1,3,4,2,5,8,10,4,9,14)` | `< I83` | [高 1 闭根](papers/output/y134259-owner-returns-20260928/HEIGHT-ONE-SEALED-PORT-BOUND.zh-CN.md) |
| `Y(C)` | `≤ R`；每个子项有固定有限梯形界 | [有限嵌套深度](papers/output/y134259-owner-returns-20260928/HEIGHT-ONE-SEALED-DEPTH-BOUND.zh-CN.md) |
| `Y(C,6)` | 后加强为 `< I29` | [递归索引闭包](papers/output/srpd-limit-y-lower-20261001/RECURSIVE-INDEXED-CLOSURE.zh-CN.md) |
| `Y(C,6^m)`，m≥1，幂表示重复 | `< I_(3m+26)`；`Y(C,6,7)≤R` | [有限返回层级](papers/output/srpd-limit-y-lower-20261001/FINITE-RECURSIVE-CLOSURE-BOUND.zh-CN.md) |
| `Y(C,6,7,9)` | `< I120` | [返回树极限](papers/output/srpd-limit-y-lower-20261001/EPSILON-TREE-RETURN-BOUND.zh-CN.md) |
| `Y(C,6,8)` | 后加强为 `< I120` | [反馈闭包](papers/output/srpd-limit-y-lower-20261001/FEEDBACK-CLOSURE-FIXED-CARRIER.zh-CN.md) |
| `Y(C,6,8,9)` 及随后有限头链、并列分支、带工作的叶 | `≤ R` 的逐段推进 | [全部中间稿](CATALOGUE.md)、[推进过程](PROOF-ROUTES.zh-CN.md) |
| `Y(C,6,8,10,12,13,14)` | `≤ R` | [有限生成等级](papers/output/srpd-limit-y-lower-20261001/GRADED-GENERATOR-CLOSURE.zh-CN.md) |
| `S9=Y(C,6,9)` | **`≤ R`，目前最高的完整节点记录** | [有限结构等级](papers/output/srpd-limit-y-lower-20261001/FINITE-STRUCTURAL-GRADE-CARRIER.zh-CN.md) |

“完整”指该节点的所有基本列项及其全部合法后代，不仅某几条有限轨迹。对每个 n 使用不同有限承载时，最后只能取非严格上界；不得把这些承载合并成一个未构造的固定有限目标。

这并未证明 `S9≤S(124842)`。主候选

```text
B = Y(1,3,4,2,5,8,10,4,9,14,17,10)
A = Y(1,3,4,2,5,8,10,4,9,14,17,9)
```

仍没有完整的 `B≤R`、`R≤B` 或等号；`A` 与 `S(124842)` 的完整比较同样未完成。没有据此证明嵌入不可能，也没有证明 `Y134259` 或 `Y1343≤R`。

## 5. 暂停前最后完成的局部工作

最后一批进展不提高上述完整 Y 下界，解决的是继续模拟时怎样保存和补充目标资源：

1. 全活根的共同容量条件、第一／第二尖端高展开，以及同宽返回的保持。
2. 最大实际行的准备操作保留旧控制点；外部控制点登记有精确更新公式。
3. 一次性预留 `k+2` 枚辅助列，连续执行 k 次有限准备，最后接回原源步，不在准备间插入额外 Y 步。
4. 在存在合适内外控制点的前提下，一次补偿使绝对行余量足够，随后**整个纯普通展开阶段**不按步数持续扣费。

完整定义、逐边公式与量词见[局部接口一节](PROOF-ROUTES.zh-CN.md)。仍缺的是**任意合法高阶交替下，这些合适控制点始终可用**的全路径定理。不能把有限准备可组合、一次调用成功或普通阶段闭合写成 B 的全局比较。

## 归档范围

原稿保留中文；总览、推导导读和证据说明提供中英双语。这不是将全部长证明重新翻译一遍。每份稿件附归档提示，原稿 SHA-256、整理后 SHA-256、删去章节及原行号都列在 `manifest.json`。没有随文打包的外部研究脚本改为明确的来源记录，不伪装为可点击文件。

旧的 73 项可运行档案未更改。本次导入的历史 NER 文件保留原规则和保护阈值；它们不自动实现最新 S9 论证。检查命令见[证据说明](EVIDENCE.zh-CN.md)。
