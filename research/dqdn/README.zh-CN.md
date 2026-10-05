# DQDN 结论与证明 · [English](README.md)

本目录整理截至 2026-10-05 暂停研究时已有的数学工作。这次入库不重启定时研究。[实现入口](../../notations/DQDN/README.zh-CN.md) 与[良序论证](../../proofs/paper/dqdn-well-ordering.zh-CN.md) 分开放置。

**证据约定：** 下表的“纸面结果”表示收录文稿给出了相应论证，不表示已经独立审稿或 Lean 认证。有限程序测试只验证实际检查过的路径与接口。尤其不能把末程序的源秩直接当作整个 TOP 标准承载式的序数。

## 主要结论

| 结论 | 证据与范围 |
| --- | --- |
| TOP 标准域全段良序 | [纸面论证](../../proofs/paper/dqdn-well-ordering.zh-CN.md)：全回答有类型正规化，加公共根的保序引理 |
| TOP[1]=ε₀ | [塔轮廓](tower-profiles.zh-CN.md)、[ε₀ 论证](epsilon0.zh-CN.md)；另需所有 System T 程序的统一上界 |
| ω 至一些较高幂，以及早期 TOP[2][n] | [定位稿](small-ordinals.zh-CN.md)，含 41 行三视图表；纸面精确分类到 n=65，不由有限测试证明 |
| ζ₀<TOP[2][524]，Γ₀<TOP[2][884] | 定位稿 §13 的紧凑迭代器论证；是承载下界，不是等号 |
| BHO<TOP[2][2690] | 定位稿 §9，采用原始 Buchholz 树约定；不是精确标准位置 |
| BO≤TOP[2] | 定位稿 §9.5；**BO 指 ψ₀(Ωω)**，不是 BHO |
| BMS(0⁴)(1⁴)<TOP[2]，lim(BMS)≤TOP[2] | [BMS 比较稿](bms-top2.zh-CN.md)：固定高度 BMS 及保留任意函数参数的 System F 抽取 |
| DQDN 全局极限 ≥ PTO(Zω) | [Girard 接口](girard-oracle-bridge.zh-CN.md)；有限阶全理解，不是仅有 System T |
| 全局极限 = PTO(Zω)，或 TOP[2]=PTO(Z₂) | **均未完成**；[反向上界义务](upper-bound-open.zh-CN.md) 仍保留 |

BMS 稿件中更细的比较链是

$$\sigma_4<\mathrm{PTO}(Z_2)\le |\mathrm{TOP}[2]|,
\qquad \lim(\mathrm{BMS})\le\mathrm{PTO}(Z_2)\le |\mathrm{TOP}[2]|.$$

没有假设或证明 lim(BMS)=PTO(Z₂)。也没有实现与基本列逐项交换的 BMS→DQDN 转换器，或算出具体 n 使四行 BMS 种子已经小于 TOP[2][n]。

## 阅读路线

1. [定义](../../notations/DQDN/definition.zh-CN.md)：普通计算、28 个生成入口、标准性与列比较。
2. [良序](../../proofs/paper/dqdn-well-ordering.zh-CN.md)：类型源、有限燃料、序数权重，以及为什么能覆盖任意字典序下降。
3. [塔轮廓](tower-profiles.zh-CN.md) 与 [ε₀](epsilon0.zh-CN.md)：区分压缩查询秩、一步源秩、独立图与标准承载式。
4. [定位稿](small-ordinals.zh-CN.md)：等号、小预算分类、Veblen/Buchholz 构造与三视图表。完整推导和更正历史保留在中文稿；英文配套明确为压缩阅读版，不冒称逐行全文翻译。
5. [BMS 比较](bms-top2.zh-CN.md)、[全局 Girard 接口](girard-oracle-bridge.zh-CN.md)、[未完成上界](upper-bound-open.zh-CN.md)。

主定义、使用说明和良序稿提供双语；六份研究稿有英文配套，其中很长的定位稿明确采用英文缩编。没有给发布检查加入整目录的单语豁免。

## 更正及未完成项

- 原 H(31)=ω·2+32 已撤回。当前纸面分类为 **H(31)=ω·3+32**，补上“返回的查询值继续控制后续循环”的影响；更正过程保留在 §10.4。
- b=32…35 的普遍上界仍未完成。`small_generator_ranks.py` 有 b>31 的下界见证及候选公式，不表示 n>65 的等号已证。
- `compact_type_author.py` 的类型复用实验进一步降低构造字段数，没有改变源程序。上面的主表使用有完整文稿推导记录的界，不把后续测得的每个字段数偷偷写成新的精确序数位置。
- ζ₀、Γ₀、BHO、BO 尚无精确标准名字。即使末独立源秩已知，主张等号时仍必须审计前置兄弟块。
- 尚无对象理论形式化、通用证明抽取器、优化后的弱公理上界或 DQDN Lean 项目。

## 程序与复核

[code/](code/) 保存上述文稿所需、对应当前核心规则的程序编写工具和有界测试。运行依赖均在 `notations/DQDN/`。不把旧 CCDN/LCDN/LQDN 候选前端、会话恢复工具、私人 PDF 和临时缓存当作 DQDN 发布。

在仓库根运行 `python -B tests/dqdn.py`，它设置本地导入路径，并以固定测试组和时间、图大小、步数、输出及内存预算运行。结果见[验收记录](validation.zh-CN.md)。旧 NER 宿主源码测试依赖另一个检出目录，本包不把它声称为可移植测试或真实浏览器实测。
