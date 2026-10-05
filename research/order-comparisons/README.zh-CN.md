# 序型大小比较与嵌入 · [English](README.md)

整理日期：**2026-09-20**。本页汇集已有比较文稿，不表示本轮重新审计了全部证明。“纸面结果”指原稿给出了全称论证，**不等于端到端 Lean 比较证书**；有限回归数据只是辅助证据。

原语言证明稿及所需数学辅助稿放在 [proofs](proofs/) 中。链接已重定位，私人机器路径已脱敏；历史命令可能依赖未收录的脚本。原稿中的旧进度和“未改仓库”属于历史记录。[导入来源清单](import-manifest.json)保留所选源文件和哈希。这里不收录 PPS4S 内容。

## 1. 对象与版本约定

2026-10-06 补充：[SRPD／TBMS／Y 暂停时总览](../srpd-tbms/continuation/README.zh-CN.md)及[完整推导导读](../srpd-tbms/continuation/PROOF-ROUTES.zh-CN.md)收录后续正向结果，包括 D44 的全体 TBMS 承载、ω³ 行节点等号和有历史前提的 Y(S9) 下界。下述 9 月 28 日说明是旧基线，不代表最新进度；两层清单均不改动本页原冻结导入记录。

2026-09-28 新增：[SRPD／TBMS 双语分析](../srpd-tbms/README.zh-CN.md)、[最终路线材料及复现导读](../srpd-tbms/archive/README.zh-CN.md)及[公共初段对应](../../notations/SRPD/correspondence.zh-CN.md)。SRPD 起点的严格后代域对应 RPD `1,2`、ARD／ARD2 `1,1,3`、IPD `1,2` 及普通 e0MN `1,3` 以下；有限底部与端点指标须作指定对齐。TBMS 总结记录整个普通 TBMS 的纸面承载界、`()(1^ε₀)` 的专用改进和仍未解决的 `…6,7,9`，不增加 Lean 比较证书。本次材料只保留最终路线的实际依赖；新总结及清单独立于下述冻结的历史导入清单。

2026-09-23 新增：双语 [BMS 到 FMP 证明](../../proofs/paper/bms-le-fmp-12242444.zh-CN.md)直接针对原始 FMP，附自包含有界核验。它与未改动的历史导入清单分开记录。

- “整个 X”指不含外顶端的有限**标准生成域**；“X(s) 以下”指相应文稿指定的标准严格后代锥。任意 raw 输入上的反例不自动是标准域反例。
- $X\hookrightarrow Y$ 表示严格保序嵌入，不自动包含像为初始段、满射、计数保持或基本列逐指标交换。
- 以下等号指相应初段的序型相同，有限底部和端点按原稿处理；不概括成原始数据和 `FS_short` 全部字面一致。
- 未明确写 **strong** 时，e0MN 一律指 **@test_alpha0 发明的普通版**。[两份计数加速 NER](../../external/README.zh-CN.md)各自保留原展开规则。“新版 strong”特指基于 `strong_e0MN (1).js` 的 2026-09-19 版本，连省略的系数 1 也搬运，不是旧 strong 版本。
- ARD、ARD2 指仓库当前 skyline 版。wY 指 **omega-Y weak magma**，不是 weak omega-Y。wY／CWY2 比较仍依赖文稿明列的 wY 有限引理；私人来源稿不在此转载。
- 向未证良序的目标嵌入，只给出一个良序**副本**，不证明目标全局良序。把结论写成目标的序数值不等式，需要该目标具备相应良序解释。本页尤其不证明整个 e0MN、ACD、CSD 良序；**ICP 则已知不良序**。

## 2. 普通 e0MN 中的整体上界

下表目标均是实际标准式；原稿将源域嵌入其严格后代。均不声称最小上界或等号。最后一行特意只写 IPD 初段，不是整个 IPD。

| 来源 | 普通 e0MN 目标计数 | 完整目标列表 | 证明稿 |
| --- | --- | --- | --- |
| 整个 RPD | `1,3,13,2` | `()(1:ω)(2:ω2)(1:1)` | [较紧上界](proofs/rpd-e0mn-tighter-20260917/RPD-le-e0MN-13132.zh-CN.md) |
| 整个 ARD | `1,3,14,1,6,54` | `()(1:ω)(2:ω^2)()(4:ω)(5:ω^2+1)` | [ARD 嵌入](proofs/ard-e0mn-cover-20260917/ARD-le-e0MN.zh-CN.md) |
| 整个 ARD2 | `1,3,14,1,6,185` | `()(1:ω)(2:ω^2)()(4:ω)(5:ω^3+ω+1)` | [ARD2 嵌入](proofs/ard2-e0mn-cover-20260917/ARD2-le-e0MN.zh-CN.md) |
| 整个 wY／CWY2 | `1,3,14,2` | `()(1:ω)(2:ω^2)(1:1)` | [CWY2／wY 嵌入](proofs/cwy2-e0mn-cover-20260917/CWY2-wY-le-e0MN.zh-CN.md) |
| IPD `1,3` 以下 | `1,3,11` | `()(1:ω)(2:ω+1)` | [IPD 低段论证](proofs/ipd-e0mn-20260917/README.zh-CN.md) |

第一行的 `ω2` 是 $\omega\cdot2$，不是 $\omega^2$。这些界均低于普通 e0MN `1,4`。旧的 [RPD `1,4` 上界稿](proofs/rpd-to-e0mn-20260917/RPD-le-e0MN-14.zh-CN.md)保留作辅助历史材料，当前采用上表更紧的界。共同上界**不能**判断 ARD／ARD2 与 wY 的大小。

## 3. 精确低段对应

| 对应 | 范围与注意事项 | 证明稿 |
| --- | --- | --- |
| 普通 e0MN `1,3` = RPD `1,2` | 非零后代锥补首空列；写成序数相等时须单独对齐有限底部。 | [证明](proofs/e0mn13-rpd12-20260919/README.zh-CN.md) |
| 新 strong e0MN `1,2` ≅ RPD `1,2` | 指定投影下默认基本列逐指标及计数保持；短展开的有限截断点不同。 | [证明](proofs/strong-e0mn-counting-20260919/RPD-12-correspondence.zh-CN.md) |
| 普通 e0MN `1,3` = ARD `1,1,3` | 首空列和底部边界修正；端点基本列有指标偏移。 | [证明](proofs/e0mn-ard-embedding-20260917/README.zh-CN.md) |
| 普通 e0MN `1,3` = IPD `1,2` | 标准域上的商／投影对应，包括底部边界。 | [证明](proofs/ipd14-e0mn-20260917/e0MN-13-equals-IPD-12.zh-CN.md) |
| ICP `1,2` ≅ RPD `1,2` | 两个种子后代域的祖先表对应，保持默认指标及计数。 | [证明](proofs/icp-candidate-20260919/RPD-ICP-flat-correspondence.zh-CN.md) |
| ICP `1,2,4` = RPD `1,2,5` | 指定平面片段的双向序嵌入；不是整个 RPD，也不声称基本列逐项相同。 | [证明](proofs/icp-candidate-20260919/RPD-zero-row-sector-below-ICP-124.zh-CN.md) |
| ACD `1,2,3,5,9,5` = 普通 BMS 极限 | 这个初段良序；整个 ACD 良序性仍未决。 | [证明](proofs/new-notation-20260918/ACD-123595-equals-BMS.zh-CN.md) |

ICP 的更高标准无穷链不否定这些低段对应。不能给**整个** ICP 指定序数序型，详见[反例稿](../../notations/ICP/non-well-founded.zh-CN.md)。

## 4. 其他下界

| 来源 | 目标 | 证据与边界 |
| --- | --- | --- |
| 整个 wY | 当前 skyline RWD | [定义及纸面论证](proofs/substantive-wy-20260914/SKYLINE-WORDS.zh-CN.md)、[全局覆盖桥](proofs/substantive-wy-20260914/GLOBAL-COVER-BRIDGE.md)、[下界独立审计](proofs/substantive-wy-20260914/LOWERBOUND-INDEPENDENT-AUDIT.md)。得到 $\mathrm{wY}\le\mathrm{RWD}$，未证严格更大或增幅显著。 |
| RPD 至 `1,2` | ACD 至 `1,2,4` | [局部嵌入](proofs/new-notation-20260918/ACD-RPD-embedding-progress.zh-CN.md)，包括文稿指定端点，不是整个 RPD。 |
| 整个普通 BMS | CSD `1,1,2,5,2` 以下 | [收紧上界](proofs/csd-20260917/BMS-small-bound.zh-CN.md)及[完整嵌入构造](proofs/csd-20260917/BMS-embedding.zh-CN.md)，不预设 CSD 全局良序。 |
| 整个普通 BMS | ICP `1,1,2,4,2` 以下 | [嵌入稿](proofs/icp-candidate-20260919/BMS-below-11242.zh-CN.md)，不宣称整个 ICP 良序。 |
| 整个普通 BMS | FMP `1,2,2,4,2,4,4,4` 以下 | [双语证明](../../proofs/paper/bms-le-fmp-12242444.zh-CN.md)。原始复制指标；序型解释采用配套 ZFC + I3 稿。不声称等号、最小性或 Lean 证书。 |
| 整个普通 BMS | IBLP `initial[0][1]` | **有条件的纸面结果；假设紧接下文。** [证明稿](proofs/iblp-bms-20260918/IBLP-01-BMS-lower-bound.zh-CN.md)。 |

**IBLP 的额外假设：** $A=\mathrm{initial}[0][1]$ 的任意严格合法后代继续展开时，既不触发原生补全，也不触发标记补全。$A$ 自己生成 $A[n]$ 时仍照原规则执行补全。该假设在此是**采用的前提，并未证明**。在此前提下，原稿把整个普通 BMS 标准域保序嵌入 $A$ 的实际严格后代；没有证明反向上界、等号或目标整个下段良序。`[0][1]` 是从 `initial` 开始的路径，不是十进制数字或计数串。

RWD 归档稿还给出含完整集合归纳的 $KP_\omega+\text{存在不可数序数}$ 下的纸面良序论证；这是 wY 下界的背景，不是本次新增 Lean 项目。不能用旧自由版 RWD 的 no-skip 猜想替代当前 skyline 版证明。

## 5. 仓库已有比较与仍未解决的问题

仓库此前已收录 $1Y\le\mathrm{RPD}$、整个 RPD 嵌入 ARD `1,2` 以下、整个 ARD 嵌入 ARD2 `1,3` 以下，以及 CWY2 ≅ wY。参见 [Y→RPD](../ordinal-comparisons-20260914/archive/ipd-upper-bounds/Y-le-RPD-proof.zh-CN.md)、[RPD→ARD](../../proofs/paper/rpd-le-ard-a2.zh-CN.md)、[ARD→ARD2](../../proofs/paper/ard-le-ard2-13.zh-CN.md)、[CWY2 等价](../../proofs/paper/cwy2-equivalence.zh-CN.md)。本档案补充这些论文，不扩张它们的形式化范围。

本次没有完成：`Y133 ≤ RPD12`、整个 ARD2 与 wY 的大小比较、由表中 IPD 低段推出整个 IPD 的嵌入、整个 ACD→RPD／ARD2、ACD／CSD 全局良序、e0MN 上界最优性或等号，以及与 Z3 的证明论序数比较。局部计数增长、相同公理上界和有限测试都不能代替嵌入证明。

## 6. 证明文件夹的阅读方式

上表直接链接主要结论稿。辅助稿保留较早的 ACD—BMS 界、非标准 BMS 行数引理、CSD 固定宽度及局部工作量论证、RWD 轮廓和标准域审计、RWD 使用的 IPD 弱 KP 树秩引理，以及 wY 有限复制审计。这些辅助稿中可能包含失败候选和明确未完成的章节，不能因为收录就将它们升级成额外定理。

部分依赖仍是外部结果，尤其原稿明确列出的 wY 来源论文和 BMS 已知定理。本次不收录私人来源 PDF、无界搜索进程，也不更改数学规则。新定义见 [ACD](../../notations/ACD/definition.zh-CN.md)、[CSD](../../notations/CSD/definition.zh-CN.md)、[ICP](../../notations/ICP/definition.zh-CN.md)；外部 e0MN 程序单独注明发明者。
