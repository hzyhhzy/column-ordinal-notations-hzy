# 推导原稿与候选数据归档

[返回研究总览](../README.zh-CN.md) · [研究目录](../../README.md)

本目录保存三份总结背后的关键文稿。它们是研究材料，不是新增的 Lean 定理或完整跨记号比较认证。原有工作区文件保留，本次只制作仓库内可读的文档副本。

## 1. IPD 候选与 Y≤RPD

| 文件 | 内容及阅读状态 |
| --- | --- |
| [最新状态索引](ipd-upper-bounds/STATUS.md) | 原研究结束时采用的最终编码与被取代方案 |
| [IPD 上界总稿](ipd-upper-bounds/IPD-upper-bounds.zh-CN.md) | 低段标志点及第一阶段八项目标；较新的缩紧以接下来两稿为准 |
| [RPD、Y、wY 缩紧](ipd-upper-bounds/RPD-Y-wY-tightening.zh-CN.md) | 固定保留列、右梳与有限祖先词编码 |
| [ARD、TPD 缩紧](ipd-upper-bounds/ARD-TPD-tightening.zh-CN.md) | 移动行锚、形状／数字词分离及最新十列候选 |
| [Y≤RPD 纸面比较](ipd-upper-bounds/Y-le-RPD-proof.zh-CN.md) | V/F 不变量、控制边预降、最小覆盖映射；有前提的纸面论证，未端到端 Lean 形式化 |
| [历史测试记录](ipd-upper-bounds/TEST-REPORT.md) | 有界样本、成功数、跳过项、标准路径重放及资源限制 |
| [完整候选数据](ipd-upper-bounds/bounds.json) | 可输入列表、精确计数、标准路径，也保留已被取代的历史候选 |

## 2. ARD2 与 IPD

| 文件 | 内容及阅读状态 |
| --- | --- |
| [Full-Context 强度限制稿](ard2-ipd-bound/full-context-strength.md) | 浅层静态编码、地址字母表差异与不能据此推出上界的原因 |
| [第一轮比较审计](ard2-ipd-bound/REPORT.zh-CN.md) | SELF 截断、固定距离和精确抬父的障碍；“尚无具体候选”是该轮的历史状态 |
| [后一小时报告](ard2-ipd-bound/HOUR-REPORT.zh-CN.md) | 新候选 U、统一种子首步、五条实际宏步和缺少的全局关系 |
| [机器核验记录](ard2-ipd-bound/VERIFICATION.json) | 当时的源码哈希、重放结果、未完成搜索和 `ordinal_comparison_proved: false` |

候选 U 的计数 `1,4,15` 在三份新总结中补记；旧 JSON 没有这一字段，不擅自伪造当时的机器记录。五条宏步采用后一小时报告中的修正版，尤其保留第五条中间的 `pref_11` 删尾。

## 3. 归档时作了哪些处理

1. 数学公式、候选数据、失败见证及历史测试结果按原稿保留；增加“历史研究稿”提示，不将探索性内容升级为定理。
2. 原工作区 `output/ipd-upper-bounds-20260914/` 的文稿和数据收在 `ipd-upper-bounds/`；`output/ard2-ipd-bound-20260914/` 的文稿和记录收在 `ard2-ipd-bound/`。另收录原 `output/simple-ipd-20260914/full-context-strength.md`，以保持 ARD2 静态编码论证的上下文。
3. 已归档文稿之间、以及正式仓库内已有文件的链接改为正确相对路径。其余原工作区引用改为普通路径说明，标明未归档。不得据此认为脚本或旧审计工程已经收录。
4. 不复制私人来源论文；原稿中出现的本机用户目录去掉，只保留论文标题和必要的文献定位。归档版本因此不是逐字节原始文件备份。
5. 原记录中的代码 SHA-256 标识当时的研究快照，不担保仓库后来同名代码仍与其相同。文中实验命令以原工作区为基准，不能当成此目录提供了可独立运行的完整实验环境。

关于记号本身的当前良序证明，应查 [IPD 定义](../../../notations/IPD/definition.zh-CN.md) 与 [ARD2 定义](../../../notations/ARD2/definition.zh-CN.md) 的正式说明，而不是复用旧研究稿的进度判断。
