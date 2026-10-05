# Research notes / 研究文档

This directory keeps exploratory order-type comparisons separate from the well-ordering proofs in `proofs/paper/` and the Lean theorem collection. A paper argument, a finite program check, and a candidate upper bound are different kinds of evidence; archiving a note does not certify its conclusions.

本目录专门存放推导、比较思路与未完成结论，不与正式良序证明或 Lean 已验证定理混在一起。每份总结区分纸面论证、局部引理、程序核验及未证候选。

## DQDN collected results and proofs / 结论与证明（2026-10-06）

[English index](dqdn/README.md) · [中文总览](dqdn/README.zh-CN.md). The DQDN archive keeps the complete Chinese small-ordinal derivations, 41-row view table, epsilon-zero/tower proofs, Veblen and Buchholz carrier bounds, the BMS-to-TOP[2] comparison and the global PTO(Zω) lower-bound interface. English companions state the evidence boundary; the long location document is an explicitly condensed reading edition. Bounded portable helpers and tests are included under `dqdn/code/`, with runtime dependencies in `notations/DQDN/`.

DQDN 归档区分纸面等号、承载下界、原型核验和未决 PTO 上界；原 H(31) 更正及 b=32…35 尚未完成的上界状态均保留。新增目录不改变旧记号，也不新增 Lean 证明；整理不会重启已暂停的定时研究。

## 2026-09-14：IPD 与其他记号的比较

For the newer collected results, see the [2026-09-20 bilingual catalogue](order-comparisons/README.md): ordinary e0MN upper bounds, exact low segments, wY→RWD, BMS→ACD/CSD/ICP, and the conditional BMS→IBLP `initial[0][1]` argument. It links the original-language proof manuscripts and states their assumptions and non-Lean status.

较新的已整理结论见 [2026-09-20 双语总览](order-comparisons/README.zh-CN.md)：普通 e0MN 上界、精确低段对应、wY→RWD、BMS→ACD／CSD／ICP，以及有额外假设的 BMS→IBLP `initial[0][1]`。总览引用原语言证明稿，区分前提、全局良序状态与尚未 Lean 化的比较。

The remainder of this index describes the older 2026-09-14 archive. 以下其余说明针对旧的 2026-09-14 档案。

- [总览与结论状态](ordinal-comparisons-20260914/README.zh-CN.md)：所有候选的位置、计数、工作前提和证据等级。
- [IPD 上界候选与 Y≤RPD](ordinal-comparisons-20260914/01-bounds-and-y-rpd.zh-CN.md)：低段标志点，RPD、Y、wY、ARD、TPD 的编码与候选，以及 Y→RPD 纸面比较链。
- [ARD2 与 IPD](ordinal-comparisons-20260914/02-ard2-vs-ipd.zh-CN.md)：中间地址障碍、失败编码、候选 `A3[2]`（计数 `1,4,15`）、实际宏步和缺少的全局封闭性。
- [原稿与数据归档说明](ordinal-comparisons-20260914/archive/README.zh-CN.md)：关键推导原稿、历史核验记录和完整候选数据。

The notes are currently in Chinese. They include a paper-level Y≤RPD argument under its stated premises, not an end-to-end Lean comparison theorem. The proposed IPD bounds for the other systems, including ARD2, remain candidates.

## 阅读与复核边界

先读总结，再读 `archive/` 中的原稿。原稿的证明进展、时间和测试结果是历史记录；与较新总结有区别时，以明确标注的最新结论为准。共同的良序公理上界、局部编码或有限计数，不能代替两个序型的大小证明。

本目录只收录研究文档与候选 JSON 数据，不收录私人来源 PDF、实验代码、机器缓存或后台搜索结果目录。指向仓库内已有定义的链接已转换为相对链接；未收录的原工作区文件改为明确标注的路径记录，不伪装成可用下载链接。历史复核命令依赖那些未随文档归档的脚本，不能直接在新克隆的仓库中执行。

The older archive did not change notation definitions or expanders. The 2026-09-20 import adds the explicitly listed implementations without changing the existing formal proofs. See the [repository overview](../README.md) or [中文主页](../README.zh-CN.md).
