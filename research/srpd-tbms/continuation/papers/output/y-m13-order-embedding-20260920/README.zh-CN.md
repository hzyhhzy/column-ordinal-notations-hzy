# Y → 普通 M13：严格保序 NER 版

> 归档研究稿／Archived research manuscript — 2026-10-06。来源：`output/y-m13-order-embedding-20260920/README.zh-CN.md`。
> 本稿是有明确历史前提的纸面论证或局部接口，不是新增的 Lean 定理，也没有因归档而完成独立整链复核。文中“本轮／最新／目标”指原稿阶段；请以[现状总览](../../../README.zh-CN.md)为准。
> Proof/status guide: [English](../../../README.md). 实验／失败路线不单独展开；有删节时，原行区间及前后 SHA-256 见[清单](../../../manifest.json)。必要前提、适用范围和未完成方向仍保留。


导入文件：[Y-to-M13-order-embedding.ne-rewritten.js](../../../explorers/Y-to-M13-order-embedding.ne-rewritten.js)。

在 [NER](https://smilelee-lyx.github.io/ne-rewritten/) 的“自定义记号”中导入／启用该 JS，
选择 **Y → M13（保序嵌入）**。无需同时导入别的记号，文件不联网。

另有 [M13-with-Y-lower-bound.ne-rewritten.js](../../../explorers/M13-with-Y-lower-bound.ne-rewritten.js)：
以 M 为主、按 M 展开，旁边显示单调 Y 下界，见[单独说明](M13-LOWER-BOUND.zh-CN.md)。
两份可同时导入，不会互相覆盖；后者不是反向嵌入。

## 覆盖范围

源顶端为 **Y(1,3,4,2,5,7,12,3)**，其中 12 是一个数十二。
顶端映到普通 e0MN 的 **M13=`()(1:ω)`**。
严格在源顶端以下的标准式，映像都严格在 M13 以下。

这是本次按最大源范围实现的映射；**不保证每一个点的像都尽可能小**。
为隔开不同源分支，像中有不少辅助列，因此可能比以前单独计算的上界长很多。

## 如何阅读

默认显示 `Y(源数列) ↦ M(目标计数)`。箭头表示嵌入，不是等号。
等价表示菜单另有：Y→M 列表、只看 Y 数列、只看 M 计数、只看 M 列表。
若要检查或复制精确目标，选 **M 列表**；计数只是一种显示。

点击节点仍使用原 Y 的基本列，然后重新求该子项的规范 M 像。
不是按 M 的同一个基本列指标展开。不同路径到达同一个 Y 数列，得到相同 M 像。

这个转换满足：**源式严格增大，实际 M 像也严格增大**。
不是只保证每条点击路径上下降，也不是只给每个点一个各不相干的上界。
保序性有[纸面论证](ORDER-EMBEDDING.zh-CN.md)，依赖前一轮分级带／闭合块模拟；尚未 Lean 形式化。

## 计算限制

一次映射约 650ms，Y 最多 96 列，实际 M 目标少于 1200 列，缓存最多 96 个像／300万字符。
超限只显示“映射计算超限”，不会换用猜测值。Y 的基本列和比较仍可使用。
计数另有 40ms 的显示预算：能算出的保留，后面显示 `?`；完整目标仍可在列表视图查看。

## 复验

在工作区根目录运行：

```powershell
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-prototype.cjs
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-order-laws.cjs
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-ner.cjs
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-ner.cjs --deep
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-ner-host.cjs
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-lift-traces.cjs
node --max-old-space-size=512 output/y-m13-order-embedding-20260920/check-m-lower.cjs
```

脚本有时间／宽度／内存限制；不执行大数次暴力 T 迭代，不启动后台服务。
JS 是独立文件；复验脚本和打包器依赖工作区内原研究模块。
本次没有修改已发布的 Y、M 或 RPD 展开器，也没有 commit／push。
