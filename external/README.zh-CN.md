# 外部记号展开器 · [English](README.md)

**e0MN 和 strong e0MN 均由 @test_alpha0 发明，不是仓库作者或本项目 AI 辅助设计的新记号。** 为方便阅读[大小比较文档](../research/order-comparisons/README.zh-CN.md)，在此单独收录。

| 记号 | 独立 NER 文件 | 固定版本 |
| --- | --- | --- |
| 普通 e0MN | [计数加速 JS](e0MN/e0MN-fast-counting.ne-rewritten.js) | 2026-09-17 优化计数版，基于提供的 `e0MN(美化版).js` |
| strong e0MN | [计数加速 JS](strong-e0MN/strong-e0MN-fast-counting.ne-rewritten.js) | 基于 `strong_e0MN (1).js` 的 2026-09-19 版，连省略的系数 1 也搬运 |

两份文件均保留 `Made by test_alpha0`。本地增补是精确计数显示与加速，不认领记号本身的发明。这里的 strong **不是**旧 `strong_e0MN.js` 变体；普通版、strong 版不能混用，默认 `FS` 与 `FS_short` 也没有被擅自合并。

在 NE Rewritten 的自定义记号中导入完整文件。两者注册 ID 不同，保留原记号、行高差和山脉图，另提供计数序列。计数使用 BigInt；地址和 CNF 系数仍沿用原版安全整数 Number 语义。资源超限只表示本次实现没有算完，不表示数学计数无限。

按要求不另写数学定义，也不添加 Python 移植，不声称整体良序。署名不等于获得许可；本次没有确认所提供原文件的再分发许可证，公开再分发前须保留署名并确认许可，见[来源说明](../SOURCES.zh-CN.md)。本次整理不包含提交或推送。
