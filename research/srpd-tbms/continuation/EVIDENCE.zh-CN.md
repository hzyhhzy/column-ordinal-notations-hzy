# 证据、浏览器与复验边界 · [English](EVIDENCE.md)

[返回总览](README.zh-CN.md)。本次整理只做文件、链接和有限程序检查，不重新开展已暂停的数学研究。

[本次整理核验回执](ARCHIVE-VALIDATION.json)：300 份导入材料的身份与清单检查通过，3 个 JS 语法通过；包括主页入口在内的 304 份 Markdown、2,945 个相对文件链接通过。原 73 项档案完整性通过，6 项旧 smoke 回归均与原记录语义一致，全部子进程退出。这些不是数学正确性认证。

## 两层档案

`../archive/` 是原有的 73 项固定档案，包含 25 篇证明稿、模拟器及依赖，可按原命令复验。本次没有改动其正文、代码、哈希或历史核验记录。

本目录的 `papers/` 保存后续以及补齐依赖所需的正向证明稿／节选。`CATALOGUE.md` 逐篇列出，不以篇数冒充定理数。原稿中的实验和失败路线章节有选择地删去，删节标题、原行号和原始／整理后 SHA-256 记入 `manifest.json`；数学适用边界、条件性和未完成方向保留。未收录的脚本和旁支引用被明确标为来源记录。

本目录**不是整个历史实验工作区的可运行镜像**。长证明中列出的研究命令可能仍需未打包脚本，不应照抄后宣称已经复现。以下三个独立 NER 文件与原有档案的复现命令是例外。

## 已交付浏览器的固定副本

可在 [NER](https://smilelee-lyx.github.io/ne-rewritten/) 的“自定义记号”中导入。这些文件只作历史成果交付，不修改仓库现行记号。

| 文件 | 实际含义 | 范围与限制 |
|---|---|---|
| [Y → M13](explorers/Y-to-M13-order-embedding.ne-rewritten.js) | 展开 Y，并显示规范 M 像；有较小域上的严格保序纸面论证 | 顶端为 `Y(1,3,4,2,5,7,12,3)`，不是最新 S9 |
| [M13 ≥ Y 下界浏览器](explorers/M13-with-Y-lower-bound.ne-rewritten.js) | 按 M 展开，显示已知最大可用 Y 标签 | 标签可重复或跳过，不是逆嵌入、最优下界或精确等值器 |
| [TBMS ≤ SRPD](explorers/TBMS-le-SRPD.ne-rewritten.js) | 从 `B_(ε₀)` 按原 TBMS 默认基本列展开，显示持续模拟的 SRPD 状态 | 不是全体 TBMS；依赖历史，不保证全域内部保序 |

TBMS 浏览器另有“重选起点”视图：它为当前源式重新选覆盖，可能较小，但不保证沿点击历史持续下降。对称式默认承载也只是下界模拟，不是对称塔等号表。其[原说明](papers/output/srpd-tbms-explorer-20260927/README.zh-CN.md)和 [Y→M 原说明](papers/output/y-m13-order-embedding-20260920/README.zh-CN.md)一起保存。

未改变已有保护阈值或超限行为，计数显示不承担证明。新 S9 纸面论证没有现成的全锥 NER 转换器。本次只校验这些 JS 的语法与副本身份，不声称进行了新的浏览器 UI 或无限路径测试。

## 有限核验记录的准确作用

以下 JSON 是历史检查回执，不是本次重新运行的数学证书。`complete: true` 只表示那项有限任务完成；并不表示穷尽源后代。报告中原有队列未处理量、有限深度或轨迹停止条件仍有效。

| 回执 | 检查内容 | 不能替代的量词 |
|---|---|---|
| [递归冠带](evidence/output/tbms-srpd-equalities-20260929/RECURSIVE-VERIFICATION.json) | 多 Q 下界、递归解释和定向搬运；包含真实原步及持久行轮廓检查 | 所有 k、所有后代的森林势归纳 |
| [有限最高行库](evidence/output/tbms-srpd-equalities-20260929/FINITE-ROOF-VERIFICATION.json) | D44 块公式、初始库容量及若干连续路径；另含有未处理队列的有限探针 | 全 L 持续模拟，更不是反向上界 |
| [最大行准备](evidence/output/srpd-limit-y-lower-20261001/MAXIMAL-HEIGHT-ARCHIVES-DIAGNOSTIC-1.json) | 6,786 对已选容量不变，保留旧控制并再次调用 | 任意未来总有可用控制 |
| [外部控制放大](evidence/output/srpd-limit-y-lower-20261001/EXTERNAL-DAMAGED-RESERVE-DIAGNOSTIC-1.json) | 一个已损耗内部储备仍由更早外点放大的成功实例 | 总能及时放大 |
| [外部登记](evidence/output/srpd-limit-y-lower-20261001/EXTERNAL-CONTROL-REGISTRY-DIAGNOSTIC-1.json) | 11、10、5 号控制的连续准备，74 个控制快照 | 无限或全路径供应 |
| [有限准备计划](evidence/output/srpd-limit-y-lower-20261001/BUFFERED-PREPARATION-PLANS-DIAGNOSTIC-1.json) | 两／三次准备后只执行原定一个源步，最大目标宽 5,327 | B 的整个后代锥 |
| [独立小目标父表](evidence/output/srpd-limit-y-lower-20261001/BUFFERED-PUMPS-INDEPENDENT-VERIFICATION-1.json) | 12 例、90 个 FS、594 个同宽 down、570 个截行归一化宏；最大宽 267 | 这只是目标骨架检查，不是实际数值 Y 全路径验证；宏未全部逐 FS 暴力回放 |

最高完整 S9 下界是有前提的纸面结果，不能由这些有限回执“认证”。文件身份检查也不能认证它的历史基础链。失败日志未作为证据收入；这不表示历史上全部实验均成功。

## 从仓库根目录检查

仅验证本次档案：

```powershell
node --max-old-space-size=256 research/srpd-tbms/continuation/verify.cjs
```

该脚本只读，检查精确文件清单、LF 规范化哈希、JSON 可读性、三个展开器语法及本目录 Markdown 的相对文件链接。不展开记号、不联网、不写文件、不启动后台进程，**不检查数学证明正确性或标题锚点语义**。

加 `--entry-points` 可同时检查本次更新的七份仓库入口文档。

检查原固定档案并运行其已有小型回归：

```powershell
python -B research/srpd-tbms/archive/verify_archive.py
python -B research/srpd-tbms/archive/run_checks.py --suite smoke
```

旧运行器顺序执行子进程，单例外部时限 30 秒、Node 堆 512 MiB，并保留原模拟器宽度／步数／RSS 保护，超时会终止并回收子进程。这里只列原有复验能力；研究仍暂停，不安排后台搜索。更长 `current` 套件及其两个已知宽度保护记录见[旧导读](../archive/README.zh-CN.md)。
