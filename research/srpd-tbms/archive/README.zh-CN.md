# SRPD／TBMS 最终路线材料与阅读顺序 · [English](README.md)

整理于 **2026-09-28**。本目录只保留[比较汇总](../README.zh-CN.md)中两条最终路线的证明依赖：**整个普通 TBMS 的递归行库承载**，以及 **`()(1^ε₀)` 的固定有限库承载**。不再按“提到过的文件”递归收录所有探索。

[清单](manifest.json)固定 **73 份材料**：25篇证明／引理文稿、39份运行与核验代码、2份当前路线的原始核验记录，以及7份必要上游源码／编译文本。旧等号尝试、无关候选搜索、障碍研究和旧核验批次不在本包内。仓库外原始研究文件未删除。

**这是纸面证明材料，不是 Lean 证书，也不表示此次独立终审了全部数学论证。** 原稿主要保留中文；本导读和上层总结有中英两版。早期引理使用的旧合同要结合后续逐项修改阅读。

## 1. 最短的完整阅读路线

先读 [SRPD 定义](../../../notations/SRPD/definition.zh-CN.md)及[公共初段／良序转移](../../../notations/SRPD/correspondence.zh-CN.md)。目标良基性依赖仓库已有 RPD 证明，而不是本档案内的有限测试。普通 TBMS 的原生代码和出处见[来源说明](vendor/README.zh-CN.md)。

以下顺序阅读。不能跳过中间引理而把最后两篇当成独立证明。

| 顺序 | 要解决的问题 | 完整原稿 |
| --- | --- | --- |
| 1 | 反射后各类祖先容量怎样变化，接缝是否也算进去 | [完整反射容量公式](output/tbms-e0mn-bridge-20260925/FULL-REFLECTION-CAPACITY-INTERFACE.zh-CN.md)、[前缀行搬运协变](output/tbms-e0mn-bridge-20260925/PREFIX-ROW-STRETCH-COVARIANCE.zh-CN.md) |
| 2 | 真实末列操作如何维持主点、三条辅助列以及父返回 | [主包与父更新](output/tbms-e0mn-bridge-20260925/PACKET-MAIN-AND-PARENT-RENEWAL.zh-CN.md) |
| 3 | 旧行标签如何常驻并在以后重新调用；如何供应越来越大的有限需求 | [常驻 ε 库](output/tbms-e0mn-bridge-20260925/PERSISTENT-EPSILON-BOUND.zh-CN.md)、[分级资源](output/tbms-e0mn-bridge-20260925/GRADED-RESOURCE-BOUND.zh-CN.md)、[可放大资源](output/tbms-e0mn-bridge-20260925/AMPLIFIED-RESOURCE-BOUND.zh-CN.md) |
| 4 | 行标签的累计端点为何仍在源标准域；登记路径如何取得 | [普通行端点闭包](output/tbms-e0mn-bridge-20260925/NATIVE-ROW-ENDPOINT-CLOSURE.zh-CN.md)、[递归端点闭包](output/tbms-e0mn-bridge-20260925/RECURSIVE-ENDPOINT-CLOSURE.zh-CN.md) |
| 5 | 任意固定有限层数的库、递归调用、次协变和主源步骤如何共同闭合 | [递归行库的全后代证明](output/tbms-e0mn-bridge-20260925/RECURSIVE-ROW-BANK-BOUND.zh-CN.md) |
| 6 | 如何从一个固定目标准备任意有限层，而不是随层数重新选目标 | [固定子项承载整个 TBMS](output/tbms-e0mn-bridge-20260925/FIXED-CHILD-WHOLE-TBMS.zh-CN.md) |
| 7 | 哪些访问边可以从两行减为一行，主区恢复如何真实支付 | [单行访问的完整修改证明](output/tbms-e0mn-bridge-20260925/ONE-PORT-WHOLE-TBMS.zh-CN.md) |
| 8 | 目标式如何通过真实下降继续压低 | [缩减种子](output/tbms-e0mn-bridge-20260925/TRIMMED-ONE-PORT-SEED.zh-CN.md)、[最新弱归档种子](output/tbms-e0mn-bridge-20260925/WEAK-ARCHIVE-SEED.zh-CN.md) |

第8步最后一篇 §4 逐项核对新的弱化条件，§5 在选择递归深度之前固定共同状态 V，再取源顶端子项的上确界。这就是整个普通 TBMS 的当前界：

$$\rho(\mathrm{TBMS\ Limit})\le\rho(V)<\rho(Q_w)<\rho(W[1])<\rho(W).$$

这里 W 的计数为 `1,2,4,8,4,2`；V、Qw 的精确父图和计数见[上层汇总](../README.zh-CN.md)及[原生路径测试](../../../tests/srpd_tbms_bounds.cjs)。**上确界处只写 ≤，严格号来自后面的真实目标下降。**

### 较小目标 `TBMS ()(1^ε₀)` 的路线

读完上述有限库合同后，接着读[固定两行行标签库证明](output/tbms-e0mn-bridge-20260925/EPSILON-FIXED-BANK-BOUND.zh-CN.md)。它的 §§2—3 说明为何最大标签 ε=`()(1,1)` 可以直接作为容量4的有限库常驻，§§4—5 给出更小种子的完整实际路径和任意源宽初始化。它不依赖“任意多递归层”的最高模板。

此处得到 E=`()(1^ε)`、J=`()(1^ε,1)` 的

$$\rho(E)<\rho(J)\le\rho(C_\varepsilon).$$

Cε 的计数为 `1,2,4,8,4,1,2,9,38,4,9,10,17,51`。原稿中另行讨论候选搜索的 §7 不参与此证明，本版省略；没有因此新增更小承载界或最优性结论。

## 2. “怎么嵌入”的准确含义与操作流程

这些原稿构造的是**持续的基本列下降模拟**：状态同时保存源式、目标式、各层行标签字典、物理代表点、归档、主包和剩余调用券。每个源步必须在同一个目标的真实后代里继续，不允许中途重选起点或免费补图。

对源指标 n 给定后，操作顺序是：

1. 按原生 TBMS 规则取得子项，并列出本次新出现的累计行端点。
2. 用最近已登记上端点规划有限细化路径；递归涉及的更低层先规划，不循环预设整个 TBMS 良序。
3. 先以真实目标下降支付该计划所需的有限张调用券。
4. 每次激活已有归档消耗一张券；按删除、单位末段、递归极限末段分支分配新库。较小旧库可留在原处，较大库随复制搬运。
5. 所有新端点登记后，实现真正的主源步骤，实际删回健康的主辅助列，并恢复所选归档的工作状态。
6. 验证全部库、主包、归档及行码的不变量，为任意下一指标保留同一合同。

最新合同的关键区别不能混淆：有限库对**所有点对，包括源非边**保留 `2 + 行码需求` 的容量背景；一般访问端口只需1；最高库的控制背景仍需2，内部高对仍需 H>r，只把“内部高对到归档”的要求降到1。不是把所有常数2一起改成1。

据目标良基秩归纳，这种每步非空的模拟给出上述秩界。**它不是已交付的“每个 TBMS 式唯一对应一个 SRPD 式”的规范保序翻译，也不要求同指标基本列交换。** 初段同构与跨系统秩模拟是两件不同的事，不能把前者的结论套到这里。

## 3. 纸面步骤与程序入口对照

| 纸面部件 | 仓库内实现 |
| --- | --- |
| 普通 TBMS 原生规则 | [原始 TypeScript](vendor/ne-rewritten/src/notations/BM-like/TBM.ts)、[有时限加载器](output/tbms-e0mn-bridge-20260925/load-tbm.cjs) |
| SRPD 的当前隐含根规则 | [公开展开器](../../../notations/SRPD/SRPD.ne-rewritten.js)、[归档精确快照](output/m13-lists-20260926/SRPD.ne-rewritten.js) |
| 反射容量、稀疏原生目标、主包操作 | [容量](output/tbms-e0mn-bridge-20260925/full-reflection-capacities.cjs)、[稀疏状态](output/tbms-e0mn-bridge-20260925/packet-sparse-native-state.cjs)、[主包](output/tbms-e0mn-bridge-20260925/packet-main-cover.cjs) |
| 暴露、局部降低、截行等宏的有限下降证书 | [独立局部证书](output/e0mn-y13425810-20260920/finite-local-certificate.cjs) |
| 递归登记和全状态不变量 | [递归内核](output/tbms-e0mn-bridge-20260925/packet-recursive-row-bank-cover.cjs)：`plan`、`register`、`prepareBudget`、`activate`、`allocateStep`、`allocateCeiling`、`step`、`check` |
| 最新整个 TBMS 模拟 | [弱归档版](output/tbms-e0mn-bridge-20260925/weak-archive-row-bank.cjs)，在[单行版](output/tbms-e0mn-bridge-20260925/one-port-recursive-row-bank.cjs)上应用精确列明的差异 |
| ε₀ 行标签专用模拟 | [固定有限库版](output/tbms-e0mn-bridge-20260925/epsilon-fixed-row-bank.cjs) |

几个增量实现对旧模拟器执行**检查匹配次数的精确文本替换**，然后在内存中载入；全部被替换的原始模块也已收录。补丁作用于模拟接口，不改 TBMS 或 SRPD 的原生规则。`*.generated.cjs` 是内存模块名，不是遗漏的磁盘文件。

`output/` 下保留研究时的相对目录布局，便于逐条追踪引用。不要把其中旧版显式根辅助器与当前 SRPD 隐含根版混用；各模块按其原接口加载。数学断言、预算和失败分支未为了让测试通过而删除。

## 4. 必要辅助引理

第1节列出主线；下列较早的材料仍被主线实际调用，故保留其论证，不能仅因文件较早就删除。

| 用途 | 依赖材料 |
| --- | --- |
| 有限需求的放大与严格资源分离 | [严格分离](output/tbms-e0mn-bridge-20260925/STAR-RESOURCE-STRICT-SEPARATION.zh-CN.md)、[额外副本资源](output/tbms-e0mn-bridge-20260925/crossing-lower-extra-copy-resource.zh-CN.md) |
| 有限多层与固定 ε 标签的持续维护 | [分层资源](output/tbms-e0mn-bridge-20260925/LAYERED-RESOURCE-BOUND.zh-CN.md)、[ε 行标签](output/tbms-e0mn-bridge-20260925/EPSILON-ROW-BOUND.zh-CN.md)、[普通行库](output/tbms-e0mn-bridge-20260925/NATIVE-ROW-BANK-BOUND.zh-CN.md) |
| 源端累计标签、有限断点与截行 | [整个 TBMS 接口](output/tbms-e0mn-bridge-20260925/WHOLE-TBMS-INTERFACE.zh-CN.md)、[多项式行](output/tbms-e0mn-bridge-20260925/POLYNOMIAL-ROW-BOUND.zh-CN.md)、[轮廓／截行引理](output/tbms-e0mn-bridge-20260925/RANKED-ROW-RESERVOIRS.zh-CN.md) |
| 真实辅助列与控制器维护 | [分隔的私有控制器](output/tbms-e0mn-bridge-20260925/SPACED-PRIVATE-CONTROLLERS.zh-CN.md)、[有限带](output/tbms-e0mn-bridge-20260925/FINITE-BAND-BOUND.zh-CN.md)、[ω 次数](output/tbms-e0mn-bridge-20260925/OMEGA-DEGREE-BOUND.zh-CN.md) |

“轮廓／截行引理”只保留原 §§1—3；最终源端闭包用到的是这里的截行事实，后面的反向嵌入候选不参与证明。弱归档稿的可继续压低障碍、固定 ε 稿的独立候选搜索也已注明省略。其余不参与证明的历史旁引标为文字，不再带入文件及其引用链。

代码采用实际导入闭包。有些文件仍沿用早期 Y／e0MN 研究的文件名，但最终模拟器调用其中的局部下降宏或加载器；保留它们不等于把早期探索结论并入主线。

## 5. 如何重跑核验

在仓库根目录运行；只需要 Python 标准库及 Node.js，不依赖原作者机器上的目录，也无需安装 TypeScript 或整个 NER 工程：

```sh
python -B research/srpd-tbms/archive/verify_archive.py
python -B research/srpd-tbms/archive/run_checks.py --suite smoke
python -B research/srpd-tbms/archive/run_checks.py --suite current
```

`current` 重跑最新弱归档的14个源／初始化例及1个付费局部例、共同状态检查、固定 ε 库12例，共28项。ε 库第3、8号案例预期触发宽度保护，单独归类为 **guarded**，不记作完成证明或完整通过路径。其他错误、超时或历史结果不一致仍令运行失败。

每个子进程只运行一个有界案例，外层30秒超时，Node 堆512 MiB，原程序仍有650 MiB RSS 检查和明确宽度／步数上限；顺序运行，不累积后台进程。超时会终止并回收该子进程。大数次固定指标倒数并非这些核验的策略。未默认执行全部历史搜索脚本。

[本次精简后核验](ARCHIVE-VALIDATION.json)与两份原始路线核验记录分开；保留的案例未改结果或保护状态。固定 ε 记录仅去掉了不属于此路线的候选搜索／分析字段，清单记录此改动。有限核验只检验实现和有界案例，**全称结论仍由前述纸面归纳承担**。

## 6. 完整性、来源和边界

[清单](manifest.json)逐文件记录原始哈希、发布哈希、最终路线角色及整理改动。上述节选／省略明确记录，保留的引理正文和模拟数学内核不变；原有路径脱敏、可移植加载器改动仍列明。此次精简没有改变公共 SRPD、其他记号或 Lean 模块。

随附必要的上游源码和固定编译输出，保留作者归属；[第三方来源与许可边界](vendor/README.zh-CN.md)不能省略。此次未证明源程序每一行正确、未形式化 TBMS 比较、未解决 `…6,7,9`，也没有把整个历史探索中的每项猜想变成定理。本包供读者沿最终路线检查实际用到的论证和实现，不充当整个研究历史的备份。
