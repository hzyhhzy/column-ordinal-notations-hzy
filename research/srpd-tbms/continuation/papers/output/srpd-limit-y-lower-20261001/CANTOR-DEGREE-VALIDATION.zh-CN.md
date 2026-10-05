## 当前版本的完整成功

> 归档研究稿／Archived research manuscript — 2026-10-06。来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-VALIDATION.zh-CN.md`。
> 本稿是有明确历史前提的纸面论证或局部接口，不是新增的 Lean 定理，也没有因归档而完成独立整链复核。文中“本轮／最新／目标”指原稿阶段；请以[现状总览](../../../README.zh-CN.md)为准。
> Proof/status guide: [English](../../../README.md). 实验／失败路线不单独展开；有删节时，原行区间及前后 SHA-256 见[清单](../../../manifest.json)。必要前提、适用范围和未完成方向仍保留。


12个完整成功例合计184.358秒、54次付费调用、12次真主删除；最大稀疏宽147783，结束RSS最高421.78MiB。
每例上限40秒、RSS1000MiB、Node堆700MiB、宽420000、至多9次付费调用；未扩大这些限额。

| 范围 | 成功记录 | 说明 |
|---|---|---|
| 指数1降低到0 | 删除（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-FINITE-ONE-VERIFICATION.json`）、单位步（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-FINITE-UNIT-VERIFICATION.json`）、正截行（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-FINITE-LIMIT-VERIFICATION.json`）、非邻接父（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-FINITE-NONLAST-VERIFICATION.json`） | 覆盖专用末点复制和完整返回 |
| 指数2降低到1 | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-FINITE-TWO-VERIFICATION.json`） | 真实产生非均匀末间隙 |
| 指数ω降低到2 | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-OMEGA-DELETE-VERIFICATION.json`） | 两次工厂，紧凑外控制 |
| 指数ω²降低到ω | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-OMEGA-SQUARED-VERIFICATION.json`） | 两次工厂，紧凑外控制 |
| 指数ω³降低到ω² | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-OMEGA-CUBED-VERIFICATION.json`） | 两次工厂，紧凑外控制 |
| 高前缀及极限尾 | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-MIXED-LIMIT-VERIFICATION.json`） | ω²+2ω降低到ω²+ω+2，紧凑外控制 |
| 高前缀及后继尾 | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-MIXED-SUCCESSOR-VERIFICATION.json`） | ω²+ω+1降低到ω²+ω |
| 外层普通控制 | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-CONTROL-VERIFICATION.json`） | 搬运完整非单一指数向量 |
| 最高指数动态供应 | 记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-SUPPLIER-VERIFICATION.json`） | 真实I193，最高ω³，两次输入别名供应 |

“紧凑外控制”指子外层只有一列，但新低指数系数图仍有完整两包C_t(2)，所有包内、包间、登记和返回断言保持。
不将它说成已经验证了一般控制秩。较高指数的普通正截行与多次高行工厂连续组合尚没有完整成功记录。
非零低指数的检查还断言新包最后间隙实际等于H、严格小于其最高预算：并非只在一个强得多的均匀高团上测试弱合同。

## 三类被否定的实现步骤

第一次尝试激活晚父体复制低指数包。在普通系数先于较低行下降后，该包到晚父体的容量可能不足当前输入行。
单位、正截行、非邻接父三例均真正触发ancestor navigation overshot。对应引擎原文为cantor-degree-type-reserves-v2.cjs（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/cantor-degree-type-reserves-v2.cjs`）。
现行实现改为先生成位于整个新包之后的专用末点，再用它完成局部复制，低指数1的三种正分支已完整通过。

其后尝试省略外层复制前重新激活父体，触发earlier value reaches active work；对应v4原文（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/cantor-degree-type-reserves-v4.cjs`）。
改保留集后仍在恢复子末点时触发ancestor navigation overshot，对应v5原文（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/cantor-degree-type-reserves-v5.cjs`）。
两种省略均撤回，现行程序保留完整父体重新激活及原保留集。失败不是保护超限，不能被成功的其他分支抵消。

共15份失败记录均保留，其中12份属于上述接口或返回断言。汇总按原始哈希识别相应引擎；保存的旧引擎只供代码审计，不应把旧检查器当作锁定全部依赖的运行入口。

## 三次保护停止

最早逐行降低工厂版本在ω²例触发宽度预分配保护，已付费7次、宽196952、结束RSS412.18MiB，见原记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-OMEGA-SQUARED-FAILURE-1.json`）。
这个版本见v1原文（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/cantor-degree-type-reserves-v1.cjs`）。随后用合法的H+1行直接反射生成零间隙，未改断言或提高宽度上限，最终ω²及ω³例完整通过。

加入专用末点、保留完整返回的v3版本（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/cantor-degree-type-reserves-v3.cjs`），在较高指数的单位步及正截行组合例中分别触发40秒保护。
两者已完成局部工厂、包复制及子profile，但停在最后分离恢复，宽301703，结束RSS分别457.73及457.13MiB。
见单位步停止（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-OMEGA-UNIT-FAILURE-2.json`）及正截行停止（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/CANTOR-DEGREE-OMEGA-LIMIT-FAILURE-2.json`）。
没有把这两个部分记录记作成功，也未继续增加其预算。现行版本回到同一完整返回路线，有限高指数正截行组合的完整核验仍未补齐。

## 源检查和边界

源端成功记录（未随本次收录的来源：`output/srpd-limit-y-lower-20261001/FINITE-LEAF-WORK-VERIFICATION.json`）另有589次原Y调用和完整父表检查，10个首次项、550个后代步，5.763秒、结束RSS186.99MiB。
它验证了标准访问、旧节点与新节点[1]的标记一致、首次项公式和若干正返回，不证明全部无限展开。

本轮全部自有进程均已退出。未改公共记号规则、NER、Lean、Git历史或远端。
这些记录既不完成主目标B，也不把条件性纸面推导提升成独立重审过的整链证明。
