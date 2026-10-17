# 证明依赖与阅读顺序

本表只把实际调用的数学接口列作前提。随附源稿的历史目标、有限测试、撤回候选和更强全局定理，不会因为同处一个文件就成为前提。新自然输入的证明以三篇主文为准。

## 1. 外部标准输入

| 接口 | 使用位置 | 来源 |
|---|---|---|
| 同生成元临界点枚举，$\kappa_4=\gamma_{q(5)-1}$ | 三组 | Laver–Dougherty 对应，Qi v5 |
| 标准有限链及临界下标计数 | 第一、二组；第三组初始化 | Dougherty I／II，Qi 的实际长链 |
| 有限点像、membership 截断及严格上确界 | 三组的实际端点 | Dougherty I 第 5 节、Qi 第 5 节 |
| 标准 BMS 良序及父表公式 | BMS 计数、类型归纳 | Hunter，尤其 Lemma 2.5 |
| 同 cap 的有界 application 良基关系 | 有限参数桥的定义性 | Qi 引用的 Steel 定理 |

链接及具体范围见[文献表](BIBLIOGRAPHY.md)。本地覆盖、森林编译、类型合同、自然 mark 和父包引理均另行证明。

## 2. BMS 固定指标计数

| 次序 | 数学接口 | 实质证明 |
|---:|---|---|
| B1 | 规范父表、末列对齐祖先覆盖、有限准备和复制接缝 | [非标准行界，第 2–5 节](proofs/output/new-notation-20260918/BMS-nonstandard-row-bound.zh-CN.md) |
| B2 | 覆盖保持固定计数，行宽交换 | [祖先覆盖](proofs/output/iblp-laver-bms-20261013/ancestor-cover-growth.zh-CN.md) |
| B3 | 一行森林求值，$H_{W(M)}=F_M$ | [精确增长接口](proofs/output/iblp-laver-bms-20261013/fixed-index-growth-interface.md) |
| B4 | 活动根模板、副本父号、参数森林恢复及终点 $e_y$ | [森林控制器](proofs/output/iblp-laver-bms-20261013/diagonal-forest-hardy-proof.zh-CN.md) |
| B5 | $r+1$ 行、$x+4$ 列及对数行损失 | [本目录合成证明](common/bms-fixed-index.zh-CN.md) |

结果是 $D(h)\ge e_{F_{B_r}(x)}$。这些引理不用 I3 或 Laver 表。[源稿最小依赖审计](proofs/output/iblp-030-laver-20261014/FGH-standalone-dependency-audit.zh-CN.md)说明为何不能省略 B1 或丢掉终点塔函数。

## 3. 第一组：闭语法、类型比较和六层实际实现

1. **安全类及 BMS 基础。** [正接口分类](proofs/output/iblp-01-equality-20260923/IBLP-01-unconditional-BMS-lower-bound.zh-CN.md) → [无补全闭包](proofs/output/iblp-01-equality-20260923/IBLP-01-no-completion-proof.zh-CN.md) → [任意安全类 BMS 上覆盖](proofs/output/iblp-01-equality-20260923/IBLP-01-BMS-upper-bound.zh-CN.md)。另附[祖先带下界](proofs/output/iblp-bms-20260918/IBLP-01-BMS-lower-bound.zh-CN.md)。
2. **准确原版基本列。** [第一根交换律](proofs/scratch/iblp030-8h-20261015/hardy-root-continuation-interface.txt)第 1–3 节 → [有限闭语法及准确下降树秩](proofs/scratch/iblp030-8h-20261015/hardy-root-first-root-tower.txt)第 1–4 节。后者第 5 节撤回的旧初始化不使用。
3. **全部参数的数值比较。** [基础 Hardy 覆盖](proofs/scratch/iblp030-8h-20261015/hardy-root-bms-interface.txt)第 2–4 节、[相对 oracle](proofs/scratch/iblp030-8h-20261015/hardy-root-oracle-upper.txt)第 3–4 节 → [类型上界](proofs/scratch/iblp030-8h-20261015/hardy-root-typed-bms-bound.txt)、[尾局部性](proofs/scratch/iblp030-8h-20261015/hardy-root-tail-locality.txt)、[同输入快比较及种子路径](proofs/scratch/iblp030-8h-20261015/hardy-root-fast-type1-C3.txt) → [整体四倍余量](proofs/scratch/iblp030-8h-20261015/hardy-root-low-stack-numeric.txt)。
4. **实际 fan 和带编译。** [前端插入](proofs/output/iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md) → [低开 fan 与全部隐含边](proofs/scratch/iblp030-8h-20261015/lift-low-open-fan-and-typed-gap.txt) → [备用带和端点修补](proofs/scratch/iblp030-8h-20261015/lift-participating-bms-spare.txt)第 1–5 节 → [自然相对 BMS 编译](proofs/scratch/iblp030-8h-20261015/lift-natural-relative-bms-oracle.txt)第 2–4 节。备用带旧稿的候选秩论证不使用，改用已知 BMS 良序归纳。
5. **类型入口和几何接缝。** [混合底入口](proofs/scratch/iblp030-8h-20261015/lift-mixed-base-type1-seed.txt)、[第二类型入口](proofs/scratch/iblp030-8h-20261015/lift-type2-entry-relaxation.txt)、[严格 cap](proofs/scratch/iblp030-8h-20261015/root-low-Q11-strict-cap-proof.txt)、[四层端点](proofs/scratch/iblp030-8h-20261015/lift-low-four-type-staircase.txt)、[压缩六层](proofs/scratch/iblp030-8h-20261015/lift-low-compressed-six-type-staircase.txt)。
6. **装配和自然输入。** [C7 合成稿](proofs/scratch/iblp030-8h-20261015/hardy-root-C7-q5-single-file.txt)第 3–7 节给出实际 $Y$-line；[本组主文](01-blp-tower.zh-CN.md)第 3–5 节完整保留 $M=\mathcal Q(1)$ 的数值推导。
7. **FGH。** [跨输入转换](proofs/scratch/iblp-I-to-I0-20261016/port-FGH-existing-bound-C6.txt)第 2–4 节逐项证明 $G_Q^h(y)\ge F_Q(x)+1$（$y\ge x+1$）；主文取 $x=M-1,y=M$。

## 4. 第二组：入口 fan、动态深度与强化初始化

| 接口 | 实质证明 |
|---|---|
| 三列弱带、有限初始化、首轮及逐段反馈 | [单文件基础证明，第 3–8 节](proofs/output/iblp-030-laver-20261014/q5-BMS-successor-single-file-proof.zh-CN.md) |
| 低出口 promoter 的严格点像 | [短搬运端点](proofs/output/iblp-030-laver-20261014/small-period-endpoint-Sf.zh-CN.md)、[第二轮搬运](proofs/output/iblp-030-laver-20261014/promoted-bms-feedback.zh-CN.md) |
| 对任意实际入口的整背景自然性 | [递归 corridor](proofs/output/iblp-030-laver-20261014/small-period-recursive-corridor.zh-CN.md)、[逐段反馈](proofs/output/iblp-030-laver-20261014/lined-feedback-corridor.zh-CN.md) |
| 动态深度统一低出口及再升级 | [动态深度完整证明](proofs/output/q5-further-bound-20261014/dynamic-depth-Lambda-omega-successor.zh-CN.md) |
| 九行种子及全部普通边、Sat、marks | [L3 原生构造](proofs/output/iblp-030-laver-20261014/ordinary-l3-native-mark-seed.zh-CN.md)、[完整证书](proofs/output/iblp-030-laver-20261014/same-owner-L3-sat-closure.zh-CN.md) |
| 父包扫描和有限参数递归 | [选择器](proofs/output/iblp-030-laver-20261014/parent-packet-propagation-selector.zh-CN.md)、[父包定量桥](proofs/output/iblp-030-laver-20261014/parent-packet-quantitative-transfer.zh-CN.md) |
| $H_0=u_{\omega^\omega}$ | [纯 E 归约](proofs/output/piblp-external-FGH-20261014/P4-pure-E-collapse.zh-CN.md)及其 baseline 四步计算 |
| 较简洁和共享端口输入 | [有限 FGH 初始化](proofs/output/q5-further-bound-20261014/P5-uniform-and-large-input.zh-CN.md)、[共享端口强化](proofs/output/q5-further-bound-20261014/active-port-stronger-initialization.zh-CN.md)、[函数代入](proofs/output/piblp-external-FGH-20261014/active-E-graft-functional-substitution.zh-CN.md) |

直接长链版本不调用最后四行的父包强化初始化链。其自然 $z_{\rm dir}$ 只是明确有限整数预算的最大解。

## 5. 第三组：原版森林入口、自然 mark 和整数计数

| 接口 | 实质证明 |
|---|---|
| 根全部 owners、包端点和长链搬运 | [实际入口，第 1–6 节](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-initializer.txt) |
| 根 shadow 的 $2^L-1$ 段 | 同稿第 15 节、[前缀保留链乘法](proofs/scratch/iblp-I-to-I0-20261016/local-budget-algebra.txt)第三节 |
| 原始森林、首轮扫描交换、$R[k][n]$ quiet 性 | [原版森林](proofs/scratch/iblp030-8h-20261015/original-audit-root-forest-interface.txt)第 2、4、5 节和[双链 quiet](proofs/scratch/iblp030-8h-20261015/original-audit-two-chain-quiet-cone.txt) |
| 单行尾包和完整相邻父块的 shadow 输送 | [shadow 森林](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-shadow-forest.txt) |
| 因子物理后继闭合、membership 修补 | [抽取定理](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-extraction.txt)；主文第 5 节也完整给出 |
| 首轮完整 family、第二轮 all-high 及闭合归纳 | [自然入口](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-initializer.txt) |
| paper 短复制、冻结扫描、Sat 和准确 mark | [自然 mark 局部引理索引](common/natural-marks.zh-CN.md) |
| 有限表严格增加、cut 和末四步 | [整数势桥](proofs/output/iblp-laver-bms-20261013/direct-step-bridge.zh-CN.md)、[短尾接口第 6 节](proofs/output/iblp-030-laver-20261014/short-tail-cofinality.zh-CN.md)，主文第 7 节重新证明 |

[原合成稿](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-total-bound.zh-CN.txt)的逐指标入口与局部闭包仍是依赖；新主文直接花实际链长，取 $k=2^L,n=2^{2^L-1}$。第二次初始化后不再假设可无限再生 shadow。

## 6. 来源、历史内容与有限核验

[全部文稿索引](proofs/README.md)包含辅助引理及局部交叉审计。[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json)记录原稿哈希、整理版哈希、固定输入历史段落的省略行号及链接整理。

源稿中还可能提到未收录的历史脚本、其他记号比较和失败路线。这些不作为以上接口的前提。全局 I2 标准域定理也不是三个主文的隐藏假设。

有限核验不替代规范覆盖准备、森林编译、实际嵌入合法性、类型量词或自然 mark 闭包中的任何全称证明。
