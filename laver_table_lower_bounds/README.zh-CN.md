# Laver 表 q(5) 下界：三条证明链 · [English](README.md)

本目录整理三组已有纸面结果及其实际依赖。$q(5)$ 是普通二元 Laver 表首行周期首次达到 32 的**阶参数**，相应表有 $2^{q(5)}$ 个元素。原纸面路线使用 **ZFC + I3** 和同一生成元的 $\operatorname{Iter}(j)$；下方新增的独立 Lean 项目已认证一个不依赖 I3 的条件下界。

## 新增 Lean 结果（2026-11-06）

$$
q(5)\downarrow\ \Longrightarrow\ q(5)>F_{\Lambda+\omega+1}(3),\qquad
\Lambda=\lim(\mathrm{BMS}).
$$

[独立 Lean 4.33.1 项目](lean/README.zh-CN.md)包含[最终定理](lean/LaverLowerBounds/OriginalBMSBound.lean)、数值版 BM4 与父表算法的精确展开等价、实际有限 FGH 求值、可移植编译命令及 [152 模块验证收据](lean/verification/VERIFICATION.json)。公理审计仅含 `propext`、`Classical.choice`、`Quot.sound`；不假设 I3 或全体 BMS 良序性。

**范围：** 输入 `3`，序数层级 `Lambda+omega+1`，采用 Lean 通常基础。没有另行编码 ZFC 对象语言推导，不证明 `q(5)` 存在，也不认证下方更大输入、指数塔或 IBLP 的纸面结论。定理量化任意满足定义方程的有限表族；完整约定和范围见[项目 README](lean/README.zh-CN.md)。

主文把旧的任意固定大输入换成原证明自己产生的参数，给出替换后的数值推导。

## 三组结果

| 组别 | 当前准确结果 | 自然参数 | 主文 |
|---|---|---|---|
| 1．BLP 实现的有限类型塔 | $q(5)>2^Y>Y\ge H_{C[7]}(M)$，且 $q(5)>F_{C[6]}(M-1)+1$ | $M=\mathcal Q(1)$，$\mathcal Q,Y$ 由六层快 BMS 算子定义 | [完整整理](01-blp-tower.zh-CN.md) |
| 2．BMS 动态深度反馈 | $q(5)>F_{\Lambda+\omega+1}(K(g(g(z))))$ | 直接长链输入 $z_{\rm dir}$；强化输入 $X=F_{2^{C_{\rm line}}+1}(C_{\rm line})$；另保留辅助递归输入 $X_*$ | [完整整理](02-bms-feedback.zh-CN.md) |
| 3．原版巨大初值的 modify/cut | $\delta(S_*)<q(5)$，$\mu(S_*)\le\tau(S_*)<2^{q(5)}$ | $S_*=R[2^L][2^{2^L-1}]$，$L=C_{\rm line}$ | [完整整理](03-iblp-modify.zh-CN.md) |

这里 $\Lambda=\lim(\mathrm{BMS})$、$g=F_\Lambda$、$K=F_{\Lambda+\omega}$，
$R=I[0][3][0]$、$C=R[0][1]^8$。$[1]^8$ 是连续八次原版操作。
第三组 $\mu$ 数完整短 modify，$\delta$ 数删行，$\tau=\mu+\delta$。

## 怎么理解“BMS 指数塔”

第一组的准确下降树下标为

$$
\alpha_1=\Lambda,\qquad\alpha_{n+1}=\Lambda\omega^{\alpha_n},
\qquad \operatorname{rank}(C[n])=\alpha_n.
$$

在额外使用 $\omega^\Lambda=\Lambda$ 的化简下，$C[6]$ 是五个 $\Lambda$ 的右结合塔，$C[7]$ 是六个。数值比较使用原版 IBLP 的基本列。秩相同并不允许换成任意另一套基本列；大输入处的六层 FGH 界尚未证明。

## 哪部分依赖 BLP

第一组使用普通 BLP 的实际 E／短复制、备用端口带和类型环境，结论是原版 IBLP 具体式子的 Hardy／FGH。

第二组的 BMS 固定下降和动态反馈可以使用直接的 Qi 长链入口；最大的初始化版本另用 pIBLP 的父包有限参数桥。没有假设整个 pIBLP 记号良序。

第三组的两次入口展开是原版 legacy 完整规则；入口以后用 **paper guard** 的短 $M_\star$，保留标记补全。这个版本区别是定理的一部分。

三条路线暂不按下标名称直接比较具体数值；第三组还没有接成整个 $R$ 的 Hardy／FGH 下界。

## 共同引理与完整依赖

先读[记号及指标约定](common/conventions.zh-CN.md)，再按需要读：

- [BMS 三列种子固定指标计数](common/bms-fixed-index.zh-CN.md)：包括原 $[1]$／展示版 $[2]$、规范父表覆盖、行宽交换、森林控制器、FGH–Hardy 精确编译及强界
$$
  D(h)\ge e_{F_{B_r}(x)}
  \quad\text{当 }h\ge r+2+\lceil\log_2(x+2)\rceil.
$$
- [自然 mark 与局部闭包](common/natural-marks.zh-CN.md)：复制词、membership 截断、Sat 包传送、扫描、E 抽取和有限参数桥。
- [逐项证明依赖](PROOF_DEPENDENCIES.zh-CN.md)：每条箭头对应所需文稿及章节，区分所用定理与历史候选。
- [随附证明稿索引](proofs/README.md)、[来源及哈希](SOURCE_MANIFEST.json)、[外部文献](BIBLIOGRAPHY.md)。

随附证明稿是整理阅读版：所用证明正文及条件保留；历史固定输入段落若被省略，其原始行号记录在清单，新的自然输入证明由三篇主文补齐。旧进度或候选文字不代表当前主定理。没有导入整个研究目录、PDF 或巨大计算输出。

## 有限核验

从本目录执行：

    python -B tools/validate.py

它核对文件哈希、局部链接、输入常数清理，以及固定原代码的有限语法恒等式和小规模入口 marks。它不计算上述巨大函数，不建立巨大 Laver 表。具体资源上限及结果见 [VALIDATION.md](VALIDATION.md)。
