# 列图序数记号 - HZY · [English](README.md)

9 月 11 日 20:00，@Phyrion 公布了 [Y 序列的良序证明](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)。不久后，@test_alpha0 进一步将所需的公理体系降低到 $KP_\omega+\text{存在不可数序数}$。本仓库收录 GPT6-astra 在阅读上述证明后设计的 RPD、LRD、Ω-LRD3、ARD、IPD、ARD2，以及它们的良序证明。其中，RPD 的定义所需篇幅短得多；下面的纸面比较链证明其序型不小于固定版本 1Y。LRD 和 Ω-LRD3 则是在此基础上进一步扩展得到的记号。ARD 则把行标改为此前列的地址，使行坐标本身也随展开移动。IPD 则使用有限层迭代树轮廓，连嵌套头内的引用也随列搬运。ARD2 回到每组仅三个自然数坐标的形式，允许行与根同时引用本列，并生成覆盖全上下文的根包。六者均有同一公理体系下的纸面良序证明。它们与 omega-Y 等其他常见记号的序型大小关系暂时未知。

本仓库收录列图序数记号的定义、可执行基本列展开器和良序证明。源码快照整理于 **2026-09-17**，仓库地址为 [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy)。名称中的 `hzy` 来自仓库所有者的名字。

记号实现收录 **RPD、LRD、Ω-LRD3、ARD、IPD、ARD2、SPD、CWY、CWY2、Ω-CWY**，CWY 的适配器／候选状态见下文；Lean 证明覆盖 **Y、RPD、LRD、Ω-LRD3、ARD、IPD、ARD2**。另保留明确标记的旧版 ARD-legacy、ARD2-legacy；其他 Ω-LRD 版本及历史实验实现不收录。

新增 **SPD（Slot Profile Diagrams，潜边轮廓图）**：每条关系只有四个整数，头与参数从此前列递归读出，输入中没有独立树字段。随附双语定义、纸面良序论证稿、Python／NER 实现及有界回归测试。**SPD 尚无 Lean 证明。** 它与 ARD、ARD2、wY、整个 IPD 的序型大小关系仍未知；局部轮廓的构造能力不等于这些跨记号比较已经成立。

## ARD2 新版（2026-09-17）

默认 **ARD2 已换成简化轮廓版**：每个父列只留最大 `(行锚, 根)`，再删除被支配项；整包低行生成由单个前驱替代。两种 SELF 仍保留，根借位上界仍为接缝自身。标准序型、逐指标基本列和计数均与旧版相同；[完整等价证明](proofs/paper/ard2-well-ordering.zh-CN.md)为纸面结果，新规则自身良序有[独立 Lean 项目](lean/ARD2/README.zh-CN.md)。

原版 NER、Python、双语定义、证明及 Lean 均保存为 [ARD2-legacy](notations/ARD2-legacy/definition.zh-CN.md)。NER 两版 ID 不同，可同时导入，默认版仍名 **ARD2**，保留五种显示和原预算。`ARD ≤ ARD2(1,3)` 通过目标同构保持；与 wY/CWY2 的整体比较没有新结论。

## CWY 系列（2026-09-17）

新增 **CWY、CWY2、Ω-CWY**，各有独立 NER 文件和中英文 Markdown／PDF 规则。

- **CWY：**NER 文件是原 wY 加根部拉长的紧凑列表视图，不是独立 CWY 展开内核。随附 Python 核心与带界封装实现数学上的根部拉长版；已有纸面论证给出内部界 B，其下是与 wY 同构的初始段。纯种子的编号与 NER 适配器不同，定义文档已明确区分。
- **CWY2：**当前无特殊列的直接列内核。[完整等价论文](proofs/paper/cwy2-equivalence.zh-CN.md)（[PDF](proofs/paper/cwy2-equivalence.zh-CN.pdf)）在引用所给 wY 稿有限引理的前提下，给出基本列逐项交换及对应标准域的序同构；良序性由该稿在弱 KP 框架内转移。这是纸面结果，**没有 Lean 证书**。
- **Ω-CWY：**极限列标采用 D[b+1]、顶端按嵌套层数展开的自索引候选，保留原式／计数序列／山脉图三视图。整体良序、共尾性及与 wY 的大小关系仍**未证明**；本次只收录已有有限结构论证与康托片段说明。

三者均未新增 Lean 项目，不扩充原七系统联合定理。私人 wY 来源稿不转载。前两个 CWY 系列 JS 包含源自上游 NER 的代码；公开再分发前请阅读[来源与许可提醒](SOURCES.zh-CN.md)。

## ARD 新版（2026-09-16）

默认 **ARD 已换成简化轮廓规则**：仍用三元组列列表，但删除被支配的记录，以单个前驱替代整包低行生成。标准序型、基本列指标和计数序列与旧版相同；[旧版 ARD-legacy](notations/ARD-legacy/definition.zh-CN.md) 的 NER、Python、定义、纸面证明和 Lean 均保留。

已有纸面比较结论

$$
\boxed{\mathrm{ARD}(1,2)\ge\mathrm{RPD}\ge 1Y.}
$$

其中 `ARD(1,2)` 是两列式 `[][(0,0,0)]`，不是整个 ARD 极限。[固定两列式下的嵌入证明](proofs/paper/rpd-le-ard-a2.zh-CN.md) 给出完整 RPD 有限标准域到其严格下方的序嵌入，故还得到整个 ARD 严格大于 RPD。**这些比较及新旧标准域同构目前是纸面证明；新版 ARD 自身良序已有独立 Lean 定理。** 1Y 指本仓库固定上游定义，不新增对任意原始 JS 输入的等价性声明。

另有[ARD 嵌入 ARD2 固定式 (1,3) 以下的证明](proofs/paper/ard-le-ard2-13.zh-CN.md)（[PDF](proofs/paper/ard-le-ard2-13.zh-CN.pdf)）。这里 `ARD2(1,3)` 是 `[][(0,0,1)]=A₂[1][1]`。对有限标准域，得到

$$\alpha_{1Y}\le\alpha_{\mathrm{RPD}}<\alpha_{\mathrm{ARD}}
\le|\mathrm{ARD2}(1,3)|<\alpha_{\mathrm{ARD2}}.$$

这项也是**尚未 Lean 形式化的纸面比较**，不声称像为初始段、计数保持、与基本列逐指标交换，或等于该固定式。wY／CWY2 的整体比较仍未解决。

## 定义与展开器

每套定义都有中英文 Markdown 和 PDF，共 **48 份定义文件（含保留的旧版及 CWY 系列）**。Markdown 默认英文；每份英文定义的标题均链接到中文版。

| 记号 | 英文定义 | 中文定义 | NER 展开器 | Python 展开器 |
| --- | --- | --- | --- | --- |
| RPD | [Markdown](notations/RPD/definition.md) · [PDF](notations/RPD/definition.pdf) | [Markdown](notations/RPD/definition.zh-CN.md) · [PDF](notations/RPD/definition.zh-CN.pdf) | [JavaScript](notations/RPD/RPD-mountain.ne-rewritten.js) | [rpd.py](notations/RPD/rpd.py) |
| LRD | [Markdown](notations/LRD/definition.md) · [PDF](notations/LRD/definition.pdf) | [Markdown](notations/LRD/definition.zh-CN.md) · [PDF](notations/LRD/definition.zh-CN.pdf) | [JavaScript](notations/LRD/LRD.ne-rewritten.js) | [lrd.py](notations/LRD/lrd.py) |
| Ω-LRD3 | [Markdown](notations/Omega-LRD3/definition.md) · [PDF](notations/Omega-LRD3/definition.pdf) | [Markdown](notations/Omega-LRD3/definition.zh-CN.md) · [PDF](notations/Omega-LRD3/definition.zh-CN.pdf) | [JavaScript](notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js) | [omega_lrd3.py](notations/Omega-LRD3/omega_lrd3.py) |
| ARD | [Markdown](notations/ARD/definition.md) · [PDF](notations/ARD/definition.pdf) | [Markdown](notations/ARD/definition.zh-CN.md) · [PDF](notations/ARD/definition.zh-CN.pdf) | [JavaScript](notations/ARD/ARD.ne-rewritten.js) | [ard.py](notations/ARD/ard.py) |
| ARD-legacy | [Markdown](notations/ARD-legacy/definition.md) · [PDF](notations/ARD-legacy/definition.pdf) | [Markdown](notations/ARD-legacy/definition.zh-CN.md) · [PDF](notations/ARD-legacy/definition.zh-CN.pdf) | [JavaScript](notations/ARD-legacy/ARD-arcs.ne-rewritten.js) | [ard.py](notations/ARD-legacy/ard.py) |
| IPD | [Markdown](notations/IPD/definition.md) · [PDF](notations/IPD/definition.pdf) | [Markdown](notations/IPD/definition.zh-CN.md) · [PDF](notations/IPD/definition.zh-CN.pdf) | [JavaScript](notations/IPD/IPD.ne-rewritten.js) | [ipd.py](notations/IPD/ipd.py) |
| ARD2 | [Markdown](notations/ARD2/definition.md) · [PDF](notations/ARD2/definition.pdf) | [Markdown](notations/ARD2/definition.zh-CN.md) · [PDF](notations/ARD2/definition.zh-CN.pdf) | [JavaScript](notations/ARD2/ARD2.ne-rewritten.js) | [ard2.py](notations/ARD2/ard2.py) |
| ARD2-legacy | [Markdown](notations/ARD2-legacy/definition.md) · [PDF](notations/ARD2-legacy/definition.pdf) | [Markdown](notations/ARD2-legacy/definition.zh-CN.md) · [PDF](notations/ARD2-legacy/definition.zh-CN.pdf) | [JavaScript](notations/ARD2-legacy/ARD2-legacy.ne-rewritten.js) | [ard2.py](notations/ARD2-legacy/ard2.py) |
| SPD | [Markdown](notations/SPD/definition.md) · [PDF](notations/SPD/definition.pdf) | [Markdown](notations/SPD/definition.zh-CN.md) · [PDF](notations/SPD/definition.zh-CN.pdf) | [JavaScript](notations/SPD/SPD.ne-rewritten.js) | [spd.py](notations/SPD/spd.py) |
| CWY | [Markdown](notations/CWY/definition.md) · [PDF](notations/CWY/definition.pdf) | [Markdown](notations/CWY/definition.zh-CN.md) · [PDF](notations/CWY/definition.zh-CN.pdf) | [wY 适配器及 CWY 视图](notations/CWY/wY-CWY.ne-rewritten.js) | [核心](notations/CWY/compact_wy.py) · [带界版](notations/CWY/compact_wy_bound.py) |
| CWY2 | [Markdown](notations/CWY2/definition.md) · [PDF](notations/CWY2/definition.pdf) | [Markdown](notations/CWY2/definition.zh-CN.md) · [PDF](notations/CWY2/definition.zh-CN.pdf) | [JavaScript](notations/CWY2/CWY2.ne-rewritten.js) | 无 Python；[可读 JS 核心](notations/CWY2/cwy_direct.mjs) |
| Ω-CWY | [Markdown](notations/Omega-CWY/definition.md) · [PDF](notations/Omega-CWY/definition.pdf) | [Markdown](notations/Omega-CWY/definition.zh-CN.md) · [PDF](notations/Omega-CWY/definition.zh-CN.pdf) | [JavaScript](notations/Omega-CWY/Omega-CWY.ne-rewritten.js) | 无 Python；[可读 JS 核心](notations/Omega-CWY/core.mjs) |

网页版：把所选 JavaScript 文件的完整内容载入 [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/) 的自定义记号功能。每份文件均独立注册，无需构建；保留已有显示方式及资源保护。脚本也保留原来的中文帮助文字，其中可能有历史证明进度说明；当前证明范围以本包论文及验收记录为准。

另有可选的 [RPD 附 Y 山脉下界版](notations/RPD/y-lower-bound/README.zh-CN.md)，在主式后显示 `≥ Y【山脉】`。独立子目录内放有单文件 JS、具体算法说明和纸面比较文稿；原 RPD 展开器不变，新增比较尚未端到端 Lean 形式化。

RPD、ARD、ARD2 在“等价表示”菜单另有“邻接表（文字）”和“邻接表（图）”。文字每列一对 `[]`，分号分层、逗号定位父列，保留内部空位。HTML 或原生图表弹窗中，每个有关系的层是一张紧凑上三角表：完整淡色对角格同时充当行列标，其他格填最大根；全部表格上方单独显示一次精确计数序列。超限明确提示，不代填近似计数，也不画局部表格。

Python 文件只依赖标准库，实现数学展开核心，不包含 NER 界面和显示缓存。命令行示例见相应定义文档。大展开仍可能很昂贵；数学上有定义不意味着计算便宜。

SPD 提供列表与精确计数序列两种显示。NER 支持输入 `S2`、`Top[2][1]`、完整关系列表，以及 `C(1,3,16)` 等标准计数词。独立的 [Python 计数解码器](notations/SPD/spd_count_decode.py) 恢复唯一标准式，并区分非法输入与资源耗尽。结构合法的手写列表不会自动被认定为标准式。

## 良序证明与证明状态

原合写论文覆盖 Y、RPD、LRD、Ω-LRD3，旧版 ARD-legacy 全文证明给出动态行引用的延拓，新版 ARD 论文证明轮廓简化及直接语义下降。IPD 独立论文给出迭代树轮廓的证明，并把直接 KP 树秩引理收入附录 A。ARD2-legacy 论文给出双 SELF 延拓及其实际接缝搬运；新版 ARD2 论文证明精确轮廓同构和直接语义下降。这些良序证明均在以下弱集合论内论证：

$$
KP_\omega+\text{存在不可数序数}.
$$

这里 KP 保留完整集合归纳。论文不增加幂集、完全分离/收集、选择、反射或大基数公理。

- **纸面证明：**[英文 Markdown](proofs/paper/well-ordering.md) · [英文 PDF](proofs/paper/well-ordering.pdf) · [中文 Markdown](proofs/paper/well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/well-ordering.zh-CN.pdf)。
- **ARD 纸面证明：**[英文 Markdown](proofs/paper/ard-well-ordering.md) · [英文 PDF](proofs/paper/ard-well-ordering.pdf) · [中文 Markdown](proofs/paper/ard-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ard-well-ordering.zh-CN.pdf)。
- **ARD-legacy 旧版证明：**[中](proofs/paper/ard-legacy-well-ordering.zh-CN.md) · [英](proofs/paper/ard-legacy-well-ordering.md)。
- **ARD(1,2)≥RPD 比较：**[中文](proofs/paper/rpd-le-ard-a2.zh-CN.md) · [英文](proofs/paper/rpd-le-ard-a2.md)。
- **ARD2(1,3)≥ARD 比较：**[中文 Markdown](proofs/paper/ard-le-ard2-13.zh-CN.md) · [中文 PDF](proofs/paper/ard-le-ard2-13.zh-CN.pdf) · [英文 Markdown](proofs/paper/ard-le-ard2-13.md) · [英文 PDF](proofs/paper/ard-le-ard2-13.pdf)。
- **IPD 纸面证明：**[英文 Markdown](proofs/paper/ipd-well-ordering.md) · [英文 PDF](proofs/paper/ipd-well-ordering.pdf) · [中文 Markdown](proofs/paper/ipd-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ipd-well-ordering.zh-CN.pdf)。
- **ARD2 纸面证明：**[英文 Markdown](proofs/paper/ard2-well-ordering.md) · [英文 PDF](proofs/paper/ard2-well-ordering.pdf) · [中文 Markdown](proofs/paper/ard2-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ard2-well-ordering.zh-CN.pdf)。
- **ARD2-legacy 纸面证明：**[英文 Markdown](proofs/paper/ard2-legacy-well-ordering.md) · [英文 PDF](proofs/paper/ard2-legacy-well-ordering.pdf) · [中文 Markdown](proofs/paper/ard2-legacy-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ard2-legacy-well-ordering.zh-CN.pdf)。
- **SPD 纸面论证稿（尚未 Lean 形式化）：**[英文 Markdown](proofs/paper/spd-well-ordering.md) · [英文 PDF](proofs/paper/spd-well-ordering.pdf) · [中文 Markdown](proofs/paper/spd-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/spd-well-ordering.zh-CN.pdf)。
- **CWY2／wY 等价（纸面）：**[英文 Markdown](proofs/paper/cwy2-equivalence.md) · [英文 PDF](proofs/paper/cwy2-equivalence.pdf) · [中文 Markdown](proofs/paper/cwy2-equivalence.zh-CN.md) · [中文 PDF](proofs/paper/cwy2-equivalence.zh-CN.pdf)。CWY 的表示及带界良序论证收入其定义；Ω-CWY 暂无整体良序证明。
- **IPD 定义对应审计：**[英文](proofs/paper/ipd-fidelity.md) · [中文](proofs/paper/ipd-fidelity.zh-CN.md)。
- **Lean：**[英文构建说明与定理索引](lean/README.md) · [中文说明](lean/README.zh-CN.md)。
- **独立 Lean 项目：**[Y](lean/Y/README.zh-CN.md) · [RPD](lean/RPD/README.zh-CN.md) · [LRD](lean/LRD/README.zh-CN.md) · [Ω-LRD3](lean/Omega-LRD3/README.zh-CN.md) · [ARD](lean/ARD/README.zh-CN.md) · [IPD](lean/IPD/README.zh-CN.md) · [ARD2](lean/ARD2/README.zh-CN.md)。
- **可选联合入口：**[ARD2RevisionFinalAudit.lean](lean/src/ARD2RevisionFinalAudit.lean)。

每个记号各有独立构建配置、输出和验证收据，只编译声明的依赖与[共享基础](lean/shared/README.zh-CN.md)；新版 ARD 和 ARD2 分别显式复用各自 legacy 语义后端，只有 Y 另需 BMS。新增记号不修改旧项目，也不强制重建旧证明。

这里“每个记号”指 Lean 索引中的原七个系统。SPD 此次只增加实现和纸面文稿，没有 `lean/SPD` 项目、验证收据，也没有扩充七系统联合定理。其文稿在同一弱集合论内展开有限需求／新父子句路线，并区分合法 raw 图的展开关系良基与指定标准域的列序良序。

Lean 工程形式化通常数学意义的良序定理，**不是在 Lean 中编码上述弱对象理论的推导**。论文的公理账本与 Lean 内核检查是两项不同成果。

Y 指固定上游提交 `1689b21131b488ec2ba2515bd630360371a2389d` 的继承祖先定义。这里不声称已完成该定义与原 Naruyoko JavaScript 在全部合法输入上的等价证明，Lean 认证部分不包含跨记号序型比较、最优公理强度或证明论序数比较；上面的比较链由纸面证明给出；另设研究目录保存未纳入正式定理的比较论证与候选。

## 序型比较研究（非正式定理）

新增的[研究目录](research/README.md)专门保存推导与比较草稿，与正式证明分开放置。当前收录 [IPD 比较总览](research/ordinal-comparisons-20260914/README.zh-CN.md)、Y≤RPD 的纸面比较思路、RPD/Y/wY/ARD/TPD 的 IPD 上界候选，以及 ARD2 与 IPD 的后续研究。每份总结区分纸面论证、局部引理、有限核验和未证候选；归档不等于完成跨记号的 Lean 认证。

关键原稿与候选数据一并保存，实验代码及私人来源稿不随文档归档。历史测试记录与正式仓库当前证明进度应分别阅读。

## 给 AI 阅读的文档

[AI 阅读文档目录](ai-docs/README.zh-CN.md) 收集双语入门指南、设计要求与交接文档。首篇为**设计基本列型序数记号的美观性**（[中文](ai-docs/fundamental-sequence-aesthetics.zh-CN.md) · [English](ai-docs/fundamental-sequence-aesthetics.md)），介绍列式语法、前缀保持的展开、精确计数序列比较、简洁的内部结构及实质强度提升。这些指南提供要求和解释，不构成新增的 Lean 证书或无条件的序型比较结论。

## 验证与重新生成 PDF

在本目录运行有界展开器测试：

```sh
python tests/test_python.py
python tests/test_ard.py
python tests/test_ard_legacy.py
node --max-old-space-size=512 tests/ard_skyline.cjs
python -B tests/rpd_ard_comparison.py
python -B tests/ard_ard2_comparison.py
python -B tests/ard_ard2_forest.py
python tests/test_ipd.py
python tests/test_ard2.py
python -B tests/test_ard2_legacy.py
python -B tests/test_spd.py
python -B tests/test_lean_verifier.py
node --max-old-space-size=256 tests/ard2_ner.cjs
node --max-old-space-size=256 tests/ard2_display.cjs
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
python -B tests/test_cwy.py
node --max-old-space-size=256 tests/cwy_family.mjs
```

固定依赖和串行、有资源上限的 Lean 构建方法见 [Lean 说明](lean/README.zh-CN.md)。Lean 编译不需要生成 PDF，也不需要 Node.js。

如果受限宿主不允许 Node 启动 Python，可用两个受限进程执行同一交叉测试：`python -B tests/test_cwy.py --fixtures | node --max-old-space-size=256 tests/cwy_family.mjs --fixtures-stdin`。这不会跳过 Python 对照。

如需重建全部 44 份发布用 PDF，安装 Pandoc、Node.js、文档工具依赖及适当的本机字体：

```sh
python -m pip install -r tools/requirements.txt
npm --prefix tools install
python tools/render_pdfs.py
python tools/qa_pdfs.py
```

生成器使用 ReportLab 和 MathJax 公式渲染，不会静默丢弃不支持的 Markdown 内容。Windows 下默认读取 `C:/Windows/Fonts`；可用 `--font-dir` 或 `ORDINAL_PDF_FONTS` 指定其他字体目录。本包不再分发字体。QA 命令另需 Poppler 的 `pdftoppm`，页面图在 Git 忽略的 `tmp/pdf-qa/` 下；重建成功不能代替目视检查。

本次检查结果见 [验收记录](VALIDATION.zh-CN.md)，发布前请阅读 [来源与许可证说明](SOURCES.zh-CN.md)。

`python tools/check_release.py` 检查发布清单、本地链接及已有 Lean 收据。双语要求针对发布文档；21 份明确列名的既有单语研究归档保留原文语言，但仍检查标题、公式、链接及私人路径。新文档不会自动获得归档豁免。

## 目录结构

```text
README.md / README.zh-CN.md       总入口
notations/
  RPD/                           双语定义、PDF、JS、Python
  LRD/                           双语定义、PDF、JS、Python
  Omega-LRD3/                     双语定义、PDF、JS、Python
  ARD/                           双语定义、PDF、弧线图 JS、Python
  IPD/                           双语定义、PDF、树形图 JS、Python
  ARD2/                          双语定义、PDF、五视图 JS、Python
  ARD2-legacy/                   完整保留的旧版定义、程序和文稿
  SPD/                           双语定义、PDF、列表／计数 JS、Python、计数解码器
  CWY/                           双语规则及已有论证、PDF、wY 视图 JS、Python 核心和带界版
  CWY2/                          双语规则、PDF、独立 JS 和可读直接核心
  Omega-CWY/                     双语候选规则、PDF、三视图 JS 和可读源码
proofs/paper/                     原有证明、SPD 文稿、CWY2 等价与对应审计
research/                       比较推导、未证候选及历史研究文稿
ai-docs/                        给 AI 阅读的双语指南与交接文档
lean/                           源码依赖集合、固定版本与有界构建工具
tests/                          有界展开器与构建验证器回归测试
tools/                          可复现 PDF 生成及 QA
```

## 发布前事项

本项目自己的公开许可证**尚未指定**。收录的第三方材料保留其明确的许可证，但不能据此自动为新代码或论文指定许可证。由于固定的 BMS 源码树中未找到许可证，该依赖在构建时外部获取，详见 [说明](SOURCES.zh-CN.md)。本包不收录私人来源稿或机器专用的研究缓存。
