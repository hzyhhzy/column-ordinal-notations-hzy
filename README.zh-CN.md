# 列图序数记号 - HZY · [English](README.md)

9 月 11 日 20:00，@Phyrion 公布了 [Y 序列的良序证明](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)。不久后，@test_alpha0 进一步将所需的公理体系降低到 $KP_\omega+\text{存在不可数序数}$。本仓库收录 GPT6-astra 在阅读上述证明后设计的 RPD、LRD、Ω-LRD3、ARD、IPD、ARD2，以及它们的良序证明。其中，RPD 预计强度不小于 Y 序列，但定义所需篇幅短得多；有关相对强度的探索性论证另存研究目录，尚未作为正式比较定理收录。LRD 和 Ω-LRD3 则是在此基础上进一步扩展得到的记号。ARD 则把行标改为此前列的地址，使行坐标本身也随展开移动。IPD 则使用有限层迭代树轮廓，连嵌套头内的引用也随列搬运。ARD2 回到每组仅三个自然数坐标的形式，允许行与根同时引用本列，并生成覆盖全上下文的根包。六者均有同一公理体系下的纸面良序证明。它们与 omega-Y 等其他常见记号的序型大小关系暂时未知。

本仓库收录列图序数记号的定义、可执行基本列展开器和良序证明。源码快照整理于 **2026-09-14**，仓库地址为 [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy)。名称中的 `hzy` 来自仓库所有者的名字。

新记号实现收录 **RPD、LRD、Ω-LRD3、ARD、IPD、ARD2**；证明覆盖 **Y、RPD、LRD、Ω-LRD3、ARD、IPD、ARD2**。其他 Ω-LRD 版本及历史实验实现均不收录。

## 定义与展开器

每套定义都有中英文 Markdown 和 PDF，共 **24 份定义文件**。Markdown 默认英文；每份英文文档的标题均链接到中文版。

| 记号 | 英文定义 | 中文定义 | NER 展开器 | Python 展开器 |
| --- | --- | --- | --- | --- |
| RPD | [Markdown](notations/RPD/definition.md) · [PDF](notations/RPD/definition.pdf) | [Markdown](notations/RPD/definition.zh-CN.md) · [PDF](notations/RPD/definition.zh-CN.pdf) | [JavaScript](notations/RPD/RPD-mountain.ne-rewritten.js) | [rpd.py](notations/RPD/rpd.py) |
| LRD | [Markdown](notations/LRD/definition.md) · [PDF](notations/LRD/definition.pdf) | [Markdown](notations/LRD/definition.zh-CN.md) · [PDF](notations/LRD/definition.zh-CN.pdf) | [JavaScript](notations/LRD/LRD.ne-rewritten.js) | [lrd.py](notations/LRD/lrd.py) |
| Ω-LRD3 | [Markdown](notations/Omega-LRD3/definition.md) · [PDF](notations/Omega-LRD3/definition.pdf) | [Markdown](notations/Omega-LRD3/definition.zh-CN.md) · [PDF](notations/Omega-LRD3/definition.zh-CN.pdf) | [JavaScript](notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js) | [omega_lrd3.py](notations/Omega-LRD3/omega_lrd3.py) |
| ARD | [Markdown](notations/ARD/definition.md) · [PDF](notations/ARD/definition.pdf) | [Markdown](notations/ARD/definition.zh-CN.md) · [PDF](notations/ARD/definition.zh-CN.pdf) | [JavaScript](notations/ARD/ARD-arcs.ne-rewritten.js) | [ard.py](notations/ARD/ard.py) |
| IPD | [Markdown](notations/IPD/definition.md) · [PDF](notations/IPD/definition.pdf) | [Markdown](notations/IPD/definition.zh-CN.md) · [PDF](notations/IPD/definition.zh-CN.pdf) | [JavaScript](notations/IPD/IPD.ne-rewritten.js) | [ipd.py](notations/IPD/ipd.py) |
| ARD2 | [Markdown](notations/ARD2/definition.md) · [PDF](notations/ARD2/definition.pdf) | [Markdown](notations/ARD2/definition.zh-CN.md) · [PDF](notations/ARD2/definition.zh-CN.pdf) | [JavaScript](notations/ARD2/ARD2.ne-rewritten.js) | [ard2.py](notations/ARD2/ard2.py) |

网页版：把所选 JavaScript 文件的完整内容载入 [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/) 的自定义记号功能。每份文件均独立注册，无需构建；保留已有显示方式及资源保护。脚本也保留原来的中文帮助文字，其中可能有历史证明进度说明；当前证明范围以本包论文及验收记录为准。

RPD、ARD、ARD2 在“等价表示”菜单另有“邻接表（文字）”和“邻接表（图）”。文字每列一对 `[]`，分号分层、逗号定位父列，保留内部空位。HTML 或原生图表弹窗中，每个有关系的层是一张紧凑上三角表：完整淡色对角格同时充当行列标，其他格填最大根；全部表格上方单独显示一次精确计数序列。超限明确提示，不代填近似计数，也不画局部表格。

Python 文件只依赖标准库，实现数学展开核心，不包含 NER 界面和显示缓存。命令行示例见相应定义文档。大展开仍可能很昂贵；数学上有定义不意味着计算便宜。

## 七个记号的良序证明

原合写论文覆盖 Y、RPD、LRD、Ω-LRD3，独立的 ARD 全文证明给出动态行引用的延拓。IPD 独立论文给出迭代树轮廓的证明，并把直接 KP 树秩引理收入附录 A。ARD2 论文给出双 SELF 延拓及其实际接缝搬运。四篇均在以下弱集合论内论证：

$$
KP_\omega+\text{存在不可数序数}.
$$

这里 KP 保留完整集合归纳。论文不增加幂集、完全分离/收集、选择、反射或大基数公理。

- **纸面证明：**[英文 Markdown](proofs/paper/well-ordering.md) · [英文 PDF](proofs/paper/well-ordering.pdf) · [中文 Markdown](proofs/paper/well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/well-ordering.zh-CN.pdf)。
- **ARD 纸面证明：**[英文 Markdown](proofs/paper/ard-well-ordering.md) · [英文 PDF](proofs/paper/ard-well-ordering.pdf) · [中文 Markdown](proofs/paper/ard-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ard-well-ordering.zh-CN.pdf)。
- **IPD 纸面证明：**[英文 Markdown](proofs/paper/ipd-well-ordering.md) · [英文 PDF](proofs/paper/ipd-well-ordering.pdf) · [中文 Markdown](proofs/paper/ipd-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ipd-well-ordering.zh-CN.pdf)。
- **ARD2 纸面证明：**[英文 Markdown](proofs/paper/ard2-well-ordering.md) · [英文 PDF](proofs/paper/ard2-well-ordering.pdf) · [中文 Markdown](proofs/paper/ard2-well-ordering.zh-CN.md) · [中文 PDF](proofs/paper/ard2-well-ordering.zh-CN.pdf)。
- **IPD 定义对应审计：**[英文](proofs/paper/ipd-fidelity.md) · [中文](proofs/paper/ipd-fidelity.zh-CN.md)。
- **Lean：**[英文构建说明与定理索引](lean/README.md) · [中文说明](lean/README.zh-CN.md)。
- **独立 Lean 项目：**[Y](lean/Y/README.zh-CN.md) · [RPD](lean/RPD/README.zh-CN.md) · [LRD](lean/LRD/README.zh-CN.md) · [Ω-LRD3](lean/Omega-LRD3/README.zh-CN.md) · [ARD](lean/ARD/README.zh-CN.md) · [IPD](lean/IPD/README.zh-CN.md) · [ARD2](lean/ARD2/README.zh-CN.md)。
- **可选联合入口：**[SevenNotationFinalAudit.lean](lean/src/SevenNotationFinalAudit.lean)。

每个记号各有独立构建配置、输出和验证收据，只依赖自己与[共享基础](lean/shared/README.zh-CN.md)；只有 Y 另需 BMS。新增记号不修改旧项目，也不强制重建旧证明。

Lean 工程形式化通常数学意义的良序定理，**不是在 Lean 中编码上述弱对象理论的推导**。论文的公理账本与 Lean 内核检查是两项不同成果。

Y 指固定上游提交 `1689b21131b488ec2ba2515bd630360371a2389d` 的继承祖先定义。这里不声称已完成该定义与原 Naruyoko JavaScript 在全部合法输入上的等价证明，正式证明部分也不收录七者序型比较、最优公理强度或证明论序数比较；另设研究目录保存未纳入正式定理的比较论证与候选。

## 序型比较研究（非正式定理）

新增的[研究目录](research/README.md)专门保存推导与比较草稿，与正式证明分开放置。当前收录 [IPD 比较总览](research/ordinal-comparisons-20260914/README.zh-CN.md)、Y≤RPD 的纸面比较思路、RPD/Y/wY/ARD/TPD 的 IPD 上界候选，以及 ARD2 与 IPD 的后续研究。每份总结区分纸面论证、局部引理、有限核验和未证候选；归档不等于完成跨记号的 Lean 认证。

关键原稿与候选数据一并保存，实验代码及私人来源稿不随文档归档。历史测试记录与正式仓库当前证明进度应分别阅读。

## 验证与重新生成 PDF

在本目录运行有界展开器测试：

```sh
python tests/test_python.py
python tests/test_ard.py
python tests/test_ipd.py
python tests/test_ard2.py
python -B tests/test_lean_verifier.py
node --max-old-space-size=256 tests/ard2_ner.cjs
node --max-old-space-size=256 tests/ard2_display.cjs
node --max-old-space-size=256 tests/ipd_display.cjs
node --max-old-space-size=256 tests/adjacency_views.cjs
```

固定依赖和串行、有资源上限的 Lean 构建方法见 [Lean 说明](lean/README.zh-CN.md)。Lean 编译不需要生成 PDF，也不需要 Node.js。

如需重建二十份发布用 PDF，安装 Pandoc、Node.js、文档工具依赖及适当的本机字体：

```sh
python -m pip install -r tools/requirements.txt
npm --prefix tools install
python tools/render_pdfs.py
python tools/qa_pdfs.py
```

生成器使用 ReportLab 和 MathJax 公式渲染，不会静默丢弃不支持的 Markdown 内容。Windows 下默认读取 `C:/Windows/Fonts`；可用 `--font-dir` 或 `ORDINAL_PDF_FONTS` 指定其他字体目录。本包不再分发字体。QA 命令另需 Poppler 的 `pdftoppm`，页面图在 Git 忽略的 `tmp/pdf-qa/` 下；重建成功不能代替目视检查。

本次检查结果见 [验收记录](VALIDATION.zh-CN.md)，发布前请阅读 [来源与许可证说明](SOURCES.zh-CN.md)。

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
proofs/paper/                    合写、ARD、IPD、ARD2 证明及双语定义对应审计
research/                       比较推导、未证候选及历史研究文稿
lean/                           源码依赖集合、固定版本与有界构建工具
tests/                          有界展开器与构建验证器回归测试
tools/                          可复现 PDF 生成及 QA
```

## 发布前事项

本项目自己的公开许可证**尚未指定**。收录的第三方材料保留其明确的许可证，但不能据此自动为新代码或论文指定许可证。由于固定的 BMS 源码树中未找到许可证，该依赖在构建时外部获取，详见 [说明](SOURCES.zh-CN.md)。本包不收录私人来源稿或机器专用的研究缓存。
