# 来源、版本与许可证 · [English](SOURCES.md)

本包是 [column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy) 于 2026-09-14 整理的源码快照。来源与证明边界也是交付内容，不会为了展示方便而删去。

## 记号实现

LRD、Ω-LRD3 继续与选定工作版本逐字节一致。RPD、ARD 新增文字和三角表格两种邻接表显示，并更新注册信息；每份文件完整嵌入提交 `542d47a` 中此前发布的原脚本，统一换行符后核验原文不变。展开、比较、已有显示和原资源保护均保留，新视图另设完整输出保护。下表哈希固定交付文件的实际字节。

| 脚本 | SHA-256 |
| --- | --- |
| `notations/RPD/RPD-mountain.ne-rewritten.js` | `447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026` |
| `notations/LRD/LRD.ne-rewritten.js` | `394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1` |
| `notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js` | `fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab` |
| `notations/ARD/ARD-arcs.ne-rewritten.js` | `ab4f05ef1fb65b6308e710cbbc98c173310f9c3073ce3a57082863af708841d6` |
| `notations/IPD/IPD.ne-rewritten.js` | `acc1a1c2ae260da9be7d13e14ac17d84a92679f82efe97aa85cd0e3b072f6011` |
| `notations/ARD2/ARD2.ne-rewritten.js` | `e0d4eb14056ee54a6d4a8d2475241469ba33f07d38c406cfa9b20c648407380d` |
| `notations/SPD/SPD.ne-rewritten.js` | `d693c23564a766ecbbe3072cd200632c49b490d47d18428e1310ea438e85f266` |

RPD 是当前按列比较、带山脉图及邻接表显示的版本，不是早期按操作历史排序的记号。浏览器菜单名为 `RDP`，记号及文件名仍为 RPD。LRD 使用固定的序数多项式行标。Ω-LRD3 的生成包包含至指标 `b`，顶端基本列采用每级只加一列的种子塔。不收录其他 Ω-LRD 实现。

ARD 全称为 *Anchored Row Diagrams*（锚定行图）。它用此前列的地址作为行锚，四个关系坐标一起移动。所选独立浏览器脚本为弧线图版本，根标签保留圆圈或胶囊外框；本次加入未改数学规则及资源保护。Python 模块保留可读的 `AnchoredRows` 类与最大根压缩。未把旧山脉图 ARD 另作为重复实现收录。

IPD 全称为 *Iterated Profile Diagrams*（迭代轮廓图）。零起始 JS 与可读 Python 均与已证明的参考版本逐字节一致；`notations/IPD/ipd.py` 的 SHA-256 为 `12d3f08fd38fc51aa78b9972bae2d5e02fc8efc09de085a9b1752880948ebab1`。所有嵌套头中的 ROOT/SELF 都参与移动，保留列表、计数和完整树形显示；`FS`、`FS_alter`、`FS_short` 规则相同。冻结代码的历史注释以当前论文为准。不收录实验性的 TPD、wY 比较草稿。

ARD2 是 Anchored Row Diagrams 的全上下文版本。新增可读的 `ARD2` Python 类与 NER 脚本使用行、根两种 SELF，并生成直到接缝自身的根包。保留精确的列表／计数／弧线／文字邻接／表格邻接显示；局部计数专门适配双 SELF 规则，不套用旧 ARD 捷径。旧记号源码及规则均未改变。Lean 子项目重组时，只更新 NER 脚本中的两处说明路径及 Python 文档字符串中的一处路径，数学与绘图算法均未改动；因此 ARD2 两个实现文件不再与提交 `e2bdd08` 逐字节一致。Python 文件当前 SHA-256 为 `05a9b14d9897db8e64e2c907eb3d3e326e6768600e1c7fcb27cd336990fb2e68`；其他五个记号实现与此前二十份 PDF 仍与该提交逐字节一致。

SPD 全称为 *Slot Profile Diagrams*（潜边轮廓图）。固定 2026-09-14 版本采用四整数关系、最高可见头纤维、LATENT 低包、严格连接守卫、仅第二块起的同头携带和完整纯来源副本。共享递归头从实际此前列派生，不作为独立树字段输入。不收录实验性 refresh/splice 变体及非严格连接变体。NER 脚本相对固定研究版仅修改开头的文档链接，规则、两种显示和资源保护均未改变。

SPD Python 核心及独立标准计数解码器与该固定版本逐字节相同。SHA-256 分别为 `c3f72538aa71f8b4f43cf593d00731bfff38cafa3705462d1736de203591b826`（`spd.py`）及 `34e8a7a26a225c3d2dbd837baad3805fd02436b071faa356852524e5d0fdf075`（`spd_count_decode.py`）。解码器在预算足够时可以判断标准性，不把超时当作否定答案。发布测试使用独立的元组参考，不导入私人研究目录。此次加入不修改原六个记号实现或七个 Lean 项目。

Python 文件提供只依赖标准库的独立数学核心。RPD、LRD 由已有简易核心整理；Ω-LRD3 按规则实现，并与 `tests/omega3_tuple_reference.py` 内的旧有限元组参考独立对照。这三个实现不设数学截断规则，也不判断标准域成员资格。有界测试是实现一致性的证据，不是全输入解释器等价定理，也不能替代良序证明。

宿主为 [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/)。本包不复制宿主源码、用户数据或浏览器状态。测试中的注册接口桩不等于新做了一次完整浏览器集成测试。

## 证明来源

合写论文完整呈现四个记号的弱 KP 论证，中英文均为全文，不只是摘要翻译。来源稿为用户提供的简化稿 *A Short Proof of 1-Y Well-Ordering in KP with ω₁*。本包**不再分发该来源稿**；其识别哈希及公开背景文献见 [论文参考资料](proofs/paper/well-ordering.zh-CN.md)。读者无需访问原作者电脑上的文件路径。

独立的 [ARD 论文](proofs/paper/ard-well-ordering.zh-CN.md) 把有限需求方法扩展到动态行引用，完整记录带保护条件的关系、闭高度供应、四坐标拼接、标准域论证及弱公理账本。两种语言均为全文。普通 Lean 实现实际构造所需关系及初始供应，而非将其作为假设；有限并集规格、压缩根与完整根的比较桥也是单独的定理，不是从解释器测试推测的结论。

[IPD 论文](proofs/paper/ipd-well-ordering.zh-CN.md) 收录完整直接 KP 树秩、有界递归、初等高度和显式 Bad/Ext 见证闭包两条路线、真实整图拼接及从 L 转移集合秩。[定义对应审计](proofs/paper/ipd-fidelity.zh-CN.md) 区分 Lean 数学算法与纸面源语言对应、JS 精确剪枝证明。40 个 IPD 模块使用既有 `IPD...` 导入名，源码规范化记录于清单，原有证明模块不变。

[ARD2 论文](proofs/paper/ard2-well-ordering.zh-CN.md) 给出有界行根对优先递归、四种顶端谓词、pointed pair 端点一致性、强供应、实际双 SELF 拼接及绝对集合秩。21 个新增 Lean 模块真实构造关系及见证闭包，七系统联合入口另导入压缩／全根桥。普通 Lean 不是对象语言 KP 推导，也不是 ARD2 大于 ARD 或 IPD 的证明。

有限 Y 几何固定到 [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d)，提交为 `1689b21131b488ec2ba2515bd630360371a2389d`。本包保留继承祖先 Y 定义，明确不声称它与原 Naruyoko JavaScript 全域等价。普通 Lean 证明与限定公理体系的纸面证明具有不同验证范围。

七个 Lean 证明现在是同一仓库内的独立子项目。各自精确源码导入清单为 [Y](lean/Y/sources.json)（189 模块）、[RPD](lean/RPD/sources.json)（36）、[LRD](lean/LRD/sources.json)（41）、[Ω-LRD3](lean/Omega-LRD3/sources.json)（44）、[ARD](lean/ARD/sources.json)（50）、[IPD](lean/IPD/sources.json)（55）、[ARD2](lean/ARD2/sources.json)（51）。每份清单是本项目的完整依赖闭包，包含需要的共享模块及相应压缩根／树比较附加入口，而不是把总闭包复制七遍。只有 Y 包含 12 个固定外部 BMS 模块。

[共享包](lean/shared/sources.json) 拥有 35 个源码模块，同一物理源文件由各记号复用，不重复复制；每个记号只导入自己需要的共享子集。有些共享文件仍保留历史 RPD／LRD／ARD 前缀，因为其中同时包含被复用的有限引理及原有声明，不能按文件名前缀判断项目归属。[布局清单](lean/layout.json) 记录每个模块的归属与仓库相对文件路径；源码记录的 `source` 保留溯源含义，`file` 才是当前内置文件位置。

[总清单](lean/sources.json) 仍覆盖全部 322 个模块，`lean/src` 只保留四个联合审计入口。本次迁移 306 个文件，310 个内置 Lean 文件的字节及模块名均未改变；161 个上游 Y 模块现位于 `lean/Y/src`，外部 BMS 源码仍不内置。换行归一化哈希与原始上游记录均保留。固定依赖版本、验证状态及最终定理索引见 [lean/README.zh-CN.md](lean/README.zh-CN.md)。

双语 [SPD 文稿](proofs/paper/spd-well-ordering.zh-CN.md) 汇总固定规则的局部秩接口、正的新父子句、端点一致性与闭高度供应、精确连接拼接、最小末标签秩及标准后代锥论证。既有 KP 秩和见证闭包机制准确引用随附 IPD 论文。**没有 SPD Lean 形式化或内核收据。** 此次纸面文稿不扩充七系统 Lean 验收范围，也不主张与 ARD、ARD2、wY 或整个 IPD 的序型大小比较。

## 许可证边界

- 本项目自己的记号代码、Python 代码、论文与打包工具尚未选择公开许可证。发布仓库本身不会自动授予开源许可。
- 收录的 161 个未修改 Y 模块保留上游 Apache-2.0，副本位于 [lean/licenses/1Y-Apache-2.0.txt](lean/licenses/1Y-Apache-2.0.txt)，原有源码声明也保留。
- 检查的固定版本 [BMS 仓库](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d) 没有 `LICENSE` 或 `NOTICE` 文件，因此本包**不内置其源码**，只在构建时获取固定依赖。不能靠推测为它指定再分发许可。
- Mathlib 和文档渲染包属于外部依赖，各自保留许可证。安装包、字体和编译缓存均不是发布源码。

本项目尚未选择整体许可证。公开可见不等于授予一揽子再使用许可；应保留上述第三方声明，并在再分发其他源码材料前检查相应许可。
