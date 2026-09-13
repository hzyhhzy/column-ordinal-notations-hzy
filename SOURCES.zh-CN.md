# 来源、版本与许可证 · [English](SOURCES.md)

本包是 [column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy) 于 2026-09-13 整理的源码快照。来源与证明边界也是交付内容，不会为了展示方便而删去。

## 记号实现

LRD、Ω-LRD3 继续与选定工作版本逐字节一致。RPD、ARD 新增文字和三角表格两种邻接表显示，并更新注册信息；每份文件完整嵌入提交 `542d47a` 中此前发布的原脚本，统一换行符后核验原文不变。展开、比较、已有显示和原资源保护均保留，新视图另设完整输出保护。下表哈希固定交付文件的实际字节。

| 脚本 | SHA-256 |
| --- | --- |
| `notations/RPD/RPD-mountain.ne-rewritten.js` | `447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026` |
| `notations/LRD/LRD.ne-rewritten.js` | `394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1` |
| `notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js` | `fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab` |
| `notations/ARD/ARD-arcs.ne-rewritten.js` | `ab4f05ef1fb65b6308e710cbbc98c173310f9c3073ce3a57082863af708841d6` |

RPD 是当前按列比较、带山脉图及邻接表显示的版本，不是早期按操作历史排序的记号。浏览器菜单名为 `RDP`，记号及文件名仍为 RPD。LRD 使用固定的序数多项式行标。Ω-LRD3 的生成包包含至指标 `b`，顶端基本列采用每级只加一列的种子塔。不收录其他 Ω-LRD 实现。

ARD 全称为 *Anchored Row Diagrams*（锚定行图）。它用此前列的地址作为行锚，四个关系坐标一起移动。所选独立浏览器脚本为弧线图版本，根标签保留圆圈或胶囊外框；本次加入未改数学规则及资源保护。Python 模块保留可读的 `AnchoredRows` 类与最大根压缩。未把旧山脉图 ARD 另作为重复实现收录。

Python 文件提供只依赖标准库的独立数学核心。RPD、LRD 由已有简易核心整理；Ω-LRD3 按规则实现，并与 `tests/omega3_tuple_reference.py` 内的旧有限元组参考独立对照。它们不设数学截断规则，也不判断标准域成员资格。有界测试是实现一致性的证据，不是全输入解释器等价定理，也不能替代良序证明。

宿主为 [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/)。本包不复制宿主源码、用户数据或浏览器状态。测试中的注册接口桩不等于新做了一次完整浏览器集成测试。

## 证明来源

合写论文完整呈现四个记号的弱 KP 论证，中英文均为全文，不只是摘要翻译。来源稿为用户提供的简化稿 *A Short Proof of 1-Y Well-Ordering in KP with ω₁*。本包**不再分发该来源稿**；其识别哈希及公开背景文献见 [论文参考资料](proofs/paper/well-ordering.zh-CN.md)。读者无需访问原作者电脑上的文件路径。

独立的 [ARD 论文](proofs/paper/ard-well-ordering.zh-CN.md) 把有限需求方法扩展到动态行引用，完整记录带保护条件的关系、闭高度供应、四坐标拼接、标准域论证及弱公理账本。两种语言均为全文。普通 Lean 实现实际构造所需关系及初始供应，而非将其作为假设；有限并集规格、压缩根与完整根的比较桥也是单独的定理，不是从解释器测试推测的结论。

有限 Y 几何固定到 [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d)，提交为 `1689b21131b488ec2ba2515bd630360371a2389d`。本包保留继承祖先 Y 定义，明确不声称它与原 Naruyoko JavaScript 全域等价。普通 Lean 证明与限定公理体系的纸面证明具有不同验证范围。

Lean 的完整导入依赖集合及换行归一化的源码哈希见 [lean/sources.json](lean/sources.json)；固定依赖版本、仅在发布副本中的改动及最终定理索引见 [lean/README.zh-CN.md](lean/README.zh-CN.md)。

## 许可证边界

- 本项目自己的记号代码、Python 代码、论文与打包工具尚未选择公开许可证。发布仓库本身不会自动授予开源许可。
- 收录的 161 个未修改 Y 模块保留上游 Apache-2.0，副本位于 [lean/licenses/1Y-Apache-2.0.txt](lean/licenses/1Y-Apache-2.0.txt)，原有源码声明也保留。
- 检查的固定版本 [BMS 仓库](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d) 没有 `LICENSE` 或 `NOTICE` 文件，因此本包**不内置其源码**，只在构建时获取固定依赖。不能靠推测为它指定再分发许可。
- Mathlib 和文档渲染包属于外部依赖，各自保留许可证。安装包、字体和编译缓存均不是发布源码。

本项目尚未选择整体许可证。公开可见不等于授予一揽子再使用许可；应保留上述第三方声明，并在再分发其他源码材料前检查相应许可。
