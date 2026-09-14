# 六个记号的 Lean 证明 · [English](README.md)

本目录整理 **Y、RPD、LRD、Ω-LRD3、ARD、IPD** 在普通经典 Lean 中的良序证明。交付的是源码工程，而不是一批预编译证书。

限制公理体系的论证见另附的[四系统纸面证明](../proofs/paper/well-ordering.zh-CN.md)、[ARD 纸面证明](../proofs/paper/ard-well-ordering.zh-CN.md)及 [IPD 纸面证明](../proofs/paper/ipd-well-ordering.zh-CN.md)。这些 Lean 定理**不是**对象理论 `KP_ω + 存在不可数序数` 中的形式推导；打印出来的宿主 Lean 公理依赖本身不证明这个元数学上界。

## 主要定理入口

建议先看 [SixNotationFinalAudit.lean](src/SixNotationFinalAudit.lean)：它导入未修改的[五系统验收](src/FiveNotationFinalAudit.lean)、IPD 最终定理及实际递归比较方程，打印十项公理报告。原四系统和五系统入口保持不变。

| 记号 | 最终模块 | 主要定理 |
| --- | --- | --- |
| Y | [FiniteDemandYFinal.lean](src/FiniteDemandYFinal.lean) | `OrdinalFormal.YFiniteDemand.generated_strictWellOrder` |
| RPD | [FiniteDemandRPDFinal.lean](src/FiniteDemandRPDFinal.lean) | `OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder` |
| LRD | [FiniteDemandLRDFinal.lean](src/FiniteDemandLRDFinal.lean) | `OrdinalFormal.LRDFinal.standard_isWellOrder` |
| Ω-LRD3 | [OmegaLRD3Final.lean](src/OmegaLRD3Final.lean) | `OrdinalFormal.Omega3Final.with_top_isWellOrder` |
| ARD | [ARDFinal.lean](src/ARDFinal.lean) | `OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder` |
| IPD | [IPDStandardOrder.lean](src/IPDStandardOrder.lean) | `IPD.standard_wellFounded`、`IPD.standard_total`、`IPD.term_wellFounded` |

各最终模块也提供展开关系良基性、有限式域结论或标准域变体。主要良序定理不要求调用者额外提供反射、初始表示、行标良基性或种子可及性假设。

Y 指固定上游的祖先继承定义。本工程**没有**证明它与原始 JavaScript 在所有合法执行上的完全等价。RPD 使用当前列图／完整根展开定义，并包含独立纸面标准域的等价桥。Ω-LRD3 使用每次增加一列的种子及含端点的行包 `0 ≤ t ≤ b`；不附带其他 Ω-LRD 版本。ARD 移动包括行锚在内的全部四个坐标，并生成严格低于移动后控制行的所有自然数行标。[独立有限规则桥](src/ARDDefinitionFidelity.lean)证明纸面标准域与可执行标准域相同；[ARDCompression.lean](src/ARDCompression.lean)证明规范最大根压缩列表与完整根列表的比较结果、控制项完全相同。这是与独立数学规则的等价证明，不是 Python 或 JavaScript 执行环境的编译器级验证。

IPD 的标准域是零起始种子的有限可达式，不是事后以可及性定义的子类型。实际父优先列序良基且全序，另加 TOP 仍良序；全部结构合法原始图的严格展开也良基，但不主张它们的全局列序良序。详见[定义对应审计](../proofs/paper/ipd-fidelity.zh-CN.md)。

## 源码结构

- `src/FiniteDemand*.lean`：有限需求语义构造及具体宿主 Lean 环境实例。
- `src/OrdinalFormal/`：共享列图、行包、比较、表示下降与原三个新记号的定义。
- `src/ARD*.lean`：ARD 动态有限需求构造、实际分阶段拼接、标准域良序、独立规格及表示桥；定义见 [ARD 参考文档](../notations/ARD/definition.zh-CN.md)。
- `src/IPD*.lean`：40 个模块，包含树 LPO、精确降低、有限模板、真实见证闭包、完整分阶段拼接和标准列序；没有拿 Y/ARD 良序定理替代 IPD。
- `src/OneY/`、`src/ZeroY/`：所需上游 Y 源码的完整依赖闭包，保持原样。
- `sources.json`：完整导入图、来源、固定版本和源码哈希。哈希先将 CRLF 换为 LF，不受 Git 换行符转换影响。
- `build.py`：有资源上限的源码验证与公理报告检查器。

本目录包含 **288 个 Lean 源码模块**：161 个未经修改的上游 Y 模块、127 个本地证明模块。另有 **12 个固定版本的 BMS 模块**由 Lake 作为外部依赖获取。证明源码闭包共 **300 个模块**，此外还依赖 Lean、Mathlib 及 Mathlib 的依赖库。发布内容不需要无关的暂停中对象理论研究、构建缓存、旧记号定义或机器私有绝对路径。

发布副本中的 `OrdinalFormal/Domains.lean` 与 `OrdinalFormal/StandardValidity.lean` 删去了不用的早期记号声明；保留的 RPD/LRD 证明项没有改变。另外两个最终模块只修改了注释，以区分已完成的纸面论证与尚未声称完成的对象语言 Lean 认证。`sources.json` 记录了这些变动及原始源码哈希。

## 重新构建

需要 Git、Python 3.10 或更新版本，以及 Lean/Lake **4.33.1**（通常通过 elan 安装）。在本目录运行：

```sh
lake --keep-toolchain update
lake build
lake env python build.py
```

`lake build` 是包含依赖库的标准可移植构建；随后 `build.py` 重编译精确的证明源码闭包，核对预期公理报告，并生成本地 `.build/verification.json`。部分系统的 Python 命令叫 `python3`。

固定的源码依赖版本如下：

| 依赖 | 版本 |
| --- | --- |
| Mathlib | `eba3d887fc52c98627f4b81507c0efc3096e91b9` |
| BMS / `YesMetaZFC` | `bae7e3d741f24a56d80da9b99c1345562cd10c2d` |
| 随附 1Y 源码 | `1689b21131b488ec2ba2515bd630360371a2389d` |

固定的 Mathlib 源码自身注明 Lean 4.33.0-rc1；本工程有意使用既有验证采用的 4.33.1。请保持本工程工具链不变。不同编译器生成的缓存可能无法读取，此时需要从固定源码重建依赖；远程预编译缓存是否可用，不属于数学证明的一部分。

依赖环境准备好后，可以直接运行有资源限制的验证器：一次只运行一个编译器进程，Lean 单线程，**每个编译器上限 2048 MiB**，**每模块墙钟超时 120 秒**。这些限制针对 `build.py`，不自动约束任意依赖安装命令。超时会终止该次创建的子进程树，不按名称清理其他进程。

```sh
python build.py --check-only
lake env python build.py --seconds 120 --memory-mb 2048
lake env python build.py --resume
```

`--check-only` 不下载任何内容，只核对随附源码与清单闭包。如果 BMS 尚未获取，则先检查其 12 项清单结构，获取后在构建时验证实际字节。`--resume` 只复用本验证器针对相同编译器、相同传递源码指纹认证过的产物哈希；这属于增量检查，不是全新重编译。

离线环境可使用 `--lean`、`--bms-source` 及可重复的 `--external-path` 参数。提供固定 BMS **源码**和已构建的 Mathlib／依赖导入目录，不要拿本工程预编译证明模块替代源码验证。这类机器路径只写在本地命令行，不要提交到配置中。

## 验证范围与状态

已于 **2026-09-14** 验证：全部 **300 个证明源码模块**在发布目录自己的输出目录内从源码全新重建，**774 项预期公理报告**全部通过。完整重建耗时 **1657.966 秒**；随后通过 `--resume` 再次核对每个模块的源码／依赖指纹与产物哈希。参见不含机器私有路径的[验收记录](VERIFICATION.json)。

新增真实日志包括 [IPD 标准序](verification/IPDStandardOrder.log)（3 项）、[完整图语义下降](verification/IPDSemanticWellFounded.log)（3 项）、[实际递归树比较](verification/IPDTreeCompare.log)（3 项）、[六系统联合验收](verification/SixNotationFinalAudit.log)（10 项）。

此前的[四系统验收记录](verification/FourNotation-VERIFICATION.json)和[五系统验收记录](verification/FiveNotation-VERIFICATION.json)作为历史记录保留。九份旧日志不变：[Y](verification/FiniteDemandYFinal.log)、[RPD](verification/FiniteDemandRPDFinal.log)、[LRD](verification/FiniteDemandLRDFinal.log)、[Ω-LRD3](verification/OmegaLRD3Final.log)、[四系统联合验收](verification/FourNotationFinalAudit.log)、[ARD](verification/ARDFinal.log)、[五系统联合验收](verification/FiveNotationFinalAudit.log)、[独立规则等价桥](verification/ARDDefinitionFidelity.log)、[压缩／完整根表示桥](verification/ARDCompression.log)。十三份发布的最终／桥日志全部与本次六系统重建的对应日志按 LF 字节核对，完全一致，合计包含 **77 项报告**；历史验收记录只描述各自此前的构建。

本次使用既有 Lean／Mathlib／依赖库产物，不是从零联网安装或重建 Mathlib；没有使用研究工作区的证明二进制替代发布源码重编译。实际 Lake 使用固定外部包的临时本地覆盖，成功离线载入了发布配置；全部随附模块也通过了库根归属检查。本地构建产物已被 Git 忽略，交付内容只包含源码、验收记录和选定日志。

允许的公理集合是 `propext`、`Classical.choice`、`Quot.sound`，或其子集。验证器拒绝 `sorryAx`、被报告为使用 `sorry` 的声明、打印报告中的额外公理、缺少导入、哈希不符及报告数量不完整。这不等于对 Lean 基础的证明论分析，也不宣称找到了记号的最小公理上界。

## 上游来源与许可证

161 个随附 Y 模块未经修改，来自 [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d)。Apache-2.0 许可证保留于 [licenses/1Y-Apache-2.0.txt](licenses/1Y-Apache-2.0.txt)，原源码声明均保留。

BMS 源码依赖来自 [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d)。在固定版本中没有发现 `LICENSE` 或 `NOTICE`，因此**这里不再分发 BMS 源码**，由 Lake 从原仓库另行获取。不要把 Y 仓库的许可证自动套到这个独立依赖上；如需自行再分发其源码，应先确认授权。

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) 及其依赖也另行获取，各自保留原许可证。上游许可证不代表本新项目所有原创代码和文档都已获得同一许可；项目所有者尚未选择统一的公开许可证。
