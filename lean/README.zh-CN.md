# 四个记号的 Lean 证明 · [English](README.md)

本目录整理 **Y、RPD、LRD、Ω-LRD3** 在普通经典 Lean 中的良序证明。交付的是源码工程，而不是一批预编译证书。

限制公理体系的论证见另附的[纸面证明](../proofs/paper/well-ordering.zh-CN.md)。这些 Lean 定理**不是**对象理论 `KP_ω + 存在不可数序数` 中的形式推导；打印出来的宿主 Lean 公理依赖本身不证明这个元数学上界。

## 主要定理入口

建议先看 [FourNotationFinalAudit.lean](src/FourNotationFinalAudit.lean)：它导入四个最终模块，并打印七项公理依赖报告。

| 记号 | 最终模块 | 主要定理 |
| --- | --- | --- |
| Y | [FiniteDemandYFinal.lean](src/FiniteDemandYFinal.lean) | `OrdinalFormal.YFiniteDemand.generated_strictWellOrder` |
| RPD | [FiniteDemandRPDFinal.lean](src/FiniteDemandRPDFinal.lean) | `OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder` |
| LRD | [FiniteDemandLRDFinal.lean](src/FiniteDemandLRDFinal.lean) | `OrdinalFormal.LRDFinal.standard_isWellOrder` |
| Ω-LRD3 | [OmegaLRD3Final.lean](src/OmegaLRD3Final.lean) | `OrdinalFormal.Omega3Final.with_top_isWellOrder` |

各最终模块也提供展开关系良基性、有限式域结论或标准域变体。主要良序定理不要求调用者额外提供反射、初始表示、行标良基性或种子可及性假设。

Y 指固定上游的祖先继承定义。本工程**没有**证明它与原始 JavaScript 在所有合法执行上的完全等价。RPD 使用当前列图／完整根展开定义，并包含独立纸面标准域的等价桥。Ω-LRD3 使用每次增加一列的种子及含端点的行包 `0 ≤ t ≤ b`；不附带其他 Ω-LRD 版本。

## 源码结构

- `src/FiniteDemand*.lean`：有限需求语义构造及具体宿主 Lean 环境实例。
- `src/OrdinalFormal/`：列图、行包、比较、表示下降与三个新记号的定义。
- `src/OneY/`、`src/ZeroY/`：所需上游 Y 源码的完整依赖闭包，保持原样。
- `sources.json`：完整导入图、来源、固定版本和源码哈希。哈希先将 CRLF 换为 LF，不受 Git 换行符转换影响。
- `build.py`：有资源上限的源码验证与公理报告检查器。

本目录包含 **225 个 Lean 源码模块**：161 个未经修改的上游 Y 模块、64 个本地证明模块。另有 **12 个固定版本的 BMS 模块**由 Lake 作为外部依赖获取。证明源码闭包共 **237 个模块**，此外还依赖 Lean、Mathlib 及 Mathlib 的依赖库。发布内容不需要无关的暂停中对象理论研究、构建缓存、旧记号定义或机器私有绝对路径。

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

本次发布已于 **2026-09-13** 验证：全部 **237 个证明源码模块**均已重建，**554 项预期公理报告**全部通过。参见不含机器私有路径的[验收记录](VERIFICATION.json)，以及五个最终模块的实际日志：[Y](verification/FiniteDemandYFinal.log)、[RPD](verification/FiniteDemandRPDFinal.log)、[LRD](verification/FiniteDemandLRDFinal.log)、[Ω-LRD3](verification/OmegaLRD3Final.log)、[联合验收](verification/FourNotationFinalAudit.log)。联合验收打印七项报告；五个最终日志合计包含 28 项报告。

这是完整证明源码闭包的全新重建，使用了既有 Lean／Mathlib／依赖库产物；**不是**一次从零联网安装，也没有从源码重建 Mathlib。Lake 配置另行通过类型检查，每个随附模块都已核对归属于配置声明的库根。交付中不包含编译后的证明二进制文件和临时构建日志；保留的验收记录与最终日志记录了实际验证结果。

允许的公理集合是 `propext`、`Classical.choice`、`Quot.sound`，或其子集。验证器拒绝 `sorryAx`、被报告为使用 `sorry` 的声明、打印报告中的额外公理、缺少导入、哈希不符及报告数量不完整。这不等于对 Lean 基础的证明论分析，也不宣称找到了记号的最小公理上界。

## 上游来源与许可证

161 个随附 Y 模块未经修改，来自 [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d)。Apache-2.0 许可证保留于 [licenses/1Y-Apache-2.0.txt](licenses/1Y-Apache-2.0.txt)，原源码声明均保留。

BMS 源码依赖来自 [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d)。在固定版本中没有发现 `LICENSE` 或 `NOTICE`，因此**这里不再分发 BMS 源码**，由 Lake 从原仓库另行获取。不要把 Y 仓库的许可证自动套到这个独立依赖上；如需自行再分发其源码，应先确认授权。

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) 及其依赖也另行获取，各自保留原许可证。上游许可证不代表本新项目所有原创代码和文档都已获得同一许可；项目所有者尚未选择统一的公开许可证。
