# 七个记号的 Lean 证明 · [English](README.md)

2026-09-17：默认 ARD2 现为轮廓版，旧完整包规则归入 [ARD2-legacy](ARD2-legacy/README.zh-CN.md)，21 个旧数学源码文件不变。新版有 7 个私有模块、57 模块精确闭包；旧版为 51 模块。当前联合入口为 [ARD2RevisionFinalAudit](src/ARD2RevisionFinalAudit.lean)，联合范围 338 模块。下方 9 月 14/16 日数字是历史记录；当前认证以各项目收据为准。新旧同构仍为纸面结果。

2026-09-16：默认 ARD 已切换到轮廓版，旧版完整保留为 ARD-legacy。新版实际规则良序已核查：56 模块、178 份报告，7 个新版模块新编译。旧版新位置也重新核查 50 模块、156 份报告。当前联合收据为 330 模块、897 份报告（5 个联合模块新编译，325 个已验证模块复用）；后文 2026-09-14 的拆分及网络说明保留为历史记录。完整新旧标准域同构和跨记号比较仍是纸面证明，不能由这些公理报告代替。


本目录整理 **Y、RPD、LRD、Ω-LRD3、ARD、IPD、ARD2** 在普通经典 Lean 中的良序证明。交付的是源码工程，而不是一批预编译证书。

限制公理体系的论证见另附的[四系统纸面证明](../proofs/paper/well-ordering.zh-CN.md)、[ARD 纸面证明](../proofs/paper/ard-well-ordering.zh-CN.md)、[IPD 纸面证明](../proofs/paper/ipd-well-ordering.zh-CN.md)及 [ARD2 纸面证明](../proofs/paper/ard2-well-ordering.zh-CN.md)。这些 Lean 定理**不是**对象理论 `KP_ω + 存在不可数序数` 中的形式推导；打印出来的宿主 Lean 公理依赖本身不证明这个元数学上界。

## 主要定理入口

优先进入所需记号自己的子项目。根目录的 [ARD2RevisionFinalAudit.lean](src/ARD2RevisionFinalAudit.lean) 仅是可选的联合验收入口，不是每次新增记号的必经构建。四个历史联合模块保持原样。

| 记号 | 最终模块 | 主要定理 |
| --- | --- | --- |
| Y | [FiniteDemandYFinal.lean](Y/src/FiniteDemandYFinal.lean) | `OrdinalFormal.YFiniteDemand.generated_strictWellOrder` |
| RPD | [FiniteDemandRPDFinal.lean](RPD/src/FiniteDemandRPDFinal.lean) | `OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder` |
| LRD | [FiniteDemandLRDFinal.lean](LRD/src/FiniteDemandLRDFinal.lean) | `OrdinalFormal.LRDFinal.standard_isWellOrder` |
| Ω-LRD3 | [OmegaLRD3Final.lean](Omega-LRD3/src/OmegaLRD3Final.lean) | `OrdinalFormal.Omega3Final.with_top_isWellOrder` |
| ARD-legacy | [ARDFinal.lean](ARD-legacy/src/ARDFinal.lean) | `OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder` |
| ARD | [ARDSkylineFinal.lean](ARD/src/ARDSkylineFinal.lean) | `OrdinalFormal.ARDSkyline.standard_with_top_strictWellOrder` |
| IPD | [IPDStandardOrder.lean](IPD/src/IPDStandardOrder.lean) | `IPD.standard_wellFounded`、`IPD.standard_total`、`IPD.term_wellFounded` |
| ARD2-legacy | [ARD2Final.lean](ARD2-legacy/src/ARD2Final.lean) | `OrdinalFormal.ARD2.paper_standard_with_top_strictWellOrder` |
| ARD2 | [ARD2SkylineFinal.lean](ARD2/src/ARD2SkylineFinal.lean) | `OrdinalFormal.ARD2Skyline.standard_with_top_strictWellOrder` |

各最终模块也提供展开关系良基性、有限式域结论或标准域变体。主要良序定理不要求调用者额外提供反射、初始表示、行标良基性或种子可及性假设。

Y 指固定上游的祖先继承定义。本工程**没有**证明它与原始 JavaScript 在所有合法执行上的完全等价。RPD 使用当前列图／完整根展开定义，并包含独立纸面标准域的等价桥。Ω-LRD3 使用每次增加一列的种子及含端点的行包 `0 ≤ t ≤ b`；不附带其他 Ω-LRD 版本。ARD-legacy 移动包括行锚在内的全部四个坐标，并生成严格低于移动后控制行的所有自然数行标。[独立有限规则桥](ARD-legacy/src/ARDDefinitionFidelity.lean)证明纸面标准域与可执行标准域相同；[ARDCompression.lean](ARD-legacy/src/ARDCompression.lean)证明规范最大根压缩列表与完整根列表的比较结果、控制项完全相同。这是与独立数学规则的等价证明，不是 Python 或 JavaScript 执行环境的编译器级验证。

IPD 的标准域是零起始种子的有限可达式，不是事后以可及性定义的子类型。实际父优先列序良基且全序，另加 TOP 仍良序；全部结构合法原始图的严格展开也良基，但不主张它们的全局列序良序。详见[定义对应审计](../proofs/paper/ipd-fidelity.zh-CN.md)。

ARD2 允许行与根同时 SELF，父仍严格向前。新版[子图桥](ARD2/src/ARD2SkylineBridge.lean)证明实际轮廓规则输出包含于旧完整包输出。后端的[有限规则桥](ARD2-legacy/src/ARD2DefinitionFidelity.lean)和[最大根压缩桥](ARD2-legacy/src/ARD2Compression.lean)针对 ARD2-legacy，不能误读成新旧轮廓同构的形式化。语义关系与初始供应均实际构造，并非额外前提。详见[定义](../notations/ARD2/definition.zh-CN.md)。

## 独立项目结构

| 项目 | 私有源码目录 | 私有模块数 | 精确证明闭包 |
| --- | --- | --- | --- |
| [Y](Y/README.zh-CN.md) | `Y/src/` | 163 | 189 |
| [RPD](RPD/README.zh-CN.md) | `RPD/src/` | 4 | 36 |
| [LRD](LRD/README.zh-CN.md) | `LRD/src/` | 10 | 41 |
| [Ω-LRD3](Omega-LRD3/README.zh-CN.md) | `Omega-LRD3/src/` | 13 | 44 |
| [ARD](ARD/README.zh-CN.md) | `ARD/src/` | 7 | 56 |
| [ARD-legacy](ARD-legacy/README.zh-CN.md) | `ARD-legacy/src/` | 20 | 50 |
| [IPD](IPD/README.zh-CN.md) | `IPD/src/` | 40 | 55 |
| [ARD2-legacy](ARD2-legacy/README.zh-CN.md) | `ARD2-legacy/src/` | 21 | 51 |
| [ARD2](ARD2/README.zh-CN.md) | `ARD2/src/` | 7 | 57 |
| [共享基础](shared/README.zh-CN.md) | `shared/src/` | 35 | 35 |
| 可选联合验收 | `src/` | 6 | 338 |

每个记号有自己的 `lakefile.lean`、工具链、锁文件、`sources.json`、`build.py`、构建输出和验证收据。原记号项目只依赖共享基础，只有 Y 还依赖外部 BMS。新版 ARD、ARD2 分别显式依赖各自 legacy 语义后端；无关记号项目仍相互独立。闭包数字包含实际使用的共享模块，不能直接相加当作不同模块总数。

现在共有 **326 个随库模块**（161 个原样上游 Y 模块、165 个本地模块），加 **12 个外部 BMS 模块**，证明源码并集为 **338**。两次轮廓修订各新增七个私有模块和一个联合入口。20 个 ARD-legacy 和 21 个 ARD2-legacy 数学源码文件只迁移目录、内容不变；此前所有联合源码原样保留。

[layout.json](layout.json) 是全库目录索引，不参与单个子项目的缓存指纹。各项目的 `sources.json` 才是其精确源码依赖清单，包含来源、版本、SHA-256 和真实路径。哈希将 CRLF 规范为 LF。共享基础保留部分历史上名带 RPD／LRD／ARD 的完整模块，因为其中的定义、引理已被多个项目使用；不因此依赖那些记号的私有项目。

## 单独构建

需要 Git、Python 3.10+ 与 Lean **4.33.1** 及其随附 Lake。例如只构建 ARD2，从仓库根目录运行：

```sh
cd lean/ARD2
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048 --publish
```

`lake build` 是常规构建；随后有界验证器从源码核对精确闭包、公理报告，并写本项目的 `.build/verification.json`。`--publish` 另写不含机器私有路径的 `VERIFICATION.json` 及选定日志。其他记号换用自己的目录即可。**不要在增加一个记号时默认运行根目录的联合构建。**

已准备好依赖环境后：

```sh
python build.py --check-only
lake env python build.py --resume --publish
```

`--check-only` 不下载或编译，检查本项目源码、闭包和 Lake 模块枚举。Y 的外部 BMS 源码若未提供，仅检查其清单结构；实际构建必须核对源码字节。`--resume` 是增量验证，不是全新重建：只复用同一验证环境下源码、递归依赖、产物及日志指纹均匹配的结果。

`--resume` 只接受上一次**完整成功**且当前仍匹配的收据，不支持从失败或中断的部分检查点继续编译；这种情况会重建当前项目的闭包。常规 Lake 的增量构建机制与此独立。

验证器一次只运行一个编译器、Lean 单线程、每编译器 **2048 MiB**、每模块 **120 秒**；超时只终止自己创建的进程树。这些限制不约束另行运行的依赖安装或任意 `lake build` 命令。

离线环境可通过 `--lean`、重复的 `--external-path` 提供 Lean 与已编译 Mathlib／辅助依赖目录。Y 和联合验收另需 `--bms-source`，必须是 BMS **源码**。不要把本项目其他旧证明缓存冒充外部库。机器路径仅写在本地命令行，不写入版本库。

验证期间应保持正在检查的源码、配置、编译器与外部依赖不变；验证器不是并发编辑下的快照协议。导入清单解析器针对当前源码使用的单行 `import M`／`public import M`；若将来改用 `meta import` 或 `import all`，必须先扩展解析器并重验，不能沿用旧闭包检查结论。

共享基础已有当前版本的验证产物时，可显式复用；例如先在 `lean/shared/` 运行有界验证器，再在 ARD2 项目内运行：

```sh
lake env python build.py --reuse-from ../shared --publish
python build.py --check-receipt
```

跨项目复用必须通过源码、环境、完整导入产物组与日志核对；收据会分别记录新编译和复用的模块。`--check-receipt` 仅检查已发布记录及当前源码，不重新运行内核，也不重新测量本机外部编译器环境。

## 新增记号不干扰旧记号

1. 新建自己的 `lean/名称/`，保存私有源码、配置、精确闭包清单和收据；依赖现有共享基础。
2. 保留旧记号的源码、锁文件、清单和收据。模块名使用不冲突的前缀；Lake 只声明自己拥有的模块。
3. 只编译新项目及它实际需要的共享依赖。全库 README／目录索引可更新；它们不是旧项目的缓存输入。
4. 需要全库联合验收时再更新根项目；根项目从不被叶项目反向依赖。
5. 若确实要修改旧共享引理或工具链，明确列出受影响项目并重验。不能承诺依赖改变后仍沿用旧证明收据。

## 依赖与验证范围

| 依赖 | 固定版本 |
| --- | --- |
| Mathlib | `eba3d887fc52c98627f4b81507c0efc3096e91b9` |
| BMS（仅 Y） | `bae7e3d741f24a56d80da9b99c1345562cd10c2d` |
| 随附 Y 源码 | `1689b21131b488ec2ba2515bd630360371a2389d` |

该 Mathlib 版本本身写的是 Lean 4.33.0-rc1，本包固定使用实际验证过的 4.33.1；其他编译器产物可能不兼容，必要时从固定源码重建依赖。远端缓存的存在性不是数学证明的前提。

拆分前的完整七系统重建已通过：**322 个模块、866 项公理报告、1638.176 秒**，记录保留在[历史七系统收据](verification/SevenNotation-Monolithic-VERIFICATION.json)。拆分后的各项目验证结果另行发布，不把旧收据改名冒充新布局重建。

已于 **2026-09-14** 完成新布局验证。[汇总收据](verification/IndependentProjects-VERIFICATION.json)核对了九个项目的真实收据：共享基础先从源码编译，各记号只复用已核验的共享产物并编译自己的私有源码，Y 另编译 12 个 BMS 模块，最后联合工程复用这些结果并编译四个联合模块。首轮迁移验收中，全库 **322 个不同的证明模块均在新布局下从源码编译一次，合计 866 项不同的公理报告**；不能把各项目含共享模块的闭包数字重复相加，也不把缓存复用称作全新编译。

各项目自己的 README 链接到独立的 `VERIFICATION.json`；逐项目新编译／复用数量见[验证记录](../VALIDATION.zh-CN.md)。真实 Lake 另通过九套配置的 18 项加载、归属、导入查找和默认枚举检查；[目录验收](verification/ProjectLayout-VERIFICATION.json)还记录了加入损坏的无关项目后 ARD2 仍通过的隔离测试。这是 Lake 配置验收；实际证明编译由有界验证器完成，不声称另完整运行过 `lake build`。

接受的报告公理仅为 `propext`、`Classical.choice`、`Quot.sound`（或其子集）。验证器拒绝 `sorryAx`、报告中的 `sorry`、额外公理、缺失导入、哈希不符和不完整报告。它不是 Lean 基础的证明论分析，也不是弱 KP 对象理论推导。网络全新初始化与 Mathlib 源码全量重建不在本次验收范围。生成的二进制与本地缓存不提交。

## 上游来源与许可证

161 个随附 Y 模块未经修改，来自 [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d)。Apache-2.0 许可证保留于 [licenses/1Y-Apache-2.0.txt](licenses/1Y-Apache-2.0.txt)，原源码声明均保留。

BMS 源码依赖来自 [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d)。在固定版本中没有发现 `LICENSE` 或 `NOTICE`，因此**这里不再分发 BMS 源码**，由 Lake 从原仓库另行获取。不要把 Y 仓库的许可证自动套到这个独立依赖上；如需自行再分发其源码，应先确认授权。

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) 及其依赖也另行获取，各自保留原许可证。上游许可证不代表本新项目所有原创代码和文档都已获得同一许可；项目所有者尚未选择统一的公开许可证。
