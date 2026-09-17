# ARD2 轮廓版：独立 Lean 项目 · [English](README.md)

默认 ARD2 已采用简化轮廓规则。本项目独有 **7 个模块**，精确证明源码闭包为 **57 个模块**。显式依赖 [ARD2-legacy](../ARD2-legacy/README.zh-CN.md) 的已有有限需求语义和 [shared](../shared/README.zh-CN.md) 基础；不修改其他记号的数学源码。

入口为 [ARD2SkylineFinal.lean](src/ARD2SkylineFinal.lean)，主定理是 `OrdinalFormal.ARD2Skyline.standard_with_top_strictWellOrder`，不剩反射、表示、可及性或良序性前提需要调用者提供。

## 数学范围

- [Core](src/ARD2SkylineCore.lean)：轮廓、移动后控制前驱、以接缝自身为借位上界、来源块展开和单记录种子。
- [Bridge](src/ARD2SkylineBridge.lean)：同一输入的新旧输出等宽，新版记录逐列包含于旧输出；据此限制语义表示。
- [Structure](src/ARD2SkylineStructure.lean)：合法性、排序、完整列前缀、嵌套种子、列序严格下降。来源切点列只有父坐标不动，行和根 SELF 都可能重绑。
- [Domain](src/ARD2SkylineDomain.lean)：实际有限生成域、外顶端和列序；不把可及性放进标准域。
- [语义下降](src/ARD2SkylineSemanticWellFounded.lean)与[标准序归约](src/ARD2SkylineOrderReduction.lean)：完成一般归约。
- [Final](src/ARD2SkylineFinal.lean)：用实际旧版需求关系、有界拼接及初始供给消去全部语义前提，另以内核归约核对小例。

有限实现选最大控制并筛选严格较低的优先级；在轮廓列上恰为末记录及其删除。每个追加列取轮廓。来源切点列按下一块搬运，两个 SELF 正确重绑。验证的是[新版小规则](../../notations/ARD2/definition.zh-CN.md)，不是给旧定理改名。

[完整新旧同构](../../proofs/paper/ard2-well-ordering.zh-CN.md)、计数保持、跨记号比较及弱 KP 内部可证性仍是**纸面结果**，不算新增 Lean 定理。也不是 Python/JS 编译器或虚拟机认证。

## 构建与收据

使用 Lean 4.33.1 及[总说明](../README.zh-CN.md)中的固定依赖，在本目录运行：

```sh
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048 --publish
python build.py --check-only
python build.py --check-receipt
```

[公开收据](VERIFICATION.json)日期为 2026-09-17，已通过 **57 模块 / 182 公理报告**：7 个新模块重新编译，50 个旧版／共享模块经源码及指纹核验后复用。报告只使用 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorryAx`。编译串行、单线程，每个编译器限制 2048 MiB、每模块 120 秒；超时只清理本次启动的进程树。本次使用已准备的固定依赖，不声称重新联网初始化或从源码构建整个 Mathlib。

`sources.json` 和精确 Lake globs 只拥有这七个模块。`ARD2Core` 等历史模块名由 **ARD2-legacy** 拥有，保留命名空间 `OrdinalFormal.ARD2`；新版定理使用 `OrdinalFormal.ARD2Skyline`。添加无关新记号不使本项目收据失效。
