# ARD 轮廓版：独立 Lean 项目 · [English](README.md)

当前 ARD 使用简化轮廓规则。本项目拥有 **7 个模块**，精确依赖闭包为 **56 个模块**。明确依赖 [ARD-legacy](../ARD-legacy/README.zh-CN.md) 提供已证明的有限需求语义，以及[共享基础](../shared/README.zh-CN.md)。没有改动或复制其他记号的私有源码。

主入口为 [ARDSkylineFinal.lean](src/ARDSkylineFinal.lean)，主要定理是 `OrdinalFormal.ARDSkyline.standard_with_top_strictWellOrder`。没有未实例化的反射、表示、可及性或良序假设。

## 核查内容

- [核心](src/ARDSkylineCore.lean)：有限轮廓规范化、移动后控制的单个前驱、来源块展开和单记录种子。
- [桥接](src/ARDSkylineBridge.lean)：同一输入下，新版每条输出边都属于旧版对应列，且宽度相同；语义表示沿这个已证包含关系限制。
- [结构](src/ARDSkylineStructure.lean)：合法性、有序性、精确前缀、种子嵌套及实际列比较严格下降。
- [标准域](src/ARDSkylineDomain.lean)：以有限生成定义标准性，不以可及性倒定义；外顶端显式给出。
- [语义下降](src/ARDSkylineSemanticWellFounded.lean)及[标准序](src/ARDSkylineOrderReduction.lean)：完成一般归约。
- [最终定理](src/ARDSkylineFinal.lean)：用实际旧版有限需求关系及初始供给实例化全部语义条件。

有限规则用“最大控制、严格较低优先级筛选”书写；轮廓列上就是末记录及删末记录。每个追加列规范化，而搬运后的内部来源轮廓已经规范，故不变。这与[定义](../../notations/ARD/definition.zh-CN.md)的小规则相同，不是给旧整包展开改名后的定理。

完整的新旧标准域同构、`ARD(1,2) ≥ RPD ≥ 1Y`，以及弱 KP 对象理论内的可推导性仍是**纸面结果**，不属于新增 Lean 声明。也不声称编译器级验证了 JS/Python。

## 构建与收据

使用 Lean 4.33.1 和[中央说明](../README.zh-CN.md)中的固定依赖。在本目录运行：

```sh
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048 --publish
python build.py --check-only
python build.py --check-receipt
```

2026-09-16 的[公开收据](VERIFICATION.json)记录 **56 个模块、178 份公理报告**通过；7 个模块新编译，49 个模块从明确指定、重新验证的旧版及共享依赖复用。报告公理均为 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或额外公理。

有界验证器只用一个编译进程和线程，每模块最多 2048 MiB、120 秒，超时仅清理自己的子进程树。普通 Lake 构建、全新网络引导另算；本次使用已准备好的固定依赖，没有从源码重编 Mathlib 或测试全新联网安装。

[sources.json](sources.json) 与 Lake 精确模块表只拥有七个新版模块。旧 `ARDCore` 等模块属于明确的 **ARD-legacy** 后端，保留历史命名空间 `OrdinalFormal.ARD`；新版定理位于 `OrdinalFormal.ARDSkyline`。新增无关记号不会使本项目收据失效。
