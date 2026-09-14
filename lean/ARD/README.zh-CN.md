# ARD：独立 Lean 子项目 · [English](README.md)

本项目独有 **20 个 Lean 源码模块**，精确证明源码闭包共 **50 个模块**，包括实际导入的共享模块。它不依赖其他记号的私有项目。

主要入口：[ARDFinal.lean](src/ARDFinal.lean)。主要定理：`OrdinalFormal.ARD.paper_standard_with_top_strictWellOrder`。完整定理范围，以及普通 Lean 与纸面弱集合论证明的区别，见[总说明](../README.zh-CN.md)。

## 只构建这个记号

在本目录内运行，需要 Lean 4.33.1 及其随附 Lake，另需 Python 3.10+：

```sh
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048
```

常规 Lake 构建与额外的有界验证器是两项不同检查。已有离线依赖环境的用法见总说明。仅检查源码、不编译或下载：

```sh
python build.py --check-only
```

后续验证可用 `lake env python build.py --resume`，仅复用源码、依赖和验证指纹仍匹配的产物。有界验证器的输出只写入本项目的 `.build/`（常规 Lake 产物使用 `.lake/build/`）；增加同级新记号不会改变本项目的源码清单，也不要求它重新编译。本项目不获取或编译 BMS。

## 维护边界

- 私有证明放在 `src/`，本项目 `lakefile.lean` 只声明这些模块。
- [sources.json](sources.json) 记录精确的递归源码依赖，包括实际使用的 [shared](../shared/README.zh-CN.md) 文件。
- 增加新记号时，不修改旧记号的源码、锁文件或收据；可选的联合工程及仓库索引另行维护。
- 实际使用的共享引理若变动，应重新检查受影响的使用者。共享源码只维护一份，不通过复制私有依赖制造项目间耦合。

从原联合工程拆出时，全部模块名和数学源码字节保持不变。

## 本次验证

2026-09-14 的[独立项目收据](VERIFICATION.json)：**50 个模块、156 项公理报告**通过；其中 20 个模块在本次从源码编译，30 个复用刚刚核验的共享产物。报告只使用普通 Lean 的 `propext`、`Classical.choice`、`Quot.sound` 或其子集；这不是弱 KP 对象理论形式化。
