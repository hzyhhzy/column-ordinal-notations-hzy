# 共享 Lean 基础 · [English](README.md)

本项目独有 **35 个模块**，是两个或更多记号共同使用的源码及其共享依赖。它依赖固定版本的 Mathlib 环境，不依赖任何记号的私有项目或 BMS。源码只在 `src/` 保存一份。

部分模块保留历史上的 RPD、LRD 或 ARD 名字，其中可复用定义与引理原本已被多个记号导入。本次拆分刻意保留完整源文件、模块名和证明项；这些名字不构成对 RPD／LRD／ARD 子项目的依赖。

各子项目的 `sources.json` 只包含自己实际导入的共享模块。新记号可使用共享包，而不修改任何既有子项目的配置。

在本目录运行：

```sh
python build.py --check-only
lake --keep-toolchain update
lake build
lake env python build.py --seconds 120 --memory-mb 2048
```

有界验证器产物保存在本项目的 `.build/`；常规 Lake 产物使用 `.lake/build/`。离线验证、缓存、证明范围及新增记号流程见[总说明](../README.zh-CN.md)。实际修改共享依赖时，需检查其使用者；新增无关的私有代码则不需要。

## 本次验证

2026-09-14 的[独立项目收据](VERIFICATION.json)：**35 个模块、93 项公理报告**通过；其中 35 个模块在本次从源码编译，0 个复用刚刚核验的共享产物。报告只使用普通 Lean 的 `propext`、`Classical.choice`、`Quot.sound` 或其子集；这不是弱 KP 对象理论形式化。
