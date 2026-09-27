# 归档运行依赖：来源与许可边界 · [English](README.md)

这些是复现 SRPD／普通 TBMS 研究所需的最小上游快照，不是本仓库原创代码，也不随本仓库自动重新许可。逐文件哈希见[完整清单](../manifest.json)。

## NER 的普通 TBMS

来自 [SmileLee-lyx/ne-rewritten](https://github.com/SmileLee-lyx/ne-rewritten)，固定提交 `c539d8f68c5553da2d681c1251ea443b6b735e62`：

- [TBM.ts](ne-rewritten/src/notations/BM-like/TBM.ts)：普通 TBMS 原生规则，默认基本列。
- [utils.ts](ne-rewritten/src/utils.ts) 与 [notation_utils.ts](ne-rewritten/src/notations/notation_utils.ts)：运行依赖。

`compiled/` 的三个 CommonJS 文本由 TypeScript **6.0.3**、目标 ES2023 编译上述相应源码。它们是固定的可读文本，不是二进制文件，不需要读者安装 TypeScript。加载器仍使用原有 VM 时限，不改变基本列算法。

## 其他原始实现

- [hypcos/1-Y.js](hypcos/1-Y.js)：来自 [hypcos/notation-explorer](https://github.com/hypcos/notation-explorer)，提交 `51ffbe3e89f5dd5c307d59bb9b70243f6d05962c`；保留源码中的 Naruyoko 等作者信息。最终模拟器的导入闭包中仍有 Y 相关辅助器读取此快照；没有据此加入另一条 Y 比较路线。
普通 e0MN 的运行适配器在 `output/e0mn-counting-20260917/`，保留 `@test_alpha0` 署名。不是 strong e0MN；本目录不重复收录未被调用的原始 UI 版本，也不收录只供旁支测试使用的 BMS 模块。

## 许可边界

本次整理记录来源和作者，但**没有据此建立第三方代码的再分发许可**；署名、可访问的源码和哈希本身不等于许可。第三方文件不被本仓库的原创文件许可覆盖。公开再分发前仍需确认上游许可或授权；本次只整理本地仓库，没有执行提交或推送。

数学论证与这些运行快照的边界见[档案导读](../README.zh-CN.md)。
