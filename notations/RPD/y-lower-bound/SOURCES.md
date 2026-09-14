# Sources and scope / 来源与范围

This optional expander was packaged on 2026-09-14. It is copied from the locally tested annotated RPD deliverable, not substituted for the original RPD implementation.

- Annotated script SHA-256: `0533cfe6c101bb7461361140b7074bdf25c0ee289834ac18c80d834b253a11b4`.
- Unchanged parent RPD script SHA-256: `447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026`.
- The original RPD implementation is embedded without changes to its rules. The additional code computes, verifies, caches and renders display-only Y lower bounds.
- The Y mathematical core is adapted from `1-Y.js` in [hypcos/notation-explorer](https://github.com/hypcos/notation-explorer/blob/51ffbe3e89f5dd5c307d59bb9b70243f6d05962c/1-Y.js), pinned at `51ffbe3e89f5dd5c307d59bb9b70243f6d05962c`. That source credits the FS code to **Naruyoko**. Adaptations use BigInt mathematical values and bounded loops, and remove host UI dependencies. This is not a fresh universal equivalence proof.
- No upstream license file was found in the inspected notation-explorer snapshot. This packaging does not assign that code a new license. Review permissions before public redistribution; see also the repository's [license boundary](../../../SOURCES.md#license-boundary).
- The manuscripts are the comparison research developed for this converter. They are not the private Y/wY source manuscripts, nor additional certified Lean theorems. The BMS source referenced in the first manuscript is an external dependency described by the [Y proof project](../../../lean/Y/README.md); BMS source is not copied here.

文稿复制时保留推导与历史测试记录，仅补充本目录阅读入口，并将 BMS 的机器专用源码路径改为固定公共版本的链接。文稿中的 `.cjs` 名称主要是开发模块或历史探针标识；数学模块已经内联到 JS，历史探针没有全部打包。当前目录可直接运行的检查为 [test.cjs](test.cjs)。

The standalone import, 300 RPD and 360 Y FS comparisons, 220 annotation checks, 700 display checks, actual local NER loader reloads and targeted high-layer cases passed before packaging. The portable test included here exercises this copied artifact without private research dependencies. Neither finite tests nor successful structural certificates prove the general comparison lemmas.
