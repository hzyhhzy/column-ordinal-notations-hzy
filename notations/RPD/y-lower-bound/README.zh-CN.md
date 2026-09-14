# RPD：附 Y 山脉下界 · [English](README.md)

[NER 单文件展开器](RPD-with-Y-bound.ne-rewritten.js) 在 RPD 主式后附加
`≥ Y【山脉】`，不改变原来的基本列、比较、表达式标识或六种等价显示。
[原 RPD 展开器](../RPD-mountain.ne-rewritten.js) 保留不动；本目录是可选附注版。

## 使用

将整份 JS 导入 ne-rewritten 的“自定义记号”。注册名称为
**RPD（附 Y 山脉下界）**，ID 为 `rpd-with-y-lower-bound-v1`，与原 RPD 不同，
因此可以并存。若已经安装同 ID 的旧附注版，替换旧脚本即可，不要重复启用。

选择 HTML 显示时，附注画完整的 Y 山脉；纯文本和 LaTeX 模式使用完整的
按列父关系列表。原生“显示图表”仍画 RPD 自己的图。脚本无需构建、联网或
另装模块；附注超限不影响主式继续展开。

当前标准 RPD `11248` 可自动得到 Y 下界 `125354`，一些高层结构也可得到
以14、15或更高数字开头的下界。程序先搜索，再独立复验有限结构证书，
最后重画真正的 Y 山脉；不会把未经核验的候选直接标成下界。

不等式比较原展开关系的良基秩。附注允许合法非标准词，不保证等值或最紧。
新增比较论证仍是纸面版本，**没有端到端 Lean 形式化**；证书复验与有限测试
都不能替代一般引理的证明。尤其没有声称已证明 `Y14≤RPD11248`。

## 算法与推导

先读[算法说明](algorithm.zh-CN.md)，其中给出图格式、动态规划、证书规则、
候选比较、浏览器预算及可复现例子。进一步推导按以下顺序阅读：

1. [BMS 种子的直接父表桥](BMS-SEED-LOWER-BOUND.zh-CN.md)：固定 RPD 项的 β 下界，不借用 `11242=Y13` 的猜测等号。
2. [受保护代入与加权 BMS](PROTECTED-SUBSTITUTION.zh-CN.md)：任意高内部参数以及 F/K 的早期下界。
3. [不限提取层的 Y 骨架编译](GENERAL-PROTECTED-Y-COMPILER.zh-CN.md)：外部骨架也可具有高层结构。
4. [坐标伸缩与 Star/K 加强](DILATION-AND-STAR-BOUNDS.zh-CN.md)：当前 `11248≥Y125354` 的纸面论证。
5. [有间隙的高层几何链](DILATED-GEOMETRIC-Y.zh-CN.md)：自动识别和同族候选的确定比较。

基础的 V/F、控制边暴露与逐边模拟还可参阅仓库中的
[Y≤RPD 比较研究稿](../../../research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/Y-le-RPD-proof.zh-CN.md)。
这些研究说明与[已验证的 RPD 良序定理](../../../lean/RPD/README.zh-CN.md)是不同层面的成果。

文稿保留历史探针的名称及结果；那些实验脚本没有全部随本目录分发，不应
把其文件名当成本目录下可以直接运行的命令。实际算法模块已经内联于 JS。
[来源说明](SOURCES.md)记录出处和许可证边界，不包含私人稿件或机器缓存。

## 本目录的离线检查

在仓库根目录运行：

```sh
node --max-old-space-size=256 notations/RPD/y-lower-bound/test.cjs
```

检查只读本目录展开器和上一级原展开器；不联网，不修改 NER 设置，也不
构建 Lean。覆盖注册、原规则保持、新下界、完整 SVG、复制回输与超限回退。
