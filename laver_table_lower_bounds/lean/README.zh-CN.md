# Lean：q(5) 的条件 BMS 下界 · [English](README.md)

本独立 Lean 4.33.1 项目证明

$$
q(5)\downarrow\ \Longrightarrow\ q(5)>F_{\Lambda+\omega+1}(3),
\qquad \Lambda=\lim(\mathrm{BMS}).
$$

最终定理采用**原数值版 BM4 规则**，其与父表坐标的任意指标逐步对应已经证明。结论同时给出实际 FGH 求值终止的见证，且求值结果唯一。

## 精确陈述与约定

入口 [`q5_original_bms_bound`](LaverLowerBounds/OriginalBMSBound.lean)：

```lean
theorem q5_original_bms_bound (family : BinaryFamily) (m : Nat)
    (hm : Q5At family m) :
    ∃ y, NumericBMS.OmegaSuccessorEval 3 y ∧ y < m
```

- `BinaryFamily` 给出每个 `n` 上大小为 `2^n` 的表，仅要求左自分配律及 `a * 1 = a + 1`（模表大小）。周期、投影、截断作用等性质都是推导结论。
- `Q5At family m` 表示首行周期首次达到至少 `32` 的**阶参数**为 `m`。更强的 [`threshold_original_bms_bound`](LaverLowerBounds/OriginalBMSBound.lean) 只要求第 `m` 阶达到该周期阈值，不要求最小性。
- 数值 BM4 定义见 [`Reference.lean`](YesMetaZFC/BMS/Reference.lean)。`A[0]` 删除末列，正指标 `n` 在保留前缀后添加 `n` 个复制块，再裁掉全零底行。
- `F_0(x)=x+1`；后继阶段迭代前驱函数 `x+1` 次；极限阶段取基本列第 `x` 项。
- `Lambda[x]` 为 `x+1` 行种子 `(0…0)(1…1)`；`(Lambda+omega)[x]=Lambda+(x+1)`。

`OmegaSuccessorEval` 是由这些递归规则归纳定义的**实际有限求值关系**。存在量词同时给出该周期条件下的求值结果和终止性；并未任意指定一个满足增长条件的总函数。

## 公理与形式化范围

最终定理的 Lean 公理审计结果恰为：

```text
[propext, Classical.choice, Quot.sound]
```

最终定理没有自定义公理、`sorry`、`native_decide`、I3 假设、全体 BMS 良序性假设或尚未证明的计数／比较接口。本项目不证明 I3 推出 `q(5)` 存在，也不另行构造所有有限 Laver table；结论量化任意满足定义方程的 `BinaryFamily`。

这是 **Lean 通常基础下的直接数学证明**，**没有另行编码 ZFC 对象语言并构造 ZFC 句法推导树**。预期的 ZFC 数学论证使用自然数、有限表／列表及经典集合构造，但这一步元理论翻译不在机器认证范围内。导入的 `YesMetaZFC` 命名空间在此仅提供有限 BM4 组合论模块，不代表内部 ZFC 证明证书。

本定理输入为 **3**，序数层级为 `Lambda+omega+1`。[纸面证明集](../README.zh-CN.md)中的更大输入、指数塔及 IBLP 结论不在此次 Lean 认证范围内。

## 证明结构

1. [`FiniteTable`](LaverLowerBounds/FiniteTable.lean)、[`FinitePeriods`](LaverLowerBounds/FinitePeriods.lean)、[`Signature`](LaverLowerBounds/Signature.lean) 及 [`FiniteCapped`](LaverLowerBounds/FiniteCapped.lean) 从普通表定义推出有限代数性质。`LowProducts` 中的有限 `A_9` 乘积证书由内核规约检查。
2. [`finite_feedback_stops`](LaverLowerBounds/FiniteFeedbackBudget.lean) 构造一个具体三列父表的实际固定 `[1]` 终止下降，其次数小于 `m`。饱和端点不会被误用为未饱和的严格增长点。
3. 祖先覆盖、行数与宽度交换、`W` 及 `Sigma` 将变指标 FGH 求值编译为有限下降预算。[`triple_realizes_fgh`](LaverLowerBounds/DiagonalFGH.lean) 同时证明实际求值存在及指数形式的计数下界。
4. [`Numerical`](LaverLowerBounds/Numerical.lean) 和 [`UpperHierarchyEvaluation`](LaverLowerBounds/UpperHierarchyEvaluation.lean) 组织后继迭代、对角化及最终后继阶段，得到 [`threshold_fgh_bound`](LaverLowerBounds/FiniteFGHBound.lean)。
5. [`NumericCopyParents`](LaverLowerBounds/NumericCopyParents.lean) 从 Hunter 祖先复制引理推出直接父指针的精确公式。[`encode_expand`](LaverLowerBounds/NumericExpansionFidelity.lean) 对**所有合法数值矩阵、所有展开指标**证明 `encode(A[n]) = encode(A)[n]`，包括全零行裁剪。[`NumericSeedsAndKinds`](LaverLowerBounds/NumericSeedsAndKinds.lean) 与 [`NumericFGH`](LaverLowerBounds/NumericFGH.lean) 完成种子、后继／极限判定及有限 FGH 求值的双向传递。

两个辅助计数函数在终止域外设有明确的默认值。每个有限表应用都提供真实终止见证，最终求值中的每个底层 FGH 调用也都取得真实见证。因此最终结论不依赖默认值所代表的虚假求值。

## 重编译

安装 `lean-toolchain` 固定的工具链，然后从本目录执行：

```sh
python -B build.py --record
```

也可通过 `--lean-bin /path/to/lean/bin` 指定工具链。Windows 的 `build.ps1` 包装同一命令，支持 `-LeanBin`、`-Python` 和 `-Record`。工程亦配置了标准 `lake build`；收录的验证记录采用上述有资源限制的审计命令。

编译器只依赖 Python 标准库及 Lean/Std。脚本按 import 顺序完整重编译，逐模块限定**一个线程、2048 MB、60 秒**，超时结束它自己的进程树；检查 Lean 版本、编译期间源码一致性、占位证明及最终定理的公理输出。不计算巨大层级函数，不构造巨大 Laver 表。

[验证收据](verification/VERIFICATION.json) 用 LF 规范化 SHA-256 固定每个实际编译模块，[完整日志](verification/build.txt) 记录 **152 个模块**的重新编译。`.build/`、`.lake/` 为不进入 Git 的本地缓存。`generate_low_data.py` 是可选的有限证明源码生成器，生成的等式仍须由 Lean 内核检查。

## 来源

数学 Lean 文件与已完成的研究快照一致，仅规范化了换行。[PROVENANCE.json](PROVENANCE.json) 记录原文件和发布文件的哈希；八个数值 BM4 依赖模块及上游作者来源见 [VENDORED.zh-CN.md](YesMetaZFC/VENDORED.zh-CN.md)。未导入上游抽象良序／集合论接口。
