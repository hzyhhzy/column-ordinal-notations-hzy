# 较低临界点的 Lean 证明与未完成范围 · [English](README.md)

**本扩展已完成的 BMS 下界在 $\kappa^{11}_3$。更低端点 $\eta$ 的 BMS 塔下界尚未形式化。** 本目录同时保存完整结果和通往更低端点的已验证入口，二者不混称为同一个定理。

## 已完成的 BMS 下界

记 $\Lambda=\lim(\mathrm{BMS})$。[K11Bound.lean](K11Bound.lean) 证明：在普通二元 Laver 表族中，

$$
A_m(11,16)\ne0\quad\Longrightarrow\quad
F_{\Lambda+1}(120)\downarrow\ \land
F_{\Lambda+1}(120)<v_2(A_m(11,16))<m.
$$

采用模 $2^m$ 的编号，零代表通常编号中的 $2^m$。截断赋值在零处为 $m$。因为结论严格小于 $m$，实际使用的是未饱和值。临界点解释下，这是 $\kappa^{11}_3=j_{(11)}(\gamma_4)$ 的自然数下标。

最终定理只要求指定表项自身非零，不要求首行周期达到 32。还证明该下标一旦存在就在所有更高阶表中保持不变，并得到无条件析取：下标不存在，或者它大于 $F_{\Lambda+1}(120)$。

```lean
theorem k11_undefined_or_large (family : BinaryFamily) :
    (¬ ∃ r, K11Index family r) ∨
      ∃ r y, K11Index family r ∧
        NumericBMS.FiniteLevelEval 1 120 y ∧ y < r
```

`FiniteLevelEval` 是[原数值 BM4 的有限求值关系](../lean/LaverLowerBounds/NumericFGH.lean)，采用 $F_0(x)=x+1$、后继迭代 $x+1$ 次，以及 $\Lambda[x]$ 为 $x+1$ 行两列种子的约定。存在量词包含实际终止见证。

证明从 [252 段实际链](K11/Entrance.lean) 出发，用 [131 段初始化](K11/Bootstrap.lean)，再用 [121 段反馈](K11/Feedback.lean) 实现 $F_\Lambda$ 的 121 次迭代。[数值预算](K11/Counting.lean) 为

$$
\rho(x)=x+4+\lfloor\log_2(x+8)\rfloor,
\qquad \rho(120)=131.
$$

每轮反馈取得真实求值 $y=F_\Lambda(x)$，并重新生成足够容纳 $\rho(y)$ 行的相容组；[最终组合](K11/Successor.lean) 没有假设一个抽象总 FGH 或未经证明的增长估计。

## 更低端点已经验证的部分

定义

$$
\eta=\bigl((j_{(11)}(j_{(3)}))(j_{(7)})\bigr)(\gamma_3).
$$

嵌入之间的括号表示 application，向左结合。在有限表中，它对应

$$
\operatorname{act}_m\bigl((11*_m3)*_m7,3\bigr),
\qquad\operatorname{act}_m(a,x)=v_2(A_m(a,2^x)).
$$

[Word.lean](LowerEndpoint/Word.lean) 对任意有限 application 表达式证明了投影相容性、未饱和下标的稳定性，以及稳定下标的唯一性；稳定性不要求表达式的表元素编码在不同阶数保持相同。

[Entrance.lean](LowerEndpoint/Entrance.lean) 从真实表运算构造压缩低层背景，证明 $q(5)$ 存在时 $\eta$ 的有限稳定下标存在，并验证以下临界点链的有限下标版本：

$$
\eta<\kappa^{11}_3<\kappa^{10}_3<\kappa^9_3<\kappa_4,
\qquad\kappa_4=\gamma_{q(5)-1}.
$$

这里没有另外定义 `c11`、`c10`、`c9`；Lean 的精确陈述直接使用相应 `act` 值。关于 $\kappa,\gamma$ 的集合论解释沿用已有文献；机器验证的对象是明确的有限表量。

## 尚未完成

纸面更强目标为 $\eta=\gamma_r$ 时 $r>F_{C[6]}(2047)$，其中 $C=I[0][2][1]^8$ 使用[纸面塔证明](../01-blp-tower.zh-CN.md)固定的原版 IBLP 基本列。这不等于已经完成的 $\kappa^{11}_3$ 下界。

仍缺两个关键部分：

1. 纸面严格上确界控制 $A(<a)<\eta$ 的语义及有限表替代证明。原文用到非临界上确界、application 对上确界的搬运和生成临界基数的正则性。较高端点的有限表下界不能直接把名字换成 $\eta$。
2. 带全部参数和外环境量词的六类型相对 BMS 编译，以及原版 $C[6]$ 的准确有限 FGH 求值比较。

本目录没有把这两条结论当作公理或最终定理前提，也没有把 $\eta<j_{(13)}(\gamma_{16})$ 宣称为已形式化。更低端点的完整 BMS 下界仍待完成；文稿中的相应“已形式化”句子尚不能启用。

## 编译与范围

从本目录执行：

```sh
python -B build.py --lean-bin /path/to/lean/bin --record
```

固定 Lean 4.33.1。脚本从源码重新编译本目录及共享 [lean](../lean/README.zh-CN.md) 的完整导入闭包，产物只写本目录 `.build`；每个编译进程单线程、最多 2048 MB、60 秒。超过时限会结束该进程。通过后生成[验证收据](verification/VERIFICATION.json)和[完整日志](verification/build.txt)，收据同时列出已验证及未验证范围。

这是 Lean 通常基础中的有限组合论形式化；没有 I3 或全体 BMS 良序性前提，没有对象语言 ZFC 推导树或 I3 嵌入模型的实现。最终公理审计只允许 `propext`、`Classical.choice`、`Quot.sound`。

K11 源码来自 2026-11-09 已完成的本地证明，本次新增 $\eta$ 入口和稳定性证明。来源及 LF 规范化哈希见 [PROVENANCE.json](PROVENANCE.json)。本目录独立构建，不改动原来 $q(5)>F_{\Lambda+\omega+1}(3)$ 的工程或验证收据。
