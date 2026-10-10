# CDMN 研究状态 · [English](README.md)

2026年10月10日。**整个 CDMN 仍未证明良序，也没有已知的标准无穷降链。** 当前展开器采用前缀零项规则，正指标不变。新旧版有限模拟的自审纸面论证给出相同可达域与比较顺序，但一次零项及旧指标证书不能直接互换。

[完整定义](../../notations/CDMN/definition.zh-CN.md) · [NER](../../notations/CDMN/CDMN.ne-rewritten.js) · [Python](../../notations/CDMN/cdmn.py) · [有限性质](../../proofs/paper/cdmn-properties.zh-CN.md) · [来源记录](../../notations/CDMN/provenance.json)

## 当前结果与未决目标

以下 `1=[]` 为一个空列，`W=[0:1]`；紧凑显示的上标是行图，不是普通序数乘方。

| 对象 | 当前状态 |
| --- | --- |
| `S=()(1^(1))` 及自然高度种子 | 自审纸面精确对应：S=lim(BMS)，且h≥1时 `[][0:h]=BMS(0^h)(1^h)` |
| `T=()(1^(1))(1)(3^(1))(3)` | 自审纸面证明：标准域中后裔可以达到任意有限嵌套深度的最小式子 |
| 普通 TBMS 与 T | 在既有 TBMS 端点接口下，全源域嵌入给出 `lim(TBMS) ≤ T`；没有证明在 T 处取等或严格小于 |
| `R∞=()(1^(1))(1)(3^(1))(3^2)(5,3)(6^(1))` | 自审纸面证明覆盖整个实际后裔锥，由标准可达可比覆盖整个标准初段 |
| `A=()(1^(1)())` | 良序性未决；第一个尚未解决的基本项是 `A[2]=()(1^(1))(2^(2))` |
| BTBMS 上界比较 | 有具体标准承载式及前两层全参数公式；整个后裔域嵌入未完成 |

实际支持的关系是
\[
\lim(\mathrm{TBMS})\le T<R_\infty<A[2]<A.
\]
有限 CDMN 式之间用原比较器及实际标准入口；最左侧序数解释依赖源侧接口与完整锥纸面证明。`R∞` 只是局部前沿名，**不是 CDMN 极限**。可安全推出 `lim(TBMS)<R∞`，但不能把截止总结中的含混“严格下界”当成 `lim(TBMS)<T` 的证明。

## 论证入口

- [有限行BMS精确对应与BMS极限](papers/s2-equals-bms.zh-CN.md)给出超出早期单向下界的后续等号。
- [最小无界深度起点与 TBMS 下界](depth-and-tbms.zh-CN.md)分别说明两个独立命题。
- [BTBMS 比较与相邻读取目标](btbms-comparisons.zh-CN.md)给出编码、公式、上界候选和缺失的闭包。
- [证明依赖与标准入口](proof-dependencies.zh-CN.md)列明独立接口。

完整中文良序推导按依赖顺序保存，英文配套均明确标为**节译摘要**：

1. [累积行势与闭合组件](papers/cumulative-row-potential.zh-CN.md)。
2. [隔离算子驱动](papers/separated-operator-driver.zh-CN.md)。
3. [有限类型驱动](papers/finite-type-driver.zh-CN.md)。
4. [一致模板族的新层](papers/polymorphic-family-driver.zh-CN.md)。
5. [任意有限证明族层及共同上端](papers/finite-universe-diagonal.zh-CN.md)。
6. [全族层一致性与混合端口](papers/global-family-mixed-port.zh-CN.md)。

它们是自审纸面证明，**不是 Lean 认证、独立同行终审，也未完成 KP 加存在不可数序数的公理审计**。文稿以通常 ZFC 为足够的环境；这只覆盖已证明的锥，不是整个 CDMN 的公理上界。

## A 为什么仍未证明

令 `W_j=[j:1]`，对所有 \(n\ge0\) 有
\[
A[n]=C_n=[][0:W_0][1:W_1]\cdots[n-1:W_{n-1}],\qquad C_0=[].
\]
C1 已由闭合行反射覆盖。C2 的内层读取非空前列，复制出的行仍引用外部前文，不能直接放进上述已知良序的闭合行库。C2 已能到达 T，因此起始语法深度也不是归纳上界。

与整个 RPD、ARD 系列、SRPD、Y、wY、普通及 strong e0MN、BTBMS 的比较均未完成。失败映射不是相反方向的不等式；原始语法上的保序编码不等于标准域嵌入，必须证明所有像标准。

## 历史反例研究与检查

旧全来源导入、非严格阈值变体有参数化再生链；当前阈值阻止这些具体机制，不是排除所有无穷降链。[插空引理](dilation.zh-CN.md)提供另一充分反例判据，但旧深零项宏与当前前缀零项宏应区分，见其版本说明及[历史实验索引](historical/README.zh-CN.md)。

历史统计保留未知和截断，不冒充本次更新重新运行了全部旧实验。当前包检查为 `python -B tests/cdmn.py`，范围见[有限验收记录](../../tools/cdmn-validation.json)。有限样例、每步字典序下降都不等于良序证明。本目录没有提供整个 CDMN 的 Lean 定理或新增 PDF。
