# BTnSS 的固定行数 BMS 上界 · [English](README.md)

本次收录的纸面证明对每个有限 $n\ge2$，将 **strong BT*(-1)Y-nSS v2 的整个标准域**保序嵌入一个固定标准 BMS 节点以下。记

$$
B_r=(0^r)(1^r),\qquad U_r=(0^r)(1^r)(2^r)(3^r),
$$

则

$$
\boxed{\lim(\mathrm{BTnSS})\le |U_{n+1}|<|B_{n+2}|.}
$$

右端 $|B_{n+2}|$ 是**标准 $(n+1)$ 行 BMS 的上确界**。中间的固定界 $U_{n+1}=B_{n+2}[3]$ 采用冻结的短基本列，不随源种子、嵌套深度或项大小改变。

这是完成接合并经自审的**纸面证明，尚未 Lean 形式化，也不是独立审稿认证**。没有声称等号、像为初段或逐指标交换基本列。论证使用 BTnSS 的有限不变量与 Hunter 的 BMS 良序定理，不以旧 BTnSS 的 I3／almost 2-huge 模型解释为前提；这里不主张最小公理体系。

## 阅读顺序

- [中文主证明](upper-bound.zh-CN.md) · [完整英文主证明](upper-bound.md)。
- [冻结定义与标准域有限不变量](source-finite/definitions-and-invariants.zh-CN.md)：摘录旧 BTnSS 主文第1至3节，配套18份有限组合引理；后续模型论部分不收入。
- [省略所属绑定的上下文编码](lemmas/context-encoder.zh-CN.md)：有限性、精确父表、固定入口保序、中间行运输。
- [所属入口键下降](lemmas/owner-entry.zh-CN.md)、[部分变基的键比较](lemmas/partial-key-comparison.zh-CN.md)。
- [跨叶延拓](lemmas/cross-leaf.zh-CN.md)、[最高两行的块运输](lemmas/top-row-transport.zh-CN.md)、[首对角引理](lemmas/first-diagonal.zh-CN.md)。

主证明与总览为中英双语；配套引理完整保留中文论证，没有把英文导读冒充全部引理的译文。局部稿中“本篇尚未证明某一步”等表述仅说明该引理的范围，总体接合以主证明为准。

## 行数与非标准式的区别

源的数值维数为 $d=n-1$，编码使用 $d+2=n+1$ 行。例如

$$
\lim(\mathrm{BT3SS})\le |(0000)(1111)(2222)(3333)|<|(00000)(11111)|.
$$

首列为零的数值合法 $r$ 行矩阵，补零后在裸字典序上小于 $B_{r+1}$，但这**不自动给它赋予该界以下的序数**。原始合法矩阵的字典序甚至含有

$$
(0)(1)>_{\mathrm{lex}}(0)(0)(1)>_{\mathrm{lex}}(0)(0)(0)(1)>_{\mathrm{lex}}\cdots.
$$

这不是声称存在基本列展开降链。对本次编码的像，证明另外建立全部有限块条件，再由有限覆盖及标准 BMS 良序性推出目标标准性，不能用“只有固定行数”跳过这一环节。

## 来源、检验及收录边界

规则固定在 NER 提交 `c539d8f68c5553da2d681c1251ea443b6b735e62`：

- [strong BT*(-1)Y-nSS v2](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/Minus1_Y_nSS-series/BT_star_Minus1_Y_nSS-v2.ts)。
- [BMS 源文件及默认 BM4 短基本列](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/BM.ts)。
- Rachel Hunter，[《Well-Orderedness of the Bashicu Matrix System》](https://arxiv.org/abs/2307.04606)，提供目标 BMS 的良序定理。

[收录清单](MANIFEST.json)记录来源与收录后的哈希、主文摘录行范围、编辑项目及冻结规则哈希。此次导入26份数学文稿和一份仅统一为 LF 换行的[历史有限核验记录](verification.json)。不收录私人 PDF、上游实现及旧实验脚本，不新增展开器或 Lean 项目。文中的实验脚本名、收据内原有的 `repository_changes` 字段均描述当时研究状态，不是这次发布状态。

核验记录区分真实标准路径样本、原始数值样本与原始有限条件样本，保留逐项上限及一次超时退出的范围；不同批次有重叠。它们用于寻找实现错误，不能代替全称证明。可从仓库根目录运行：

```sh
node research/btnss-bms/tools/validate.cjs
```

这只验证收录文件、链接、哈希及记录一致性，不是数学证明检查器。附带收录脚本需要显式传入原工作区，只供来源复核；阅读和验证新克隆的仓库不依赖原工作区。
