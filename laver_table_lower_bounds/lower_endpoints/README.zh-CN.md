# 较小端点的 BLP 与 BMS 下界 · [English](README.md)

中文版 PDF：[总览](README.zh-CN.pdf) · [共同入口](endpoints.zh-CN.pdf) · [BLP 证明](blp.zh-CN.pdf) · [BMS 证明](bms.zh-CN.pdf)。

本组整理 2026-11-09 的两条纸面证明，整理日期为 **2026-11-14**。假设 **ZFC + I3**，始终使用同一个生成元 $j$ 的 $\operatorname{Iter}(j)$。这是纸面证明，不是新增的 Lean 认证，也没有把假设降为仅“有限表的某个表项非零”。

令 $J_1=j$、$J_{n+1}=J_n(j)$。嵌入之间的括号表示 application，并从左结合；$\circ$ 才表示普通复合。$\gamma_n$ 是生成临界点的递增枚举，特别有

$$
\kappa_0=\gamma_0,\quad\kappa_1=\gamma_1,\quad
\kappa_2=\gamma_2,\quad\kappa_3=\gamma_4.
$$

定义

$$
\begin{aligned}
\xi&=((J_{11}(J_3))(J_7))(\kappa_2)=\gamma_r,\\
\eta&=((J_{11}(J_3))(J_7))(\gamma_3)=\gamma_s,\\
\Sigma&=J_{13}(\gamma_{16})=\gamma_N,\qquad
\Theta=J_{11}(\kappa_3).
\end{aligned}
$$

两条证明有不同的实际端点，并共同满足

$$
\boxed{J_{11}(\gamma_3)<\xi<\eta<\Sigma<\Theta.}
$$

**普通 BLP**

$r\ge 2^{f(P_{25},8)}$；独立地，$r\ge 2^{\Psi^{\circ4}(8)}$，$\Psi(m)=f(p_{\rm init},m)$

[25 行图案及全部实际行边](blp.zh-CN.md)

**相对 BMS 六类型构造**

$s\ge2^Y$，$Y\ge H_{C[7]}(M)$，$M=\mathcal Q(8)\ge2048$；从而 $s>F_{C[6]}(M-1)+1$，特别 $s>F_{C[6]}(2047)$

[严格上确界、类型接口及数值比较](bms.zh-CN.md)


普通 BLP 的 $P_{25}$ 是四份七行 $p_{\rm init}$ 首尾拼接，行数为 $7+6+6+6$。BMS 结果中的 $C=I[0][2][1]^8$ 使用固定原版 IBLP 的基本列；$C[6]$ 的 24 行与这个 25 行 BLP 不是同一个图案。$C[6]$ 的准确秩按 $\alpha_1=\Lambda=\lim(\mathrm{BMS})$、$\alpha_{n+1}=\Lambda\omega^{\alpha_n}$ 定义，为 $\alpha_6$；函数值的比较依赖指定基本列，不能只凭序型名称替换。

由于 $r<s<N$，两条下界也都给出 $\Sigma$ 的谱索引下界。这里比较的是**自然数谱索引**，不是将不可数临界点与一个巨大自然数直接比较。没有证明两条路线的函数值彼此大小，也没有把 $\eta$ 的 BMS 下界下移到 $\xi$。

建议阅读顺序：

1. [共同入口与严格端点比较](endpoints.zh-CN.md)：完整证明 $\Sigma<\Theta$、新入口的严格截断，以及 $\xi<\eta<\Sigma$。
2. [BLP 证明](blp.zh-CN.md)：四个源嵌入、七行图案的实际 witnesses、25 行拼接及定量定理；末节另列有明确规则版本的标记补全推论。
3. [BMS 证明](bms.zh-CN.md)：在新入口中重做严格上确界控制，给出六个类型环境，接上仓库已有的全对象编译和增长函数比较。

正文明确链接所复用的仓库内引理和公开文献，不需要读者访问原工作机的 scratch 目录。原研究稿、编辑范围及哈希见 [provenance.json](provenance.json)。

仓库已发布的 [$q(5)$ 下界 Lean 工程](../lean/README.zh-CN.md)另有自己的认证范围；本组纸面定理不因此自动成为形式化结果。
