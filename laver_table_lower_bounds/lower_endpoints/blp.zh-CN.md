# 较小端点 $\xi$ 上的完整 BLP 下界 · [English](blp.md)

假设 ZFC + I3，沿用[共同入口](endpoints.zh-CN.md)的全部记号。这里证明普通 25 行 BLP $P_{25}$ 有末点恰为 $\xi$ 的实际实现。因此，若 $\xi=\gamma_r$，

**式 (1)**

$$
\boxed{\begin{gathered}
r\ge2^{f(P_{25},8)},\\
r\ge2^{\Psi^{\circ4}(8)},\qquad\Psi(m)=f(p_{\rm init},m).
\end{gathered}}
$$

两个下界独立成立；不声称 $f(P_{25},8)=\Psi^{\circ4}(8)$。共同入口已经证明

**式 (2)**

$$
\xi=((J_{11}(J_3))(J_7))(\kappa_2)
<\eta<J_{13}(\gamma_{16})<J_{11}(\kappa_3).
$$

普通 BLP、BLS、函数 $f$ 和 linedness 使用 [Qi v5，第 2 节](https://arxiv.org/html/2501.06733v5#S2) 的定义。下面逐行给实际 witnesses，不以图案形状或行数代替实现。

## 1. 更低的四阶段搬运算子

取 $T=J=e(g_2)$、$H=T(j)$，其中 $e=b_0(j)$、$b_0=q(J_7)$。共同入口给出

$$
\operatorname{crit}T=\kappa_1,\qquad
T(\kappa_1)=\mu,\quad T(\mu)=\xi,\quad
T(g)(\kappa_1)=\chi.
$$

因为 $g\equiv_{\kappa_2}j$，

$$
T(g)\equiv_{T(\kappa_2)}H.
$$

严格读取守卫由 $H$ 自身提供：

$$
H(\kappa_1)<H(\mu)=T(\kappa_2).
$$

于是 $H(\kappa_1)=\chi$；另有

**式 (3)**

$$
H(\kappa_0)=\mu,\qquad
H(\mu)=T(\kappa_2),\qquad
H(T(\kappa_2))=T(\kappa_3).
$$

全部后续构造用这个 $T$，其末点 $T(\mu)=\xi<\Sigma$。不使用末点更高的 $q(J_{10})$。

## 2. 四个实际源嵌入

置

$$
\begin{gathered}
D_4=J_{14},\qquad D_{16}=J_{65534},\\
R_0=j,\quad R_1=D_4(j),\quad R_2=D_{16}(j),\quad R_3=D_{16}(R_1).
\end{gathered}
$$

[Dougherty II，Theorem 7.2(c)、Lemma 7.1](https://arxiv.org/pdf/math/9503204) 给出所需有限缩放：

$$
D_4(\gamma_m)=\gamma_{4m}\ (m\le4),\qquad
D_{16}(\gamma_m)=\gamma_{16m}\ (m\le16).
$$

四个临界序列前缀因此为

| $i$ | $R_i$ 的临界序列前缀 |
|---:|---|
| 0 | $\gamma_0\mapsto\gamma_1\mapsto\gamma_2\mapsto\gamma_4$ |
| 1 | $\gamma_0\mapsto\gamma_4\mapsto\gamma_8\mapsto\gamma_{16}$ |
| 2 | $\gamma_0\mapsto\gamma_{16}\mapsto\gamma_{32}\mapsto\gamma_{64}$ |
| 3 | $\gamma_0\mapsto\gamma_{64}\mapsto\gamma_{128}\mapsto\gamma_{256}$ |

令 $s_i=4^i$，并以 $h_i$ 表示 $R_i$ 的谱索引函数。上表给 $h_i(0)=s_i$、$h_i(s_i)=2s_i$；Lemma 7.1 给

$$
2s_i\ge s_i+s_i(h_i(1)-s_i).
$$

严格递增性同时给 $h_i(1)\ge s_i+1$，所以
$R_i(\kappa_1)=\gamma_{s_i+1}$。

还需如下有限商事实：若 $u(\gamma_0)=v(\gamma_0)=\gamma_s$，则
$u\equiv_{\gamma_{s+1}}v$。因为 $\operatorname{crit}(u(j))=\gamma_s$，其在 $P_{s+1}$ 的余数为 $2^s$；右乘生成元是模 $2^{s+1}$ 加一，故 $u$ 的余数为 $2^s-1$，$v$ 同理。此处允许普通复合，因为 [Dougherty II，Theorem 2.6](https://arxiv.org/pdf/math/9503204) 的商对应包括两操作代数 $P_j$。因此

**式 (4)**

$$
R_i\equiv_{\gamma_{s_i+1}}R_{i-1}^{\circ3}\qquad(1\le i\le3).
$$

令 $H_i=T(R_i)$，并定义

$$
\begin{gathered}
a_i=H_i(\kappa_0)=T(\gamma_{s_i}),\qquad b_i=H_i(\kappa_1),\\
c_i=H_i(a_i),\quad d_i=H_i(b_i),\quad e_i=H_i(c_i).
\end{gathered}
$$

于是 $c_i=T(\gamma_{2s_i})$、$e_i=T(\gamma_{4s_i})$，且

$$
\kappa_0<\kappa_1<a_i<b_i<c_i<d_i<e_i.
$$

沿 $T$ 搬运 (4)。守卫
$b_i=H_i(\kappa_1)<H_i(\mu)=T(\gamma_{s_i+1})$
允许严格读取，给出

**式 (5)**

$$
b_i=H_{i-1}^{\circ3}(\kappa_1).
$$

## 3. 每段都具有准确的低桥

置 $G_0=g$，对 $i=0,1,2$ 定义

$$
C_i=H_i(H_i),\qquad G_{i+1}=C_i(C_i(G_i)).
$$

归纳有 $G_i:\kappa_0\mapsto\kappa_1\mapsto a_i\mapsto b_i$。初始情形由 (3) 与共同入口成立。归纳步中，$C_i$ 的临界点为 $a_i$，固定 $\kappa_0,\kappa_1$，并满足

$$
C_i(a_i)=c_i,\quad C_i(b_i)=d_i,\quad C_i(c_i)=e_i,\quad
C_i(d_i)=H_i^{\circ3}(\kappa_1).
$$

两次 application 将低桥送成
$\kappa_0\mapsto\kappa_1\mapsto e_i\mapsto H_i^{\circ3}(\kappa_1)$。
由于 $e_i=a_{i+1}$，(5) 给出所需的下一段。这没有丢失低端点或任何行边。

## 4. 每段七行 $p_{\rm init}$ 的全部 witnesses

固定一段，将点记为 $(\alpha,\beta,a,b,c,d,e)$，嵌入记为 $G,H$。它们满足

$$
G:\alpha\mapsto\beta\mapsto a\mapsto b,\qquad
H:\alpha\mapsto a\mapsto c\mapsto e,\qquad H(\beta)=b,\ H(b)=d.
$$

定义实际 application 项

$$
D=(H(H))(H(G)),\quad E=D(H),\quad F=E(G),\quad L=F(H).
$$

逐次协变给出

$$
\begin{gathered}
D:c\mapsto d\mapsto e,\\
E(\alpha)=a,\ E(\beta)=b,\ E(a)=d,\ E(b)=e,\\
F:a\mapsto b\mapsto d\mapsto e.
\end{gathered}
$$

$F$ 固定 $\alpha,\beta$，故
$L(\alpha)=b$、$L(\beta)=d$、$L(b)=F(c)$、$L(d)=e$。
令 $u=L(a)$、$v=F(c)$，严格单调性给 $d<u<v<e$。

在九点 $(\alpha,\beta,a,b,c,d,u,v,e)$ 上得到：

| 行地址 | 步长 | 实际 owner |
|---|---:|---|
| $(0,1,2)$ | 1 | $G$ |
| $(0,1,2,3)$ | 1 | $G$ |
| $(0,1,2,3,4)$ | 2 | $H$ |
| $(0,1,2,3,4,5)$ | 2 | $H$ |
| $(0,1,2,3,5,6)$ | 3 | $L$ |
| $(0,1,2,3,5,6,7)$ | 3 | $L$ |
| $(0,1,2,3,5,6,7,8)$ | 3 | $L$ |

每个 owner 的临界点都是 $\alpha$；每条行内步长边均由上述点像直接验证。这就是固定的 $p_{\rm init}$，其最后三行共享同一个 $L$。最初三点、末点以及所给 linedness 参数都保留。

## 5. 原样拼接成 25 行

第 $i$ 段采用地址映射

$$
\varphi_i(0)=0,\qquad\varphi_i(1)=1,\qquad
\varphi_i(t)=t+6i\quad(t\ge2).
$$

第一段保留七行，后三段各略去虚拟首行并附加六行。因为 $e_i=a_{i+1}$，所有接缝准确重合；段内新点严格位于该段原有间隙。每行的最后两个地址仍为全局行号及下一点号。由第 4 节的 owners 得到完整 $P_{25}$，其阶段末点如下：

| 完成段数 | 行数 | 实际末点 |
|---:|---:|---|
| 1 | 7 | $T(\gamma_4)$ |
| 2 | 13 | $T(\gamma_{16})$ |
| 3 | 19 | $T(\gamma_{64})$ |
| 4 | 25 | $T(\gamma_{256})=T(\mu)=\xi$ |

初始三点始终为 $(\kappa_0,\kappa_1,\mu)$，带有共同入口构造的实际 8-line。

## 6. 定量下界及后续操作

[Qi，Theorem 2.25](https://arxiv.org/html/2501.06733v5#S2) 将该 BLS 和初始 8-line 送到以 $\xi$ 为终点的 $f(P_{25},8)$-line。临界点计数（同文 Lemma 2.5）给出

$$
\gamma_{\,2^{f(P_{25},8)}}\le\xi=\gamma_r,
$$

即 (1) 的第一项。另一种应用方式是依次对四份 $p_{\rm init}$ 使用同一定理，保留每次得到的首三元组及实际长链，得到 $\Psi^{\circ4}(8)$-line，证明第二项。

在 $\xi$ 的谱索引上写的是 $\ge$；只有再用 $\xi<\Sigma=\gamma_N$ 时才得到 $N>2^{f(P_{25},8)}$ 等严格界。

该定理覆盖普通 BLP 的整个 $f$ 递归，不只是静态初始图案。普通 completion、$M$、$E$ 和删行由 BLS 语义实现，末点保持或降低；无须实际跑完巨大下降。这里尚不自动包含额外的 marked completion。

## 7. 单独的标记补全推论

若使用仓库[有限参数标记 BLP 定量桥](../proofs/output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md)的准确版本，还可得到同一 $\xi$ 上的独立下界。这一版本是：普通行型、短复制、正确的 paper guard、自然截断 mark 语义、从左到右的冻结扫描，以及论文的辅助三点行 $E(m)$。

在每份 $p_{\rm init}$ 的局部行号中，第 4 行标 3，第 6 行标 5，第 7 行标 5 和 6；用同一 $\varphi_i$ 重编号，得到带 16 枚 marks 的 $\widehat P_{25}$。相应局部 trace 为 $(3,1)$、$(5,1)$、$(5,1)$、$(6,2)$，都是一因子、正源、proper trace；carrier 与该唯一因子分别是同一个 $H_i$ 或 $L_i$，故标记语义由实际全局相等成立。

删掉隐含下一点后，把行 core 记为 $A_r$、步长记为 $\ell_r$，设
$p(r)=A_r[-\ell_r-1]$、$e(r)=A_r[-\ell_r]$、$B(r)=A_r[-2]$。
所有 eligible 行所需的 $\operatorname{Sat}$ 条件为 $B(e(r))\le p(r)$。第一行为 $(p,e,B(e))=(0,1,0)$；每段另外三条 eligible 行是局部行 3、5、6，分别有

$$
(p,e,B(e))=(1,\varphi_i(2),1),\quad
(1,\varphi_i(2),1),\quad
(\varphi_i(2),\varphi_i(3),\varphi_i(2)).
$$

全部 13 条均取等。初始 8-line 和全部普通行边不变，故该定量桥的证书假设逐项满足。由其自然截断、平行包和扫描闭包引理，原生及标记补全保持末点，$E(m)$ 保持末点，cut 降低末点。于是其准确函数 $f_\star$ 满足

$$
\boxed{r\ge2^{f_\star(\widehat P_{25},8)}.}
$$

这一推论的全轨道归纳依赖所链接的定量桥及[局部 mark 引理](../common/natural-marks.zh-CN.md)，不是有限证书检查本身。没有断言 $f_\star\ge f$，也没有扩展为任意长行原版 IBLP 的全尾规则。
