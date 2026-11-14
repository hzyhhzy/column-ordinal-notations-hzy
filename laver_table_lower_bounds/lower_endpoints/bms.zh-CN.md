# 较小端点 $\eta$ 上的 BMS 塔下界 · [English](bms.md)

假设 ZFC + I3，沿用[共同入口](endpoints.zh-CN.md)。令

$$
\eta=((J_{11}(J_3))(J_7))(\gamma_3)=\gamma_s,\qquad
C=I[0][2][1]^8,
$$

其中 $I$ 及基本列固定为仓库的[原版 IBLP](../code/iblp_original.py)，$[1]^8$ 表示连续八次操作。本篇证明

$$
\boxed{s>F_{C[6]}(M-1)+1,\qquad M=\mathcal Q(8)\ge2048}
\tag{1}
$$

特别有 $s>F_{C[6]}(2047)$、$s>F_C(6)$。$\mathcal Q$ 在第 4 节由快 BMS 算子独立定义，不以 $s$ 为参数。共同入口已证明

$$
\eta<J_{13}(\gamma_{16})<J_{11}(\kappa_3).
\tag{2}
$$

证明复用已有的相对 BMS 编译和全类型数值比较；新端点的实际入口、严格上确界及类型接缝在下面重新核查。只知道一个较高端点有下界，并不足以推出 (1)。

## 1. 在新的低背景中控制上确界

共同入口中的 $q$ 满足

$$
\operatorname{crit}q=\kappa_2,\quad q(\kappa_2)=\mu,\quad
q(\kappa_3)=\chi,\quad q(\mu)=\Sigma.
$$

仍用其 $g,g_i,b_0,e,J,k,x,\delta,\xi$，并令 $T_0=q(J_{10})$。源关系 $J_{10}\equiv_\mu J_8(J_2)$ 沿 $q$ 搬运给

$$
T_0\equiv_\Sigma b_0(g)(g_2).
$$

由 $g\equiv_{\kappa_2}j$，得到 $b_0(g)\equiv_\xi e$，所以 $T_0\equiv_\xi J$。再用 $J_{11}\equiv_\mu j\circ j$，

$$
k=J(g)\equiv_\xi T_0(g)=q(J_{11})\equiv_\Sigma g\circ g.
$$

因此 $k\equiv_\xi g\circ g$。对于 $z<\mu$，$k(z)<k(\mu)=\xi$ 是严格守卫，故

$$
k(z)=g(g(z)),\qquad v:=k(<\mu)=(g\circ g)(<\mu).
\tag{3}
$$

令 $s_1=j(<\kappa_1)$、$s_2=j(<\kappa_2)$。所需源点严格链为

$$
\begin{aligned}
J_7(s_1)&=J_8(<\kappa_3)>J_8(s_2)
=J_9(<\kappa_2)>J_9(s_1)\\
&=J_{10}(<\kappa_2)>J_{10}(s_1)
=J_{11}(<\kappa_2)>J_{11}(s_1).
\end{aligned}
\tag{4}
$$

这些是 [Dougherty I，印刷页 22–24](https://arxiv.org/pdf/math/9205202#page=22) 的小项及上确界关系。$q$ 固定 $s_1$，$e$ 固定 $s_1,\kappa_1,\mu$，所以

$$
g(<\kappa_1)=x(<\kappa_1)=s_1,\quad
x(\kappa_1)=J(\kappa_1)=\mu,\quad
v=J(s_1),\quad J(<\mu)=x(s_1).
$$

因为 $s_1<\mu$ 且 $\mu$ 为极限序数，
$k(s_1)<v=J(s_1)<x(s_1)$。下文 $k^2$ 表示普通复合 $k\circ k$。由 $k\circ J=J\circ g$、$J=x(x)$，以及 $k(s_1)=g^2(s_1)$，有

$$
k^2(v)=J(g^2(s_1))=J(k(s_1))
<J(x(s_1))=x(x(s_1))=e(k(s_1)).
$$

(3)、(4) 又给

$$
k(s_1)=q(J_{11}(s_1))<q(J_7(s_1))=b_0(s_1).
$$

$b_0(s_1)$ 为极限序数，且 $e=b_0(j)$。于是

$$
e(k(s_1))<e(<b_0(s_1))
=b_0(j(<s_1))<b_0(\gamma_3)=\eta.
$$

综上得到关键的严格界

$$
\boxed{k^2(k(<\mu))<\eta.}
\tag{5}
$$

## 2. 全部有限输出共用的严格上界

定义实际 application 项

$$
b=k(g),\quad c=k(b),\quad d=c(k),\quad e_1=d(g),\quad f=e_1(k),
$$
$$
A=c(d),\quad V=c(e_1),\quad Q=A(k),\qquad
t=k(\chi),\quad a=k(\xi),\quad c_{\rm out}=k(t).
$$

LD 及普通复合律给

$$
c=(k\circ k)(g),\quad c^2=(k\circ k)(g\circ g),\quad
c^2(\xi)=a,\quad A=c^2(k).
$$

因此

$$
c^2(<a)=k^2((g\circ g)(<\mu))=k^2(v).
$$

生成临界点 $a$ 是正则基数；$\xi<a=k(\xi)$ 给 $k(<\xi)<a$。在实际像 $a=c^2(\xi)$ 处使用上确界协变，

$$
\boxed{A(<a)=c^2(k(<\xi))<c^2(<a)=k^2(v)<\eta.}
\tag{6}
$$

这是对所有 $z<a$ 的统一控制。没有假设 $A(a)<\Sigma$，也没有把 $q\equiv_\Sigma q_{\rm old}$ 当作全局相等。

## 3. 两条实带及六个类型环境

### 3.1 标量层

将[一般前端插入引理](../proofs/output/iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md)及[低开 fan 构造，第 1–3 节](../proofs/scratch/iblp030-8h-20261015/lift-low-open-fan-and-typed-gap.txt)中的背景
$(j,\kappa_2,\kappa_3,J_{10},J_{11},\gamma_3)$ 换为
$(g,\mu,\chi,J,k,\delta)$。

这里需要的是该引理的一般接口，不是断言 $J$ 是以 $g$ 为生成元的第 10 项。共同入口第 5 节逐项提供
$\operatorname{crit}J=\kappa_1$、$J(\kappa_1)=\mu$、$J(\mu)=\xi$、
$k=J(g)$、$k(\kappa_1)=\chi$ 和 $k\equiv_\delta g_3$，从而支付低 owner 的重建和每次严格截断读取。

实际嵌入 $b(b)(k)$ 把 $(\kappa_0,\kappa_1,\mu)$ 送到 $(\mu,\xi,t)$。给定任意实际 $m$-line，逐次前端插入构造高度 $m+1$ 的开 fan，保留正端口的全部隐含最后边及备用端口；末点 $\le t$，当 $m\ge2$ 时严格小于 $t$。

取整个 fan 的 $f$ 像，再把两条实带的端口 1 下移，得到准确的 BMS 种子

$$
B_m=(0^m)(1^m).
$$

标量实参出口 $\le\chi$，对象输出 $\le a$。每条备用连接均是带实际全局点像的普通复合词；下移后由共同 membership 截断读取全部中间点像，隐含边保持。具体搬运公式由上述低开 fan 第 2–3 节及[备用带证明，第 1–5 节](../proofs/scratch/iblp030-8h-20261015/lift-participating-bms-spare.txt)给出。

这正是[自然相对 BMS 编译引理，第 2–4 节](../proofs/scratch/iblp030-8h-20261015/lift-natural-relative-bms-oracle.txt)的完整入口，提供
$\mathsf S(u)(m)=K_{B_m}^{(0,u)}(m)$ 的全输入、全外环境合同。编译归纳使用 BMS 良序及实际复制树；不为虚拟 oracle 端点虚构 owner。

### 3.2 高类型接缝及最后一个开区间

置

$$
T_*=J(g_3),\qquad\rho=J(\delta),\qquad Z=A(T_*).
$$

由 $g_3\equiv_\delta g\circ g$，沿 $J$ 搬运并用严格输出守卫，有

$$
\begin{gathered}
T_*(\kappa_0)=\xi,\quad T_*(\kappa_1)=t,\quad
T_*(\mu)=\rho,\quad T_*(\xi)=a,\\
\xi<t<\rho<T_*(\chi)<T_*(v)<a.
\end{gathered}
$$

此外
$A:(\kappa_0,\kappa_1,\mu,\chi)\mapsto(\mu,\chi,a,c_{\rm out})$，
$V:\mu\mapsto\chi\mapsto a\mapsto c_{\rm out}$。完整环境表为

| 类型 | 环境 | 辅助源点 | 首实带左端 | 闭输出上界 |
|---:|---|---|---|---|
| 0 | $\mathrm{id}$ | $\mu$ | $\chi$ | $a$ |
| 1 | $V$ | $\chi$ | $a$ | $c_{\rm out}$ |
| 2 | $Q$ | $a$ | $c_{\rm out}$ | $A(\xi)$ |
| 3 | $Q\circ V$ | $c_{\rm out}$ | $A(\xi)$ | $A(t)$ |
| 4 | $Z$ | $A(\xi)$ | $A(t)$ | $A(\rho)$ |
| 5 | $Z\circ V$ | $A(t)$ | $A(\rho)$ | $A(T_*(\chi))$ |
| 6 | $Z\circ Q$ | $A(\rho)$ | $A(T_*(\chi))$ | $\eta$ |

前六行的闭输出均由 (6) 严格小于 $\eta$。最后一行处理每一个实际封口 $C_0<a$：

$$
Q(C_0)<Q(<a)=A(v),\qquad
Z(Q(C_0))<Z(A(v))=A(T_*(v))<\eta.
\tag{7}
$$

没有将普通复合与上确界无条件交换为等号。

每行的辅助点等于前一类型的入口，首实带点等于前一类型的出口。零副本 owner 固定所有更低域坐标，并把当前入口送到更新后的整个对象出口；非零副本 actors 的临界点又高于这些低坐标。因此[全对象相对复制归纳](../proofs/scratch/iblp030-8h-20261015/hardy-root-C7-q5-single-file.txt)第 3、5 节逐层适用。

$g$ 的四点链提供预热 $f_0(m)=m2^m$，故第 $i$ 类型的实载荷为 $B_{m2^m}$。$m2^m\ge2$ 保证所需严格封口，得到 $\mathsf D_i$（$1\le i\le6$）的全部合同。旧稿的高端点已由 (6)、(7) 独立替换；低开 fan 草稿末节曾经未决的类型接缝不是这里的隐藏前提。

## 4. 自然输入及实际谱索引下界

快 BMS 算子 $K_M^{(r,u)}$ 的零下标值为底对象 $u$，后继按最后整数输入 $m$ 迭代 $2^m$ 次，极限采用原 BM4 的 $M[2^m]$；高类型迭代整个低类型对象。准确的有限类型、对角操作及尾序见[类型比较](../proofs/scratch/iblp030-8h-20261015/hardy-root-typed-bms-bound.txt)、[同输入快比较](../proofs/scratch/iblp030-8h-20261015/hardy-root-fast-type1-C3.txt)和[原塔证明，第 1–4 节](../01-blp-tower.zh-CN.md)。

定义

$$
f_0(m)=m2^m,\quad
\mathsf S(u)(m)=K_{B_m}^{(0,u)}(m),\quad
\mathsf D_i(u)(\cdots)(m)=K_{B_{m2^m}}^{(i,u)}(\cdots)(m).
$$

以下应用从左结合：

$$
\begin{aligned}
\mathsf T&=\mathsf D_5(\mathsf D_4)(\mathsf D_3)(\mathsf D_2)(\mathsf D_1),\\
\mathsf W&=\mathsf D_6(\mathsf D_5)(\mathsf D_4)(\mathsf D_3)(\mathsf D_2)(\mathsf D_1),\\
\mathsf U&=\mathsf T(\mathsf T(\mathsf S)),\qquad
\mathcal Q=\mathsf U(\mathsf U(f_0)),\\
M&=\mathcal Q(8),\qquad Y=\mathsf W(\mathsf S)(f_0)(8).
\end{aligned}
\tag{8}
$$

这些自然数不以 $\eta$ 的谱索引为参数。原塔证明的全类型比较给出

$$
\mathsf W(\mathsf S)\ge\mathsf U^4,\qquad
\mathsf U\ge\mathsf S,\qquad
\mathcal Q\ge_3 H_{C[7]}.
\tag{9}
$$

$\ge_3$ 量化所有最终输入至少 3，以及所有适用的低类型实参。它来自安全类的准确 BMS 覆盖、尾局部性与实际种子下降路径，不是由序型大小猜测函数大小。整个对象的四倍余量及传递见[低层数值比较](../proofs/scratch/iblp030-8h-20261015/hardy-root-low-stack-numeric.txt)。

由 $\mathcal Q\ge f_0$，$M\ge f_0(8)=2048$。强前缀增长给

$$
\begin{aligned}
Y&\ge\mathsf U^4(f_0)(8)
\ge\mathsf U(\mathcal Q)(8)
\ge\mathsf S(\mathcal Q)(8)\\
&\ge\mathcal Q(\mathcal Q(8))
=\mathcal Q(M)\ge H_{C[7]}(M).
\end{aligned}
\tag{10}
$$

第 3 节的实际合同将共同入口的 8-line 送到末点不超过 $\eta$ 的实际 $Y$-line。用 [Qi，Lemma 2.5](https://arxiv.org/html/2501.06733v5#S2) 的临界计数，

$$
\boxed{\gamma_{2^Y}\le\eta=\gamma_s<\Sigma,\qquad s\ge2^Y.}
\tag{11}
$$

因此下界已经在 $\eta$ 成立，而不只是借用较宽松的 $\Sigma$。

## 5. 以准确基本列换成 FGH

固定

$$
F_\varnothing(n)=n+1,\quad
F_{P+1}(n)=F_P^{\circ(n+1)}(n),\quad
F_P(n)=F_{P[n]}(n)\quad(P\text{ 非后继}).
$$

Hardy 使用空式值 $n$、后继时自变量加一、非后继时取同输入的原版基本列。记 $A_{\rm I}=I[0][1]$、$h=H_{A_{\rm I}}$。原版第一根代入恒等式给
$H_{C[7]}(y)=G_{C[6]}^h(y)$，其中 $G$ 的后继迭代次数为 $y$。

[跨输入比较，第 2–4 节](../proofs/scratch/iblp-I-to-I0-20261016/port-FGH-existing-bound-C6.txt)对该闭语法类证明

$$
x\ge2,\quad y\ge x+1
\quad\Longrightarrow\quad
G_P^h(y)\ge F_P(x)+1.
\tag{12}
$$

证明同时量化所有 $x,y$：后继步配对两条迭代轨道，保持数值差至少 1；极限步用准确的字面前缀 $P[x]\preceq P[y]$ 及同输入前缀比较。前缀性质包括冻结扫描及 marks；没有假设任意 FGH 或 Hardy 的输入、下标单调性。终止基础来自[原版安全类和第一根闭语法](../PROOF_DEPENDENCIES.zh-CN.md)第 3 节的完整依赖。

在 (12) 分别取 $(x,y)=(M-1,M)$、$(2047,M)$、$(6,M)$，结合 (10)、(11)，得

$$
\boxed{s>F_{C[6]}(M-1)+1,\qquad
s>F_{C[6]}(2047),\qquad
s>F_{C[6]}(6)=F_C(6).}
$$

最后等式只用固定极限规则 $F_C(6)=F_{C[6]}(6)$。

## 6. 秩、依赖及范围

准确的下降树秩为

$$
\alpha_1=\Lambda=\lim(\mathrm{BMS}),\qquad
\alpha_{n+1}=\Lambda\omega^{\alpha_n},\qquad
\operatorname{rank}(C[n])=\alpha_n.
$$

若另用 $\omega^\Lambda=\Lambda$，$\alpha_6$ 可简写为五个 $\Lambda$ 的右结合指数塔。数值结论始终采用上述原版基本列，秩名称本身不承担增长函数比较。

依赖链为：共同入口及 (5)–(7) 的新端点几何 → 已收录的前端插入、备用带与自然相对 BMS 编译 → 已收录的全类型比较与 (12)。各链接所指正文和所需章节已在上文列明；更深的覆盖与森林引理见[仓库依赖索引](../PROOF_DEPENDENCIES.zh-CN.md)第 2–3 节。

本篇没有证明任意类型高度的统一合同、整个 $C$ 在任意输入的下界、原版 $I[0][3][0]$ 的完整 FGH 下界，或把本结果从 $\eta$ 再移到更小的 $\xi$。纸面上确界、全对象归纳和数值比较也不因有限脚本通过而成为 Lean 定理。
