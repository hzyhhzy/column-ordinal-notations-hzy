# 第一组：BLP 实现的有限层 BMS 塔下界

本篇采用 ZFC + I3，固定同一个 $\operatorname{Iter}(j)$。增长函数下标使用原版 IBLP 的准确式子及基本列。原证明中人为指定的固定大输入，在这里统一换成证明内部产生的 $M=\mathcal Q(1)$。

## 1. 准确结果与自然输入

令 $I$ 为所固定原版 IBLP 的初式，取

$$
A=I[0][1],\qquad R=I[0][3][0],\qquad
C=R[0][1]^8=I[0][2][1]^8.
\tag{1}
$$

$[1]^8$ 表示连续八次实际原版 $[1]$。$A$ 的四行 core、步长为

    01:1; 012:1; 0123:2; 234:1.

$C$ 在此后加第五行 $(0,1,5):1$，均无 marks。定义第一根代入

$$
J(P)=A\mathbin{\frown}\varphi(P),\qquad
\varphi(0)=1,\quad\varphi(i)=4+i\ (i>0).
\tag{2}
$$

对所有 $n\ge2$，原规则的字面等式为

$$
C[n]=J^{n-1}(A).
\tag{3}
$$

因此 $C[6]$ 有 24 行，$C[7]$ 有 28 行；它们不是另造的替代记号。

为定义自然输入，先定义快 BMS 的各有限类型算子。$K_M^{(r,u)}$ 的零下标值为底对象 $u$；后继列将较低对象迭代 $2^x$ 次，极限列采用原 BM4 的 $M[2^x]$。$x$ 始终是最后的整数实参。$r=0$ 时对象是数值函数，升一类型后迭代的是整个低类型对象。精确定义、全参数量词和尾序见[类型比较](proofs/scratch/iblp030-8h-20261015/hardy-root-typed-bms-bound.txt)及[尾局部性](proofs/scratch/iblp030-8h-20261015/hardy-root-tail-locality.txt)。

置

$$
f_0(x)=x2^x,\qquad B_h=(0^h)(1^h),
$$
$$
\mathsf S(u)(x)=K_{B_x}^{(0,u)}(x),\qquad
\mathsf D_r(u)(\cdots)(x)=K_{B_{x2^x}}^{(r,u)}(\cdots)(x)
\quad(1\le r\le6).
\tag{4}
$$

以下多元应用一律从左结合：

$$
\mathsf T_*=\mathsf D_5(\mathsf D_4)(\mathsf D_3)(\mathsf D_2)(\mathsf D_1),
$$
$$
\mathsf W=\mathsf D_6(\mathsf D_5)(\mathsf D_4)(\mathsf D_3)(\mathsf D_2)(\mathsf D_1),
$$
$$
\mathsf U=\mathsf T_*(\mathsf T_*(\mathsf S)),\qquad
\mathcal Q=\mathsf U(\mathsf U(f_0)),\qquad
M=\mathcal Q(1),\qquad Y=\mathsf W(\mathsf S)(f_0)(1).
\tag{5}
$$

这些都是有限递归定义，不以 $q(5)$ 为参数。完整证明给出

$$
\boxed{q(5)>2^Y>Y\ge H_{C[7]}(M).}
\tag{6}
$$

并可直接推出

$$
\boxed{q(5)>F_{C[6]}(M-1)+1.}
\tag{7}
$$

这保留了原证明实际产生的输入；无需先挑选一个十进制常数，也无需假设一般原版 Hardy 函数的输入单调性。

## 2. 原版语法与终止基础

在旧安全类 $D$、$A$、冻结零锚串接及 $J$ 生成的有限语法类中，有

$$
J(0)=A,\qquad
J(Q)[n]=J(Q[n])\quad(Q\text{ 非后继}),
$$
$$
J(Q+1)[n]=J(Q)^{\frown n}\quad(n\ge2).
\tag{8}
$$

原版特殊 $[1]$ 则给 $J(Q)\frown1$，不能拿完整复制公式替代。安全类的完整复制和 cut 始终有定义；扫描无有效补全。$J$ 的复制锚点位于前一块的**第一行**，与锚在末行的其他家族不同。

全部子项在这个有限语法类中闭合。用标准 BMS 的覆盖秩、有限串接及 $J$ 的递增指数秩，得到其展开树良基，因而本篇出现的 Hardy、FGH 和类型归纳都有终止基础。

完整输入证明包括[安全类无补全](proofs/output/iblp-01-equality-20260923/IBLP-01-no-completion-proof.zh-CN.md)、[安全类 BMS 上覆盖](proofs/output/iblp-01-equality-20260923/IBLP-01-BMS-upper-bound.zh-CN.md)、[第一根代入恒等式](proofs/scratch/iblp030-8h-20261015/hardy-root-continuation-interface.txt)和[闭语法及下降树秩](proofs/scratch/iblp030-8h-20261015/hardy-root-first-root-tower.txt)。

## 3. 数值比较所需的全类型余量

以 $h=H_A$、$\mathsf B_r(u)=F_A^{(r,u)}$ 记使用原版基本列、后继迭代 $x$ 次的源类型算子。准确代入恒等式给出

$$
H_{C[7]}(x)=
\mathsf B_5(\mathsf B_4)(\mathsf B_3)(\mathsf B_2)(\mathsf B_1)(\mathsf B_0)(h)(x),
\quad x\ge2.
\tag{9}
$$

所有比较量词都覆盖全部底函数、低类型参数及最终输入。记 $\le_3$ 为所有最终输入至少 3 的尾比较。安全类覆盖及 BMS 的明确种子高度下降路径给

$$
\mathsf B_0\le_3\mathsf S^2,\qquad
h\le_3\mathsf S^2(f_0),\qquad
\mathsf B_r\le_3\mathsf D_r\quad(r\ge1).
\tag{10}
$$

这里 $\mathsf S$ 的矩阵高度确为 $x$；没有暗中换成 $x2^x$。第一项通过
$N(x)=2+x(x+1)/2$ 和 $x+2^x-1\ge N(x)+1$ 支付。高类型项使用
$N(x)\le2^x$ 及 $x2^x-1\ge x+2$。所需矩阵路径仅用原指标 0、1、2。

每个 $\mathsf D_r$ 对所有正输入和整个低类型对象满足

$$
\mathsf D_r(u)\ge u^4.
\tag{11}
$$

证明是将相关 BMS 种子降至两个零列；每个零列至少把低类型对象迭代两次。反复把 (11) 传过整个左结合链，得到

$$
\mathsf W\ge\mathsf T_*^4,\qquad
\mathcal Q\ge_3 H_{C[7]},\qquad
\mathsf W(\mathsf S)\ge\mathsf U^4.
\tag{12}
$$

每次传递先对整个函数对象证明，再代入具体实参；不能只使用一个点上的函数值不等式。

## 4. 自然输入确实被支付

快 BMS 算子在小输入处也全定义。原 $B_1[1]$ 恰为两个零列，因此

$$
\mathsf S(f_0)(1)\ge f_0^{\circ256}(8)>3.
$$

由 $\mathcal Q\ge\mathsf S(f_0)$ 得 $M\ge3$。使用 (12) 和快算子的强前缀增长，

$$
\begin{aligned}
Y
&\ge\mathsf U^4(f_0)(1)
\ge\mathsf U^3(f_0)(1)\\
&=\mathsf U(\mathcal Q)(1)
\ge\mathsf S(\mathcal Q)(1)
\ge\mathcal Q(\mathcal Q(1))\\
&=\mathcal Q(M)\ge H_{C[7]}(M).
\end{aligned}
\tag{13}
$$

只有最后一步调用尾比较，所用输入是实际产生的 $M\ge3$。不需在小输入处把原版源函数作为实际语义程序调用。

## 5. 六层算子的实际几何

这部分将 (13) 接回 $q(5)$。详细代数在[C7 合成证明](proofs/scratch/iblp030-8h-20261015/hardy-root-C7-q5-single-file.txt)第 3–5 节；本篇使用它们，下面列出全部关键端点条件。

取 $K=j_{(11)}$，以及 application 项

$$
b=K(j),\quad c=K(b),\quad d=c(K),\quad
e=d(j),\quad f=e(K),\quad A_*=c(d),\quad V=c(e),\quad Q=A_*(K).
$$

令 $\mu=K(\kappa_2)$、$\theta_5=K(\kappa_3)$、$a=K(\mu)$、
$c_{\rm out}=K(\theta_5)$、$\theta_8=j_{(9)}(\kappa_3)$。有

$$
\kappa_3<\mu<\theta_5<a<c_{\rm out}<\theta_8<\kappa_4.
$$

低开 fan 由 $K,j_{(3)}$ 初始化，逐段前端插入，所有正端口的隐含最后一条边及两个备用连接都保留。传送后保留一条备用带，把两条实带的端口 1 下移，得到实际高度恰为 $x$ 的 $\mathsf S$ 合同。

令 $T_*=j_{(10)}(j_{(3)})$、$Z=A_*(T_*)$。六个高类型环境为

| 层 | 环境 | 辅助入口 | 闭输出上界 |
|---:|---|---|---|
| 1 | $V$ | $\kappa_3$ | $c_{\rm out}$ |
| 2 | $Q$ | $a$ | $A_*(\mu)$ |
| 3 | $Q\circ V$ | $c_{\rm out}$ | $A_*(\theta_5)$ |
| 4 | $Z$ | $A_*(\mu)$ | $A_*(T_*(\kappa_2))$ |
| 5 | $Z\circ V$ | $A_*(\theta_5)$ | $A_*(T_*(\kappa_3))$ |
| 6 | $Z\circ Q$ | $A_*(T_*(\kappa_2))$ | $\theta_8$ |

每层辅助入口正好是上一层的实参入口，每层首 payload 点是上一层输出。因此后继复制的 owner 固定所有更低域坐标，同时把当前入口送到上一整对象的输出。非零副本 actors 的临界点又高于这些坐标；所有类型应用都具备实际入口合同。

最后一层只读取严格开区间。完整证明用

$$
A_*(<a)<\theta_8,\qquad
(Z\circ Q)(<a)\le Z(Q(<a))<\theta_8,
\tag{14}
$$

不把普通复合与上确界交换成等号，也不声称 $A_*(a)<\kappa_4$。

于是仅将实际初始一段链输入 $\mathsf W(\mathsf S)(f_0)$，便得到端点低于 $\theta_8<\kappa_4$ 的实际 $Y$-line。$\mathsf U,\mathcal Q$ 只用于数值比较，无须另行把它们塞入几何合同。共同临界计数给 $q(5)>2^Y$，与 (13) 合并得到 (6)。

相对 BMS 编译使用已知 BMS 良序上的归纳和实际复制树；不需要给 oracle 的虚拟端点伪造 owner。[自然相对 BMS 引理，第 4 节](proofs/scratch/iblp030-8h-20261015/lift-natural-relative-bms-oracle.txt)

## 6. Hardy 到标准后继约定 FGH：自然地牺牲一层

对这个闭语法类和任意 $x\ge2$，$y\ge x+1$，令 $G^h$ 使用底函数 $h=H_A$、后继迭代 $y$ 次的递归，则

$$
G_Q^h(y)\ge F_Q(x)+1.
\tag{15}
$$

证明按 $Q$ 良基归纳，同时量化全部 $x,y$。先证明 $G_Q^h$ 增值和同输入的字面前缀单调性。后继步把两条迭代轨道逐次配对，保持数值差至少 1；目标至少有 $x+1$ 次迭代。极限步使用准确的字面前缀关系
$Q[x]\preceq Q[y]$，然后对子项用归纳。这里包括 marks 及冻结扫描的前缀交换，没有假设任意序数下标单调性。

由第一根恒等式

$$
H_{C[7]}(M)=G_{C[6]}^h(M),
$$

在 (15) 取 $x=M-1,y=M$ 即得 (7)。[完整逐项证明](proofs/scratch/iblp-I-to-I0-20261016/port-FGH-existing-bound-C6.txt)第 2–4 节给出这一普遍引理，本篇重新给出其自然输入应用。

## 7. “几层 BMS 指数塔”的准确含义

定义

$$
\alpha_1=\Lambda,\qquad\alpha_{n+1}=\Lambda\cdot\omega^{\alpha_n}.
$$

闭语法的准确下降树秩为 $\operatorname{rank}(C[n])=\alpha_n$。所以 (6)、(7) 分别是 $\alpha_7$ 的 Hardy 界和 $\alpha_6$ 的 FGH 界；数值结论由前面的语法和几何证明得到。

若另外使用 $\omega^\Lambda=\Lambda$，则 $\alpha_2=\Lambda^2$、
$\alpha_3=\Lambda^\Lambda$，$\alpha_6$ 可化成五个 $\Lambda$ 的右结合塔，$\alpha_7$ 化成六个。这是有明确闭包前提的简写；本篇无条件使用 $\alpha_n$ 递推。

整个 $C$ 的下降树秩是严格大于 $\Lambda$ 的最小 epsilon 数。有限层结果没有证明 $H_C(M)$ 或 $F_C(M)$；但由同一跨输入引理，$q(5)>F_{C[6]}(6)=F_C(6)$ 是合法的小输入推论。不得把这个 epsilon 数自动写成 $\varepsilon_{\Lambda+1}$，除非另证 $\Lambda=\varepsilon_\Lambda$。

## 8. 本组依赖什么

本组使用普通 BLP 的实际 E／短复制／端点修补和相对 BMS 编译思想，加上六个明确的类型环境；源增长函数是原版 IBLP 的有限层第一根家族。它不以“从 $R$ 不断 modify 的次数”作为结论。

完整依赖、所用章节、历史草稿与当前接口的区别见[依赖索引](PROOF_DEPENDENCIES.zh-CN.md)。所有源数学稿都已随目录收录；未决的整个 $R$ 比较、曾撤回的初始化和仅属候选的段落均不作为前提。
