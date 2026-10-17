# 标记阶段的保端点前缀重定位

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。目标是先利用标记和补全积累足够强的有限结构，再切换到较简单的无标记规则。下面证明一种可以严格保住 Laver 周期端点的参数放大操作，并给出从标准根实际到达的有限证书。它产生的是很大的 **linedness 参数**，尚未证明产生相同行数的 BMS 种子，不能视为 BMS[10] 下界已经完成。

全篇使用同一个 I3 嵌入 $j$，全部嵌入和所有 linedness 见证均属于同一个 $\operatorname{Iter}(j)$。标记证书类 $\mathcal C$、自然截断和 Sat 条件沿用[有限参数定量桥](<marked-BLP-quantitative-transfer.zh-CN.md>)。完整行包括隐含末端；core 不包括它。

## 一般重定位引理

设 $P\in\mathcal C$ 有 $n$ 行，最后完整行为

$$
s_n=(0,1,2,a,n,n+1),\qquad \ell_n=2,\qquad 3\le a<n.
\tag{1}
$$

这是普通 BLP 的长行，不是步长 3 的 limit 行。设最后 owner 为 $J$，全局最后基数为 $\Theta=\theta_{n+1}$，并令

$$
q=p.\mathrm{del}.
$$

假设已经有同一个 $\operatorname{Iter}(j)$ 内的见证，说明

$$
(\theta_0,\theta_1,\theta_a)\quad\text{是 }M\text{-lined}.
\tag{2}
$$

**引理。** 存在 $R\in\mathcal C$，其字面模式恰好为 $q$，且

$$
R.\theta_0=\theta_0,\quad R.\theta_1=\theta_1,\quad
R.\theta_2=\theta_a,\quad R.\Theta=\Theta,\quad R.m=M.
\tag{3}
$$

此外 $R<P$，其中比较使用末基数及有界 application 关系。这里的 $R$ 不是普通删尾实现：普通删尾的末端为 $\theta_n$，而重定位后的末端仍为 $\Theta$。

### 构造辅助嵌入

取原第二行 owner $G$，于是

$$
G:\theta_0\longmapsto\theta_1\longmapsto\theta_2
  \longmapsto\theta_3.
$$

若 $a=3$，取 $G_a=G$。若 $a>3$，由
[Qi 引理 2.11](https://arxiv.org/html/2501.06733v5)
的命名点搬运结论，取 $H$ 使

$$
\operatorname{crit}(H)=\theta_3,\qquad H(\theta_3)=\theta_a,
$$

并令 $G_a=H(G)$。该引理的使用只涉及原 BLS 的两个命名点；不预设任意临界点子序列都可实现。应用恒等式给

$$
G_a:\theta_0\longmapsto\theta_1\longmapsto\theta_2
  \longmapsto\theta_a.
\tag{4}
$$

式 (1) 给出四条边

$$
J(\theta_0)=\theta_2,\quad J(\theta_1)=\theta_a,\quad
J(\theta_2)=\theta_n,\quad J(\theta_a)=\Theta.
\tag{5}
$$

令 $K=J(G_a)$。由 (4)、(5)，

$$
\boxed{
\operatorname{crit}(K)=\theta_2,\qquad
K(\theta_2)=\theta_a,\quad K(\theta_a)=\theta_n,\quad
K(\theta_n)=\Theta.}
\tag{6}
$$

特别地，$K$ 固定 $\theta_0,\theta_1$。

### 搬运整个前缀

对 $0\le i\le n$、$1\le i<n$，定义

$$
R.\theta_i=K(\theta_i),\qquad R.j_i=K(j_i).
\tag{7}
$$

这是将 $P.\mathrm{del}$ 的全部数据整体取 $K$-像，而不是逐段猜测新行的嵌入。严格递增性和全部普通行边由应用恒等式保持；(6) 正好给出 (3) 中的三个点和末端。

对一枚保留标记，设其实际因子词为

$$
W=j_{v_0}\circ\cdots\circ j_t.
$$

它在删尾前缀中的字面 trace 完全不变。搬运后的 owner 与因子分别为 $K(j_i)$、$K(j_{v_r})$，新自然界恰好为

$$
\begin{aligned}
\Delta_R
&=\bigl(K(j_{v_0})\circ\cdots\circ
        K(j_{v_{d-2}})\bigr)(K(\theta_{t+1}))\\
&=K\!\left((j_{v_0}\circ\cdots\circ j_{v_{d-2}})
               (\theta_{t+1})\right)
=K(\Delta_P).
\end{aligned}
\tag{8}
$$

其中 $d$ 为因子数，$v_{d-1}=t$；单因子时前缀复合为空。
因此 $j_i\equiv_{\Delta_P}W$ 搬运为
$K(j_i)\equiv_{\Delta_R}K(W)$。这里不能把自然界随意替换为
$\theta_{y+1}$，也不需要标记具有内部邻接。

proper、精确 trace、PosSource 和 Sat 都是未变的前缀模式 $q$ 的性质。
用 (2) 直接配置新的 linedness 见证；这些见证不必是旧见证的 $K$-像。
于是得到完整的 $R\in\mathcal C$。

### 严格下降

$R$ 的末 owner 为

$$
R.J=K(j_{n-1})=(J(G_a))(j_{n-1}).
\tag{9}
$$

这是一段从 $J$ 出发的两次 application。中间 owner $K$ 的临界点为
$\theta_2<\Theta$，最终 owner 的临界点也由真实末行低于 $\Theta$。
末基数仍为 $\Theta$，故 $R<P$。没有提高周期端点，也没有换生成元。

## 可以使用的放大参数

式 (2) 可以由较短前缀的定量定理提供。例如，把 marks 仅在调用普通定理时忘掉，

$$
M=f\bigl(\operatorname{forget}(p|(a-1)),m\bigr)
\tag{10}
$$

由 Qi 定理 2.25 给出；这里前缀的最后基数正是 $\theta_a$。若采用已经证明的标记版定量定理，也可用

$$
M=f_\star(p|(a-1),m).
\tag{11}
$$

调用普通定理取得 (10) 不要求永久删除实际证书里的 marks；这些 marks 仍按 (8) 搬运。

最简单的情形是 $a=3$。前缀只有固定的首两行，直接由
[Qi 引理 2.4](https://arxiv.org/html/2501.06733v5) 得

$$
\boxed{m\longmapsto g(m)=m2^m.}
\tag{12}
$$

因此，末行 core 为 $(0,1,2,3,n)$、步长 2 时，可以删除该字面行、重定位剩余模式，并把参数从 $m$ 提高到 $g(m)$，而保持原末端。这里没有“反复 M 直到某个未知时刻”的定义。

这是一种新增的**语义证书变换**。未宣称它就是原 IBLP 的一步，也未宣称
$f_\star(p,m)=f_\star(q,g(m))$。改变证书和证明一个特定递归函数的数值恒等式，是两件不同的事。

## 一个明确的重复块公式

设模式末两行为

$$
\begin{array}{c|c|c}
 &\text{core}&\text{步长}\\ \hline
n-1 &(0,1,2,3,n-1)&2\\
n &(0,1,2,n-1,n)&3
\end{array}
\qquad n\ge5,
\tag{13}
$$

其中倒数第二行的唯一 mark 为 3。记前 $n-2$ 行为 $q$。

对最后的 limit 行作 $E(m)$，复制锚点为 $a=n-1>3$。辅助复制固定
0、1、2、3，平移其余坐标。因此 $E(m)$ 的结果是 $q$ 后接 $2^m$
条完全相同类型的长行：

$$
(0,1,2,3,r),\quad \ell_r=2,\quad \operatorname{marks}_r=\{3\}.
\tag{14}
$$

这里“相同”指除末列号 $r$ 外形状相同。每次辅助复制使该块大小加倍，
由 $E(0)$ 的一条长行归纳即得；mark 3 走固定低分支，仍保留。

逐条应用 (12) 的重定位，得到同一末端下、模式为 $q$ 的证书，参数为

$$
\boxed{g^{\,2^m}(m).}
\tag{15}
$$

整个证明以明确的 $2^m$ 作有限归纳，不求某个无上界的 M 正规化长度。
公式 (15) 放大的是参数，不是 BMS 的行数。

## 标准根的有限证书

从标准标记 $P_{\rm start}$、参数 1 出发。写 $M$ 表示本目录已固定的
$M_\star$，写 $E$ 表示 $E(1)$。下列 32 步均保持参数 1 及原末端：

    M M M E M M M M
    E E E M M E E E
    M M E E E E M M
    E E E M M E E E

所得 $P$ 有 36 行。最后四条 core、步长及 marks 是

$$
\begin{array}{c|c|c|c}
r&A_r&L_r&\text{marks}\\ \hline
33&(0,1,2,3,33)&2&\{3\}\\
34&(0,1,2,33,34)&3&\varnothing\\
35&(0,1,2,3,35)&2&\{3\}\\
36&(0,1,2,3,36)&2&\{3\}.
\end{array}
\tag{16}
$$

先重定位末两条长行，参数由 1 变为 2，再变为 8，留下 34 行。
对新的末两行用 (15)，得到一个仅有 32 行的固定模式 $Q$，但具有参数

$$
\boxed{B=g^{256}(8)=g^{258}(1).}
\tag{17}
$$

末端始终是初始的 $\Theta_0<\kappa_4$，首两个基数始终固定。
$Q$ 的具体字面模式是 $P$ 的前 32 行；它仍只含步长不超过 4 的行。
这最后一点说明，(17) 绝不等于已经取得 $B$ 行的 BMS。

有限证书程序（历史参考：`prefix_rebase_probe.py`） 对上述 32 步结果与独立写出的
36 行字面模式逐项比较，再检查 $E(8)$ 精确生成 256 条式 (14) 的长行。
它完成 292 次结构审计，检查普通行型、Sat、PosSource、精确 traces 及
mark 恢复；不把自然界不需要的内部邻接列为前提。2026-10-14 的运行在
约 0.08 秒内完成，最多保留 288 行。$B$ 从未数值展开。

程序验证有限语法计算，重定位的嵌入意义由 (4)—(9) 的证明提供，不能反过来用程序替代这部分数学证明。

## 放大以后切换到无标记规则

从任何 $\mathcal C$ 证书删去全部 marks，都立即得到一个普通 BLS，
而行嵌入、基数、末端和 linedness 参数不变。因此达到 $Q,B$ 后，
可以彻底停止标记补全，转用普通 BLP 的 $M/E$ 与定量定理：

$$
\Theta_0\ge
\gamma_{\,2^{\,f(\operatorname{forget}Q,B)}}.
\tag{18}
$$

由于同一生成代数内 $\Theta_0<\kappa_4=\gamma_{F(4)}$ 且
$q(5)=F(4)+1$，严格得到

$$
\boxed{q(5)>2^{\,f(\operatorname{forget}Q,B)}.}
\tag{19}
$$

式 (19) 是一个定义明确的混合阶段数值下界，但尚未与既有的
$2^{f_\star(P_{\rm start},1)}$ 或三行 BMS 下降次数界比较大小，不能称为
目前最强的数值界。尤其未证明它超过指定的 BMS[10] 快速增长值。

如果后阶段要连普通原生补全也停用，还需抽出一个真正的无补全 BMS 带
实现。仅删掉 marks 保证普通 BLP 实现，并不保证此后的 native 包为空。

## 下一条需要的结构结论

现在有一个真正的低端点入口：固定的 $Q$ 已有极大的可用参数 $B$，
而不是为了取大参数另行把端点抬到很高的 $\kappa_r$。后续可以尝试
带参数的 $E(B)$、有明确次数的补全，或更强的前缀重定位式 (10)。

但必须继续证明：这些操作产生的某个结构，支持**兼容的多行 BMS
映射**，且初始化端点仍在同一界内。大量克隆行、某条行的步长很大、
linedness 参数很大，都不能单独替代该结论。此前的
有限窗口反例（历史参考：`copy-budget-obstructions.zh-CN.md`）也已排除“普通
linedness 自动提供任意长兼容窗口”的直接推断。

这把研究重点转到一个带参数的结构放大引理，而不是逐层手工搜出第四层、
第五层。十层只是目标底线；若参数到层数的统一转移成立，就可以一次利用
(17) 的规模。这个统一转移，以及最后到固定 BMS 快速增长值的比较，目前
仍待证明。

