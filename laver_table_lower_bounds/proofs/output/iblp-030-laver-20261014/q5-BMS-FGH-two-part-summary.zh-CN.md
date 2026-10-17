# 周期三十二的三层 BMS 快速增长下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。在 **ZFC + I3** 下，令 $q(5)$ 是普通二元 Laver 表首行
周期首次达到 $32$ 的阶参数，即表有 $2^{q(5)}$ 个元素。
令 $\Lambda$ 表示 BMS 极限，采用下文的基本列和 FGH 约定。则

$$
\boxed{\displaystyle
q(5)>F_\Lambda\!\left(F_\Lambda\!\left(F_\Lambda\!
\left(F_3(256)\right)\right)\right).}
\tag{A}
$$

这是同一个 $F_\Lambda$ 的三次函数复合：两次行数反馈，再加上最内层
的一次 BMS 计算。主式保守取内层输入 $256$，不残留对数、加性常数或
辅助函数。证明只分两部分：先接到 BMS 固定下降次数，再接到 FGH 并支付
全部开销。这是纸面证明，尚未 Lean 形式化。

## 第一部分 Laver 表与 BMS 固定下降的对接

### 1. 计数与端点接口

括号表示 BMS 的一列。定义

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h),
$$
$$
D(h)=\text{从 }R_h\text{ 固定取原 BM4 }[1]\text{ 到空的总步数},
\qquad T(h)=D(h)+2.
\tag{1}
$$

原 BM4 `[1]` 是本目录父表新表示的 `[2]`，不是新表示的 `[1]`。
$D$ 计入每次展开，而不仅是删除零末列的步骤。这里的 $T$ 始终是
整数函数 (1)，不指其他文稿中临时命名为 $T$ 的嵌入。

固定 I3 嵌入 $j$，全部见证均在同一个 $\operatorname{Iter}(j)$ 中。
$\gamma_n$ 枚举其临界点，$\kappa_i=j^i(\gamma_0)$。已知
$\kappa_3=\gamma_4$；若 $\kappa_4=\gamma_s$，有限 Laver 表对应给出

$$
q(5)=s+1.
\tag{2}
$$

高度 $h$ 的闭合相容组有严格递增的点
$U_0<\cdots<U_h<V_0<\cdots<V_{h+1}<c$，以及实际嵌入满足

$$
\operatorname{crit}(K_i)=U_0,\quad K_i(U_t)=V_t\ (t\le i),
\quad K_i(V_0)=V_{i+1},
$$
$$
\operatorname{crit}(L)=V_0,\quad L(V_0)=V_{h+1},\quad L(V_{h+1})=c.
\tag{3}
$$

把三条列带放在 $U,V,L(V)$ 上，第二个正列使用 $L(K_i)$，即可实现
特定种子 $R_h$。这里 $L$ 固定共同源点，所以两个正列确实具有相同的父列。
[带实现保持性](<../iblp-laver-bms-20261013/ribbon-initialization.zh-CN.md>)
与[平衡带计数](<../iblp-laver-bms-20261013/balanced-ribbon-bridge.zh-CN.md>)证明：
原 BM4 每步由若干删端点和一次短复制实现，补全失活；复制不提高末端。
当 $h\ge3$ 时，BMS 总步数严格小于实际删端点次数。故封口 $c=\gamma_a$ 时

$$
D(h)<a.
\tag{4}
$$

因此 $c<\kappa_4$ 蕴含 $q(5)>D(h)$。控制的是表的阶参数，
不是较弱的表大小 $2^{q(5)}$ 下界。

### 2. 长链初始化

沿用[有限初始化](<../iblp-laver-bms-20261013/short-terminal-initialization.zh-CN.md>)
中的 $K=j_{(11)}$ 及 $\theta_5<\theta_6<\theta_7<\theta_8<\kappa_4$。
[Qi 命题 1.3(1) 的证明及引理 3.3](https://arxiv.org/html/2501.06733v5#S3)
提供实际的 $C$-lined 链

$$
(\kappa_0,\kappa_1,\theta_5),\qquad
C=f(p_{\omega+2},1),\qquad 2^C=m_{\omega+2}(2).
\tag{5}
$$

这里直接使用链见证，不从“临界点下标很大”倒推 linedness。
$C$ 的纯有限整数定义和下界放在第二部分。

有限初始化还有 $L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7$。令
$E=L_3(K)$、$\tau=L_3(\theta_5)$，则

$$
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,
\quad E(\theta_6)=\tau,\quad \theta_6<\tau<\theta_7.
\tag{6}
$$

把 (5) 整体取 $E$-像，其末端 $E(\theta_5)<\tau$。
[统一前端插入](<../iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md>)
把根为 $\kappa_2$、起点不低于 $\theta_6$ 的 $m$ 段链变成高度
$m+2$ 的闭合相容组，封口严格低于链末端。故有高度 $C+2$、封口低于
$\tau$ 的组；取原链前缀也给出每个 $3\le h\le C+2$ 的组。
此处不依赖早先的标记启动历史。

### 3. 两次反馈分别检查端点

[第一轮降根反馈](<root-lowered-bms-feedback.zh-CN.md>)构造了实际嵌入 $P$，满足

$$
P(\gamma_0)=\theta_6,\quad P(\gamma_1)=\tau,
\quad P(\tau)=\theta_7,
\quad (\kappa_2,\theta_6,\tau)\text{ 是 2-lined}.
\tag{7}
$$

输入高度为 $h$、封口为 $c<\tau$。令 $N=D(h)$、
$m=\lfloor\log_2N\rfloor$。式 (4) 给出 $\gamma_N<c$。
Dougherty 的标准 $m$ 段链
$(\gamma_0,\gamma_1,\gamma_{2^m})$ 取 $P$-像，再与 (7) 相乘，给出
$2^{m+1}>N$ 段链，末端低于 $P(c)<\theta_7$。保端点缩至 $N$ 段并
前端插入，得到高度 $T(h)=N+2$、封口低于 $\theta_7$ 的组。

下一轮不能直接重复同一窗口，因为 $\theta_7>\tau$。
[第二轮搬运](<promoted-bms-feedback.zh-CN.md>)使用 $S=j_{(9)}(j_{(4)})$，证明

$$
S(\kappa_2)=\kappa_2,\quad
\theta_7<S(\tau),\quad S(\theta_7)<\theta_8<\kappa_4.
\tag{8}
$$

把 (7) 取 $S$-像，第一轮输出就合法进入第二轮，得到高度 $T(T(h))$、
封口低于 $S(\theta_7)<\kappa_4$ 的组。由 (2)、(4)，第一部分的接口为

$$
\boxed{q(5)>D\!\left(T(T(C+2))\right).}
\tag{9}
$$

只有第一轮也可得 $q(5)>D(T(C+2))$。这里没有断言任意多轮反馈仍可
留在 $\kappa_4$ 以下。更完整的链见证与来源见
[嵌套下界的逐项证明](<nested-bms-FGH-bound.zh-CN.md>)。

## 第二部分 D 与 FGH 的对接及所有放缩

### 1. FGH 约定和指数塔余量

$Z$ 为零列。采用原 BM4 基本列，定义

$$
F_\varnothing(x)=x+1,\quad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\quad
F_M(x)=F_{M[x]}(x)\quad(M\text{ 末列非零}),
$$
$$
\Lambda[x]=B_{x+1},\qquad F_\Lambda(x)=F_{B_{x+1}}(x).
\tag{10}
$$

定义 $e_0=1,e_{n+1}=2^{e_n}$，并令
$\ell(x)=\lceil\log_2(x+2)\rceil$。
用户提供的 [BMS 端总结](<../iblp-laver-bms-20261013/BMS-fixed-index-to-FGH-summary.zh-CN.md>)
在 $h\ge r+2+\ell(x)$ 时证明 $D(h)\ge F_{B_r}(x)$。
其[森林证明](<../iblp-laver-bms-20261013/diagonal-forest-hardy-proof.zh-CN.md>)式 (9)
实际保留更强的终点计数 $e_y$，因而同一证明给出

$$
\boxed{D(h)\ge e_{F_{B_r}(x)}
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}
\tag{11}
$$

具体链条为

$$
D(h)\ge s_{R_h}(1)
\ge s_{\Sigma(W(B_r)Z^x)}(1)
\ge e_{H_{W(B_r)}(x)}=e_{F_{B_r}(x)}.
$$

这里 $s$ 只计零列删除，$W$ 把 FGH 精确编译为 Hardy，$\Sigma$
增加一行森林；祖先覆盖和行宽交换给出明确尺寸预算。辅助非标准矩阵
由标准对角链覆盖而终止。这一部分不使用 I3，只使用标准 BMS 良序性
及所链接的有限结构证明。

### 2. 每层输出支付下一层行数

置 $\rho(x)=x+3+\ell(x)$。在 (11) 取 $r=x+1$，有

$$
h\ge\rho(x)\quad\Longrightarrow\quad D(h)\ge e_{F_\Lambda(x)}.
\tag{12}
$$

对标准下标作良基归纳，(10) 给出 $F_M(x)\ge x+1$。故 $x\ge2$ 时，
$y=F_\Lambda(x)\ge3$。由 $2^y\ge y+2$，得 $\ell(y)\le y$，
所以 $\rho(y)\le2y+3$。同时，对所有 $y\ge3$，

$$
e_y\ge2y+3>y.
\tag{13}
$$

基础为 $e_3=16\ge9$；归纳步用
$e_{y+1}=2^{e_y}\ge2e_y\ge4y+6\ge2(y+1)+3$。因此

$$
\boxed{h\ge\rho(x),\ x\ge2
\quad\Longrightarrow\quad T(h)\ge\rho(F_\Lambda(x)).}
\tag{14}
$$

下一层的全部对数开销及加性常数由 (13) 支付。
不能仅凭较弱的 $D(h)\ge F_\Lambda(x)$，就把每个嵌套 $D$ 直接替换成
$F_\Lambda$；保留指数塔余量正是修补这个跳步。

### 3. 内层输入的准确常数

有限下标由 (10) 计算：

$$
F_1(x)=2x+1,\quad F_2(x)=(x+1)2^{x+1}-1,
\quad \boxed{t=F_3(256)=F_2^{\circ257}(256).}
\tag{15}
$$

函数上标 $\circ n$ 表示复合 $n$ 次。最内层不是
$F_2^{\circ256}(256)$，也不是反馈函数的 $T(3)$。

(5) 的 $C$ 可用纯有限整数递归精确定义：

$$
\begin{aligned}
g(x)&=x2^x,&u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),&C&=w(w(1)).
\end{aligned}
\tag{16}
$$

文献中的 $m_0(n)=n^n$、$m_{k+1}(n)=m_k^{\circ n}(n)$、
$m_\omega(n)=m_n(n)$ 给出指数共轭 $m_k(2^x)=2^{u_k(x)}$。
再取 $\omega,\omega+1,\omega+2$ 三步，便得
$m_{\omega+2}(2)=2^{w(w(1))}$，所以 (16) 没有更换原常数。

对 $x\ge1$，$g(x)\ge2x$，且

$$
g^{\circ2}(x)\ge g(2x)=2x2^{2x}
\ge(x+1)2^{x+1}>F_2(x).
$$

这些函数严格递增，且 $g^3(1)=2048>256$，故

$$
t<g^{\circ514}(256)<g^{\circ517}(1).
\tag{17}
$$

写 $b=g^{\circ258}(1)$。直接核对
$u_1(1)=8$、$v(1)=u_2(1)=u_1(8)=g^{\circ256}(8)=b$。
对 $k$ 归纳，各 $u_k$ 严格递增、大于恒等函数，并随 $k$ 不减；
增加输入同时增加初值和迭代次数，所以 $v,w$ 也具有这些性质。于是

$$
\begin{aligned}
C&>w(1)=v(b)=u_{2^b}(b)\\
&\ge u_1(b)=g^{\circ2^b}(b)
=g^{\circ(2^b+258)}(1)\\
&\ge g^{\circ519}(1)>g^{\circ2}(t)\ge4t.
\end{aligned}
\tag{18}
$$

迭代次数比较只需 $b\ge2048$。由 $t\ge2$、$\ell(t)\le t$，

$$
\boxed{C+2\ge t+3+\ell(t)=\rho(t).}
\tag{19}
$$

若保留较强的 $257$，把 (17) 的 $514,517$ 改为 $516,519$，
把 (18) 的 $519$ 改为 $521$，证明仍成立。
取 $256$ 是保守简化，不是把未检查的开销藏进常数。

### 4. 合并为主式

置 $h_0=C+2,h_1=T(h_0),h_2=T(h_1)$，以及
$x_0=t,x_{i+1}=F_\Lambda(x_i)$。由 (19)、(14) 依次得

$$
h_0\ge\rho(x_0),\qquad h_1\ge\rho(x_1),\qquad h_2\ge\rho(x_2).
$$

第一部分 (9)，再用 (12)、(13)，即有

$$
q(5)>D(h_2)\ge e_{x_3}>x_3
=F_\Lambda\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).
$$

这证明 (A)。只有第一轮反馈时同理得到两层版本。
全程没有使用一般的“序数下标较大则 FGH 数值较大”，也不需要先证明
$F_\Lambda$ 的输入单调性；每次都直接核对所需行数。

### 5. T 的小值与结论边界

按 (1)，$D(1)=7,D(2)=22$，故 $T(1)=9,T(2)=24$。这些小值可以
直接证明，不必把有限测试当作数值定义：令 $A=(00)(11)(10)$，则原 `[1]` 有

$$
\begin{aligned}
R_2&\longrightarrow(00)(11)(10)(21)
\longrightarrow(00)(11)(10)(20)\\
&\longrightarrow(00)(11)(10)(10)
\longrightarrow AA.
\end{aligned}
$$

又 $A[1]=B_2B_2$，$B_2[1]=B_1$（忽略全零高行），$d_1(B_1)=3$。
块首零列切断父边，故串接块独立下降，得到
$D(2)=4+2(1+2\cdot4)=22$。同理 $R_1[1]=B_1B_1$，所以 $D(1)=7$。

而 $T(3)$ 准确指

$$
T(3)=d_1\bigl((000)(111)(111)\bigr)+2.
$$

它不是森林塔 $e_3$ 或 $g^3(1)$ 的另一种写法。目前未在此给出其
简单精确数值。一个严格但保守的下界是 $T(3)\ge28$：$R_3$ 经四步到
$(000)(111)(110)(200)(311)(310)$，其最后三列在前两行直接覆盖 $R_2$，
由祖先覆盖的计数定理，剩余至少有 22 步，故 $D(3)\ge26$。
本证明从文献长链高度 $C+2$ 启动，不以 $T(3)$
作为隐去开销的常数，因此不需要先算出它的十进制展开。

式 (A) 是 I3 条件下的数值下界，没有构造内部结构实质超越 BMS 的新记号，
也没有证明原 IBLP 030 的指定 Hardy 或 FGH 值受 $q(5)$ 控制。
不能把三次函数复合换个名称，就宣布结构性超 BMS 的目标完成。
有限程序核验只检查局部代数和编码接口，不代替上述全称证明。

后续补充：三行种子计数的结构上下界（历史参考：`T3-fixed-BMS-count-bounds.zh-CN.md`）
改进了上述 $T(3)$ 的保守估计，但仍不冒称得到它的精确值。
[沿长链逐段反馈](<lined-feedback-corridor.zh-CN.md>)进一步让反馈轮数由 BMS
计算产生，得到更强的 $F_{\Lambda+1}(F_\Lambda(F_\Lambda(F_3(256))))$
数值下界；本篇式 (A) 作为原先两轮反馈的独立总结保持不变。
