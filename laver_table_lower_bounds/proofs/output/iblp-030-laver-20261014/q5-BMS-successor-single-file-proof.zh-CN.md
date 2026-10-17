# Laver 周期三十二的 BMS 极限后继层下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。单文件纸面证明。公理假设为 **ZFC + I3**，尚未 Lean 形式化。

令 $\Lambda=\lim(\mathrm{BMS})$。按本文明确指定的基本列及快速增长函数约定，证明

$$
\boxed{\displaystyle
q(5)>F_{\Lambda+1}\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).
}\tag{主定理}
$$

这里 $q(5)$ 是普通二元 Laver 表首行周期首次达到 $32$ 的**阶参数**：
该表有 $2^{q(5)}$ 个元素。比较对象是两个自然数，不是将自然数与序数比较。
$\Lambda+1$ 在结论中表示一次后继层快速增长函数；本定理不声称已经构造了
内部结构显著强于 BMS 的新记号。

证明分成两部分。第一部分把 Laver 临界点区间变为可迭代的 BMS 计算预算；
第二部分把固定指标下降次数变为 FGH，并逐项支付行数和输入开销。
本次研究所需的新引理均在本文证明；只把第 2 节明列的已发表定理作为外部输入，
不要求读者另外打开其他本地研究文稿。

## 1 记号和计数约定

### 1.1 普通 Laver 表

$A_m$ 为大小 $2^m$ 的普通二元 Laver 表，编号为 $1,\ldots,2^m$，
满足左自分配律和 $a*1=a+1\pmod {2^m}$。记首行的最小周期为 $p_m$，定义

$$
q(n)=\min\{m:p_m\ge2^n\}.
$$

I3 下这些最小值存在。下文只使用 $q(5)$。

固定一个 I3 嵌入 $j:V_\lambda\to V_\lambda$。所有见证属于同一个
$\mathcal I=\operatorname{Iter}(j)$，允许 application 和普通复合。
$a(b)$ 表示 application；$a\circ b$ 表示普通函数复合，不能混读。
记

$$
j_{(1)}=j,\quad j_{(n+1)}=j_{(n)}(j),\quad
\kappa_0=\operatorname{crit}(j),\quad\kappa_{i+1}=j(\kappa_i),
$$

并用 $\gamma_0<\gamma_1<\cdots$ 枚举 $\mathcal I$ 的全部临界点。
下文每个命名序数点都属于这一个集合。

### 1.2 BMS 的指标

全篇 $M[n]$ 都是**原 BM4 指标**：$[0]$ 删末列，正末列的 $[n]$
保留删末列所得前缀，并附加 $n$ 份坏块副本。零末列在所有指标下均删除。
因此本文的固定 $[1]$ 等于此前父表展示版的固定 $[2]$。

设 $Z$ 为全零列，括号表示一个矩阵列，令

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h),
$$
$$
d_n(M)=\text{固定取 }[n]\text{ 到空的总步数},\qquad
s_M(n)=\text{其中删除零末列的次数},
$$
$$
D(h)=d_1(R_h),\qquad T(h)=D(h)+2.
$$

零的自环不计为一步。所有实际使用的计数的终止性在第 10 节得到保证。
$T^{\circ a}$ 总表示函数复合 $a$ 次。

### 1.3 FGH 约定

对标准 BMS 式，取

$$
F_\varnothing(x)=x+1,\qquad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\qquad
F_M(x)=F_{M[x]}(x)\quad(M\text{ 末列非零}).\tag{1.1}
$$

顶端及其后继取

$$
\Lambda[x]=B_{x+1},\qquad F_\Lambda(x)=F_{B_{x+1}}(x),\qquad
F_{\Lambda+1}(x)=F_\Lambda^{\circ(x+1)}(x).\tag{1.2}
$$

有限下标 $n$ 指 $Z^n$。特别地

$$
F_1(x)=2x+1,\qquad F_2(x)=(x+1)2^{x+1}-1,\qquad
t:=F_3(256)=F_2^{\circ257}(256).\tag{1.3}
$$

## 2 明确引用的文献输入

以下是外部定理及基础演算，不是由有限程序测试假设的性质。

**Laver–Dougherty 对应。** $\mathcal I$ 的临界点集序型为 $\omega$，
$\kappa_0=\gamma_0,\kappa_1=\gamma_1,\kappa_2=\gamma_2,\kappa_3=\gamma_4$。
若 $j(\gamma_n)=\gamma_a$，首行周期在表阶 $a$ 时不超过 $2^n$，
在 $a+1$ 时首次超过 $2^n$。周期只保持或翻倍。因此

$$
\kappa_4=\gamma_s\quad\Longrightarrow\quad q(5)=s+1.\tag{2.1}
$$

同一代数中，对每个 $m\ge1$，有
$m$-lined $(\gamma_0,\gamma_1,\gamma_{2^m})$ 的见证；各段可取
$j_{(2^{2^i}-1)}$，$0\le i<m$。来源是
[Dougherty 第二篇第 2 节及定理 3.1(c)](https://arxiv.org/pdf/math/9503204)。
lined 的定义见第 3 节。

**有限点像与截断。** 置 $K=j_{(11)}$，以及

$$
(\theta_0,\ldots,\theta_8)=
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,
j_{(7)}(\kappa_2),K(\kappa_3),j_{(10)}(\kappa_3),K(K(\kappa_3)),j_{(9)}(\kappa_3)).
$$

使用下列有限资料；记 $\mu=\theta_4$：

$$
\begin{gathered}
\theta_0<\cdots<\theta_8<\kappa_4,\qquad
K(\theta_i)=\theta_{i+2}\quad(0\le i\le5),\\
\operatorname{crit}(j_{(10)})=\kappa_1,\quad
j_{(10)}(\kappa_1)=\kappa_2,\quad j_{(10)}(\kappa_2)=\mu,\\
j_{(3)}:\kappa_0\mapsto\kappa_2\mapsto\kappa_3,
\quad j_{(3)}(\kappa_1)=\gamma_3,\quad\kappa_2<\gamma_3<\kappa_3,\\
j_{(4)}:\kappa_2\mapsto\gamma_3\mapsto\kappa_3,
\qquad j_{(9)}(\kappa_1)=\kappa_2,\\
K\equiv_\mu j\circ j,\qquad
j_{(3)}\equiv_{\gamma_3}j\circ j.
\end{gathered}\tag{2.2}
$$

来源为 [Dougherty 第一篇第 5 节](https://arxiv.org/pdf/math/9205202)及
[Qi 第 5 节](https://arxiv.org/html/2501.06733v5#S5)。$\equiv_\delta$
是 membership 截断等价，不是任意低输入处的函数相等。使用其标准规则

$$
a(b)\equiv_{\operatorname{crit}(a)}b,\qquad
a\equiv_\delta b\Longrightarrow Q(a)\equiv_{Q(\delta)}Q(b).\tag{2.3}
$$

截断可降低并传递；只有一侧的**输出严格低于截断点**，才读取对应点像相等。
application 的基础恒等式为

$$
a(b)(a(\xi))=a(b(\xi)),\quad
\operatorname{crit}(a(b))=a(\operatorname{crit}(b)),\quad
a(b(c))=a(b)(a(c)),\quad
a(b\circ c)=a(b)\circ a(c).\tag{2.4}
$$

每个嵌入严格递增，并固定小于临界点的序数。

**Qi 的实际长链。** 有 $C_{\rm line}$-lined
$(\kappa_0,\kappa_1,\theta_5)$ 的实际见证，其中

$$
2^{C_{\rm line}}=m_{\omega+2}(2),\quad
m_0(n)=n^n,\quad m_{\alpha+1}(n)=m_\alpha^{\circ n}(n),\quad m_\omega(n)=m_n(n).
\tag{2.5}
$$

这里引用的是 [Qi 命题 1.3(1) 的证明与引理 3.3](https://arxiv.org/html/2501.06733v5#S3)
中构造出的链，不是从一个临界点下标下界反推链的存在。

**BMS 良序性及父表公式。** 标准 BMS 良序，普通展开的父表公式如第 9 节。
来源为 [《Well-Orderedness of the Bashicu Matrix System》](https://arxiv.org/html/2307.04606v2)，
其中父表复制见 Lemma 2.5。本文另行证明非标准辅助矩阵的覆盖及终止接口。

以上是外部输入清单。特别地，不引用完整 IBLP 的良序性、不引用 IBLP 030
与任何增长函数的尚未完成的比较，也不假定任意高行矩阵都支配任意低行矩阵。

## 第一部分 Laver 端点与 BMS 计算

## 3 有限链的操作

称 $(r;a,b)$ 为 $m$-lined，指有
$a=u_0<\cdots<u_m=b$ 和 $Q_i\in\mathcal I$，满足

$$
\operatorname{crit}(Q_i)=r,\quad Q_i(r)=u_i,\quad Q_i(u_i)=u_{i+1}
\quad(0\le i<m).
\tag{3.1}
$$

把各点及见证取任意 $H$ 的像，由 (2.4) 得到
$(H(r);H(a),H(b))$ 的同长链。

**缩链。** 两段 $U:r\mapsto x\mapsto y$、
$V:r\mapsto y\mapsto z$ 可换成 $V(V)(U):r\mapsto x\mapsto z$。
因为 $V(V)$ 的临界点为 $y$，固定 $r,x$，并把 $y$ 送到 $z$。
于是任意非空长链可缩至任意更小正长度，同时保留三个端点。

**链乘法。** 若 $(r;a,b)$ 为 $m$-lined，$(a;b,c)$ 为
$n$-lined，则 $(r;a,c)$ 为 $m2^n$-lined。

证明对 $n$ 归纳。$n=1$ 时，用唯一见证 $H:a\mapsto b\mapsto c$
搬运第一条链，得到 $(r;b,c)$ 的 $m$ 段，与原链拼成 $2m$ 段。
一般情形，第二条链先取前 $n-1$ 段，归纳得到从 $a$ 到倒数第二端点
的 $m2^{n-1}$ 段。将原第一条链和第二条链前 $n-1$ 段一并用最后见证
搬运，归纳得到从该倒数第二端点到 $c$ 的另 $m2^{n-1}$ 段；拼接即可。
这也直接证明了本文所用的 Qi 链乘法特例。

## 4 闭合相容组和弱带实现

### 4.1 闭合相容组

高度 $h$ 的闭合相容组是严格递增的点

$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1}<C
$$

及嵌入 $K_1,\ldots,K_h,L\in\mathcal I$，满足

$$
\operatorname{crit}(K_i)=U_0,\quad K_i(U_t)=V_t\ (0\le t\le i),\quad
K_i(V_0)=V_{i+1},
\tag{4.1}
$$
$$
\operatorname{crit}(L)=V_0,\quad L(V_0)=V_{h+1},\quad L(V_{h+1})=C.
\tag{4.2}
$$

$C$ 称为封口。本文构造的组均有 $U_0=\kappa_0,U_1=\kappa_1$。

### 4.2 弱带实现的定义

固定矩阵高度 $h$，令 $w=h+1$。对一个 $m$ 列矩阵选取
$\alpha_0<\cdots<\alpha_{mw}$。第 $j$ 列使用
$\alpha_{jw},\ldots,\alpha_{jw+h}$，右端点为 $\alpha_{(j+1)w}$。
若第 $k-1$ 行有父列 $c$，其中 $1\le k\le h$，要求实际嵌入 $J_{j,k}$ 满足

$$
\operatorname{crit}(J_{j,k})=\alpha_{cw},\quad
J_{j,k}(\alpha_{cw+t})=\alpha_{jw+t}\ (0\le t\le k),\quad
J_{j,k}(\alpha_{jw})=\alpha_{jw+k+1}.\tag{4.3}
$$

零端口、锚点端口 $k=0$ 不要求嵌入见证。这是**弱带实现**，并非完整普通
BLS；下面直接证明其保持性，不借用完整 BLS 的存在性。

组 (4.1)–(4.2) 实现 $R_h$：三个带依次放在
$U_0,\ldots,U_h$、$V_0,\ldots,V_h$、$L(V_0),\ldots,L(V_h)$，
总封口为 $C$。第一正列用 $K_k$，第二正列用 $L(K_k)$。
由于 $L$ 固定全部 $U_t$，两列的父均为第零列，所有 (4.3) 由 (2.4) 给出。

### 4.3 一步保持及其端点代价

给每个带端口编号 $b_j+k$，其中 $b_j=3+jw$。锚点和零端口的形式行记作
$(0,b_j+k,b_j+k+1):1$；正端口形式行为

$$
(b_c,\ldots,b_c+k,b_j,\ldots,b_j+k,b_j+k+1):(k+1).\tag{4.4}
$$

编号 $0,1,2$ 只是语法保护，不参与弱实现的序数赋值。

若末列全零，删除最后 $w$ 个端点即实现其展开。
若末列 $x$ 的最高正端口为 $k$，父为 $c$，先删除 $h-k$ 个尾端点。
活动嵌入 $J=J_{x,k}$ 将源区间的点

$$
\alpha_{cw+k}<\alpha_t<\alpha_{xw}
$$

送入当前最后两点 $\alpha_{xw+k},\alpha_{xw+k+1}$ 之间。
按顺序插入这些像；源前 $k$ 个端口的像已由 (4.3) 指定，源基点以前的点被固定。
每个被复制的正行用 $J(K)$ 作见证，满足 (2.4)；零行无需见证。

在形式行中，这正好复制区间
$[b_c+k,b_x)$。地址 $<b_c$ 固定，所有地址 $\ge b_c$ 平移
$(x-c)w$。保留的旧末带前 $k$ 个端口，加上父带剩余端口的副本，
成为新首带：活动行以下继承旧末列，活动行及以上继承父列。
其余带按相同平移复制，与第 9 节的 BMS 父表公式逐项一致。
复制结果恰为 $2x-c$ 列，不留下半条尾带。

因此一次原 BM4 $[1]$ 由 $h-k$ 次删端点和一次**保封口**复制实现。
每个插入点是同一 $\mathcal I$ 内的临界点。此编码也不需要任何补全：
形式行 (4.4) 的补全扫描先遇到带锚点，而该锚点的回指为 $0$，立即越过下界。
本证明只用上述显式操作，因而无需另行假定完整 BLP 的 M 保持定理。

### 4.4 总步数严格小于删端点次数

设固定 $[1]$ 下降的初始列数为 $m>0$，将步骤分四类：

- $u$：非零末列、活动端口 $k=h$、坏块宽 $d=1$；
- $v$：非零末列、$d\ge2$；
- $s$：非零末列、$d=1,k<h$；
- $z$：删除零末列。

设删端点总数为 $\delta$，总 BMS 步数为 $D_*=u+v+s+z$。列数守恒及操作定义给出

$$
z=m+\sum_{\rm 正步骤}(d-1)\ge m+v,\qquad
\delta=\sum_{\rm 正步骤}(h-k)+(h+1)z\ge s+(h+1)z.\tag{4.5}
$$

还有 $u\le v+z$。证明考虑连续 $d=1$ 的正步骤，倒数第二列 $Q$ 不变。
发生一次 $u$ 后，若 $Q$ 仍有最高行，新末列的最高父继承 $Q$ 的父，
下一步的坏块宽至少为 2；若 $Q$ 无最高行，新末列高度降至 $h-1$，
以后在遇到 $v$ 或 $z$ 前不能升回 $h$。每个 $u$ 归属其后第一个
$v$ 或 $z$，不会重复归属；最终删空保证这个后继步骤存在。

于是

$$
D_*\le s+2v+2z\le s+4z-2m
\le\delta-(h-3)z-2m<\delta\quad(h\ge3).\tag{4.6}
$$

若初始封口为 $\gamma_a$，每次删除严格降低末端的全局临界点下标，复制不提高末端，
故 $\delta\le a$。特别地，高度 $h\ge3$ 的组封口 $C=\gamma_a$ 给出

$$
\boxed{D(h)<a,\qquad\gamma_{D(h)}<C.}\tag{4.7}
$$

若 $C<\kappa_4$，由 (2.1) 又得 $q(5)>D(h)$。这一步控制的是表阶，
不是只控制表的元素个数。

## 5 有限初始化的全部项

本节仅使用 (2.2)–(2.4)。为避免与随后窗口端点 $a,b,c$ 混名，把辅助项加下标：

$$
a_*=K(K),\ b_*=K(j),\ c_*=a_*(b_*),\ d_*=c_*(K),\ e_*=d_*(j),
$$
$$
f=e_*(K),\ g_*=f(K),\ r_*=g_*(f),\ p_*=f(b_*),\ s_*=r_*(d_*),\
J=p_*(f),\ L_2=s_*(g_*).\tag{5.1}
$$

第一批点像如下。每行按输入与输出顺序一一对应：

$$
\begin{array}{c|c|c}
\text{项}&\text{输入}&\text{输出}\\\hline
a_*&(\theta_2,\theta_3,\theta_4,\theta_5)&(\theta_4,\theta_5,\theta_6,\theta_7)\\
b_*&(\theta_2,\theta_3,\theta_4)&(\theta_3,\theta_4,\theta_5)\\
c_*&(\theta_4,\theta_5,\theta_6)&(\theta_5,\theta_6,\theta_7)\\
d_*&(\theta_0,\theta_1,\theta_2,\theta_3)&(\theta_2,\theta_3,\theta_5,\theta_6)\\
e_*&(\theta_2,\theta_3,\theta_5)&(\theta_3,\theta_5,\theta_6)
\end{array}\tag{5.2}
$$

例如 $c_*(\theta_4)=a_*(b_*)(a_*(\theta_2))=a_*(\theta_3)=\theta_5$；
$d_*(\theta_2)=c_*(K)(c_*(\theta_2))=c_*(\theta_4)=\theta_5$，
因为 $\operatorname{crit}(c_*)=\theta_4$ 固定 $\theta_2$。其余等式同样直接代入 (2.4)。

定义

$$
\alpha=e_*(\theta_4),\quad\beta=f(\theta_2),\quad
\zeta=f(\theta_4),\quad\eta=r_*(\theta_3),\quad\rho_0=r_*(\theta_5).
$$

由 (5.2) 及单调性，依次有
$\theta_5<\alpha<\theta_6$、$\theta_5<\beta<\alpha$、
$\alpha<\zeta<\theta_6$。继续搬运得

$$
\begin{array}{c|c|c}
f&(\theta_0,\theta_1,\theta_3,\theta_5)&(\theta_3,\theta_5,\alpha,\theta_6)\\
g_*&(\theta_3,\theta_5,\beta,\alpha)&(\beta,\alpha,\zeta,\theta_6)\\
r_*&(\theta_0,\theta_1,\theta_2,\beta)&(\beta,\alpha,\zeta,\theta_6)\\
p_*&(\beta,\alpha,\zeta)&(\alpha,\zeta,\theta_6)\\
s_*&(\beta,\alpha,\zeta)&(\zeta,\eta,\rho_0)\\
J&(\theta_0,\theta_1,\theta_2,\theta_3,\theta_4)&(\theta_3,\theta_5,\alpha,\zeta,\theta_6).
\end{array}\tag{5.3}
$$

例如 $J(\theta_2)=p_*(f(\theta_2))=p_*(\beta)=\alpha$，因 $p_*$
固定 $\theta_2$。将 $\theta_2<\theta_3<\theta_5<\beta$ 代入 $r_*$ 得

$$
\theta_5<\beta<\alpha<\zeta<\eta<\rho_0<\theta_6.\tag{5.4}
$$

临界点由 (2.4) 同步计算。$f,J$ 的临界点为 $\theta_0$，
$\operatorname{crit}(L_2)=\theta_3$，并有
$L_2(\theta_3)=\zeta,L_2(\zeta)=\rho_0$。所以

$$
U=(\kappa_0,\kappa_1,\kappa_2),\quad
V=(\kappa_3,\theta_5,\alpha,\zeta),\quad(K_1,K_2)=(f,J),\quad L=L_2
\tag{5.5}
$$

是高度 2、封口 $\rho_0<\theta_6$ 的组。

另定义

$$
A_*=c_*(d_*),\qquad L_3=A_*(j(j)).
$$

由 (5.2)，$A_*$ 把 $(\theta_1,\theta_2,\theta_3)$ 送到
$(\theta_3,\theta_6,\theta_7)$。$j(j)$ 的临界序列前三点为
$\theta_1,\theta_2,\theta_3$，故

$$
L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7.\tag{5.6}
$$

这里不需要先构造第三层组；(5.6) 是独立的实际 application 项。

## 6 从任意给定长链生成高组

证明如下全称引理：若有 $m$-lined $(\kappa_2;a_0,a_m)$，
$a_0\ge\theta_6$，则有高度 $m+2$、封口低于 $a_m$ 的组。
输入链的见证只须属于环境代数 $\mathcal I$。

### 6.1 插入一层的局部公式

已有高度 $h$ 的组，底部为 $\kappa_0,\kappa_1$。若有 $D_*$ 和 $\delta$ 满足

$$
\operatorname{crit}(D_*)=\kappa_0,\quad
D_*(\kappa_0)=V_0,\quad D_*(\kappa_1)=\delta,\quad D_*(V_0)=V_1,
$$
$$
V_0<\delta<V_1,\qquad K_i\equiv_\delta D_*\quad(1\le i\le h),\tag{6.1}
$$

取临界点为 $\kappa_1$ 的任意 $T_*$，置 $v=T_*(D_*)(\kappa_1)$，定义

$$
\begin{aligned}
U'&=(\kappa_0,\kappa_1,T_*(U_1),\ldots,T_*(U_h)),\\
V'&=(T_*(V_0),v,T_*(V_1),\ldots,T_*(V_{h+1})),\\
K'&=(T_*(D_*),T_*(K_1),\ldots,T_*(K_h)),\quad L'=T_*(L).
\end{aligned}\tag{6.2}
$$

有

$$
T_*(V_0)<v<T_*(D_*)(T_*(\kappa_1))=T_*(\delta)<T_*(V_1).\tag{6.3}
$$

所以可从搬运后的截断等价读取所有旧拥有者在新源 $\kappa_1$ 处的像 $v$；
其他边直接由 (2.4) 得到。封口为 $T_*(C)$。新组的全部拥有者在
$T_*(\delta)>v$ 以下与新最低拥有者相等。这证明局部插入及共同截断不变量。

### 6.2 一段链提供的低位截断

给定 $\operatorname{crit}(Q)=\kappa_2$，令
$T_*=Q(j_{(10)}),Z_*=Q(j_{(3)})$。由 (2.2)，

$$
\operatorname{crit}(T_*)=\kappa_1,\quad T_*(\kappa_1)=Q(\kappa_2),
$$
$$
Q(K)=T_*(Q(j))\equiv_{T_*(\kappa_2)}T_*(j),\qquad
Q(K)\equiv_{Q(\gamma_3)}Z_*.
\tag{6.4}
$$

先由单调性得 $T_*(j)(\kappa_1)<T_*(\kappa_2)$，再合法读值得
$T_*(j)(\kappa_1)=Q(\kappa_3)$。因此

$$
Q(\gamma_3)<Q(\kappa_3)<T_*(\kappa_2),\qquad
T_*(j)\equiv_{Q(\gamma_3)}Q(j_{(3)}).\tag{6.5}
$$

若 $Q_*$ 临界点也是 $\kappa_2$，或为恒等搬运词，则
$Q_*(j)\equiv_{\kappa_2}j$。对 $X=T_*(Q_*(j))$ 同理有

$X\equiv_{T_*(\kappa_2)}T_*(j)$。先用
$T_*(j)(\kappa_1)=Q(\kappa_3)<T_*(\kappa_2)$ 读取点像，
再把截断降低至 $Q(\gamma_3)$，得到

$$
X\equiv_{Q(\gamma_3)}Z_*,\qquad X(\kappa_1)=Q(\kappa_3).\tag{6.6}
$$

### 6.3 下一次低拥有者的统一重建

对普通复合词 $A=a_1\circ\cdots\circ a_t$，约定 $A(b)$ 是逐因子
application 搬运。由 (2.4) 对词长归纳，仍满足相同的点像、LD 和截断搬运律。

归纳维持最低拥有者形如

$$
K_1=A(j_{(3)}),\quad A=P_*\circ T_*\circ Q_*,\tag{6.7}
$$

其中 $P_*$ 各因子临界点均大于 $\kappa_1$，$T_*,Q,Q_*$ 如上；
全体拥有者在某个 $\varepsilon>V_1$ 以下与 $K_1$ 相等。
令

$$
Y=P_*(X)=A(j),\quad Z'=P_*(Z_*),\quad
b'=P_*(Q(\kappa_2))=A(\kappa_1),\quad
\zeta'=P_*(Q(\gamma_3)),\quad W=A(j_{(2)}).
$$

则

$$
\begin{gathered}
\operatorname{crit}(Y)=\operatorname{crit}(Z')=\kappa_0,\quad
Y(\kappa_0)=Z'(\kappa_0)=b',\\
Y(\kappa_1)=P_*(Q(\kappa_3)),\quad Z'(\kappa_1)=\zeta',\quad
Z'(b')=P_*(Q(\kappa_3)),\quad b'<\zeta'<Y(\kappa_1),\\
\operatorname{crit}(W)=b'>\kappa_1,\qquad W(b')=A(\kappa_2)=V_0.
\end{gathered}\tag{6.8}
$$

置 $D_*=W(Z'),\delta=W(\zeta')$。$W$ 固定 $\kappa_0,\kappa_1$，
因此 $D_*$ 满足 (6.1) 的四个点像。
其中

$$
D_*(V_0)=W(P_*(Q(\kappa_3)))=W(Y)(\kappa_1)=K_1(\kappa_1)=V_1.
$$

搬运 (6.6) 得 $K_1=W(Y)\equiv_\delta W(Z')$。又有
$V_0<\delta<V_1<\varepsilon$，所以全体拥有者满足 (6.1)。

用下一段 $T'=Q'(j_{(10)})$ 插入后，新最低拥有者为

$$
T'(D_*)=A'(j_{(3)}),\quad
A'=P'\circ T'\circ Q,\quad P'=T'(W)\circ T'(P_*).\tag{6.9}
$$

$P'$ 每个因子的临界点仍大于 $\kappa_1$，共同截断由 (6.3) 保持。
于是归纳不变量闭合。

### 6.4 起点和封口

从 (5.5) 的高度 2 组开始，首次取
$D_0=e_*(j_{(3)}),\delta_0=e_*(\gamma_3)$。
由 (2.2)，$f=e_*(K)\equiv_{\delta_0}D_0$；
$J=p_*(f)\equiv_{\operatorname{crit}(p_*)}f$，且
$\delta_0<\theta_5<\operatorname{crit}(p_*)=\beta$。
点像满足 (6.1)。首次插入后，(6.7) 中可取
$P_*=T_0(e_*),T_*=T_0,Q_*$ 为恒等搬运词，故后续可统一重建。

现设输入链为 $Q_i:\kappa_2\mapsto a_i\mapsto a_{i+1}$，依次取
$T_i=Q_i(j_{(10)})$。若当前封口 $C_i<a_i$，则

$$
C_{i+1}=T_i(C_i)<T_i(a_i)=Q_i(\mu)<Q_i(a_i)=a_{i+1}.\tag{6.10}
$$

最后严格性使用 $\mu<\theta_6\le a_0\le a_i$。初始
$C_0=\rho_0<\theta_6\le a_0$。归纳 $m$ 次，得到高度 $m+2$、
封口低于 $a_m$ 的组，全称插入引理得证。

## 7 反馈窗口及保周期搬运

### 7.1 基础窗口

定义

$$
k=\kappa_2,\quad a=\theta_6,\quad b=L_3(\theta_5),\quad c=\theta_7,
\quad E=L_3(K),\quad P=L_3(f).
$$

由 (5.3)、(5.6) 和 (2.4)，

$$
k<a<b<c<\kappa_4,\quad
E(\kappa_0)=k,\ E(\kappa_1)=a,\ E(a)=b,
$$
$$
P(\gamma_0)=a,\quad P(\gamma_1)=b,\quad P(b)=c.\tag{7.1}
$$

令 $W=L_3(b_*)$、$a'=L_3(\mu)$。则
$W:k\mapsto a\mapsto a'\mapsto b$，所以 $W,W(W)(W)$
给出 $(k;a,b)$ 的两段链。

把 (2.5) 的长链取 $E$-像，根为 $k$，起点为 $a$，末端为
$E(\theta_5)<E(a)=b$。第 6 节给出高度

$$
h_0=C_{\rm line}+2\tag{7.2}
$$

且封口低于 $b$ 的组。取链前缀，还得到每个 $3\le h\le h_0$ 的这种组。

### 7.2 搬运者的严格端点界

令 $\nu=j_{(9)}(\gamma_3)$。先证明

$$
c=\theta_7<\nu<\theta_8<\kappa_4.\tag{7.3}
$$

后两项由 (2.2) 和单调性。取

$$
V_*=j_{(10)}(j_{(10)}),\quad A=j_{(9)}(j_{(3)})=V_*(j_{(10)}),
\quad B=V_*(j),\quad Q=j_{(10)}(K)=V_*(K)=A(B).
$$

这些项恒等式直接由 LD 展开，不是根据有限点像认同嵌入。
$\operatorname{crit}(V_*)=\kappa_2$，故 $B\equiv_{\kappa_2}j$。
同时 $A(\kappa_1)=\mu,A(\kappa_2)=\nu$，于是
$Q\equiv_\nu A(j)$。因 $\kappa_3<\mu=A(\kappa_1)$，有

$$
A(j)(\kappa_3)<A(j)(A(\kappa_1))=A(\kappa_2)=\nu.
$$

合法读值得 $Q(\kappa_3)<\nu$。另一方面，搬运
$K\equiv_\mu j\circ j$，得
$Q\equiv_{j_{(10)}(\mu)}K\circ K$。
由 $j_{(9)}(\kappa_1)=\kappa_2$ 得
$j_{(9)}(\kappa_2)=\mu$ 及 $j_{(10)}(\mu)=\theta_8$。
又 $K(K(\kappa_3))=\theta_7<\theta_8$，故
$Q(\kappa_3)=\theta_7$，证明 (7.3)。

现在令

$$
S=j_{(9)}(j_{(4)}).
$$

由 (2.2)，$S:\mu\mapsto\nu\mapsto\theta_8$，固定 $k$。
用 $\mu<a<b<c<\nu$，得到

$$
\boxed{c<S(a)<S(b)<S(c)<\theta_8<\kappa_4.}\tag{7.4}
$$

### 7.3 整背景反馈引理

设 $H\in\mathcal I$ 固定 $\gamma_0,\gamma_1$。不要求固定 $k$。
则任意高度 $x\ge3$、封口 $C<H(b)$ 的组，都能变成高度
$T(x)$、封口低于 $H(c)$ 的组。

先说明全称插入工具为何可以搬运。把第 5–6 节的**背景常量、项、点像和截断点**
一并取 $H$-像，再用第 6 节相同公式，对任意新输入链执行有限归纳。
新链根为 $H(k)$，起点不低于 $H(a)$。因为 $H$ 固定前两个源点，
输出组底部仍为 $\kappa_0,\kappa_1$；(6.1)–(6.10) 的严格守卫全部被搬运。
这些公式只要求新链见证在环境代数中，**不要求新见证是某旧见证的 $H$-像**。
因此这里不是对任意输入取不存在的逆像，也不换用 $\operatorname{Iter}(H(j))$
的临界点编号。

对给定输入，置 $N=D(x),m=\lfloor\log_2N\rfloor$。$N\ge3$，由 (4.7) 得

$$
\gamma_{2^m}\le\gamma_N<C<H(b).\tag{7.5}
$$

将全局 Dougherty 的 $m$ 段链取 $H(P)$-像，再与 $H$-像的两段链相乘，得到

$$
(H(k);H(a),Z)\text{ 的 }2^{m+1}\text{ 段链},\qquad
Z=H(P)(\gamma_{2^m})<H(P)(C)<H(P)(H(b))=H(c).
$$

因 $N<2^{m+1}$，保端点缩至 $N$ 段，再用搬运后的全称插入引理。
输出高度为 $N+2=T(x)$，封口低于 $Z<H(c)$。引理得证。
$H$ 为恒等搬运时也成立，给出基础窗口 $b\to c$ 的一次反馈。

## 8 反馈次数也由一次 BMS 计算决定

先证明链式反馈。设有 $(k;u_0,\ldots,u_M)$ 的实际 $M$ 段链，$c<u_0$，
见证 $Q_i:k\mapsto u_i\mapsto u_{i+1}$。每个 $Q_i$ 固定
$\gamma_0,\gamma_1$，且

$$
u_i=Q_i(k)<Q_i(b),\qquad Q_i(c)<Q_i(u_i)=u_{i+1}.\tag{8.1}
$$

所以封口低于 $u_i$ 的组，经过第 7.3 节的 $Q_i$-背景反馈，封口低于
$u_{i+1}$，高度应用一次 $T$。有限归纳 $M$ 次，输出高度
$T^{\circ M}(x)$。不同轮次使用不同链段和背景，不是在同一窗口无条件循环。

取第 7.1 节任意允许的 $h$。基础反馈先给高度 $T(h)$、封口 $C_1<c$ 的组。
置

$$
N=D(T(h)),\qquad m=\lfloor\log_2N\rfloor.
$$

由 (4.7)，$\gamma_{2^m}\le\gamma_N<C_1<c<S(b)$。将全局 Dougherty 链取
$S(P)$-像，接上 $S$-像的两段链，再保端点缩短，得到
$(k;S(a),Z)$ 的 $N$ 段链，其中

$$
Z=S(P)(\gamma_{2^m})<S(P)(C_1)<S(P)(S(b))=S(c)<\kappa_4.\tag{8.2}
$$

根仍为 $k$，因为 $S$ 固定它；起点 $S(a)>c>C_1$，故链式反馈可以执行。
从高度 $T(h)$ 的组出发，再执行 $N$ 轮，得到高度
$T^{\circ(N+1)}(h)$、封口低于 $Z<\kappa_4$ 的组。最后用 (4.7) 和 (2.1)：

$$
\boxed{q(5)>D\!\left(T^{\circ(D(T(h))+1)}(h)\right)
\quad(3\le h\le C_{\rm line}+2).}\tag{8.3}
$$

量词顺序为：先构造第一个输出组并确定有限整数 $D(T(h))$，再构造该长度的链，
最后作同样次数的有限归纳。没有循环定义链长，也没有预设最终输出的存在性。

## 第二部分 固定指标下降与 FGH

## 9 普通 BMS 的父表和辅助矩阵域

列号、行号均从 0 开始。$P_q(i)$ 表示第 $i$ 列第 $q$ 行的父项；
$p\prec_q i$ 表示沿这一行的父链，$p$ 是 $i$ 的非空祖先。
无父坐标为 0；有父坐标满足

$$
a_{i,q}=1+a_{P_q(i),q}.\tag{9.1}
$$

使用的规范父表域要求：父项向左，正坐标无支持空洞，较高行祖先也是较低行祖先，
且把 (9.1) 恢复出的数字矩阵交给原 BM4 逐行父搜索，恰好恢复所给父表。
这里不包括任意缺父的数字矩阵。标准式属于此域；原展开、下文的 $W$ 和
$\Sigma$ 均保持此域。辅助式不必从标准种子可达。

末列 $x$ 最高有父行为 $r$，控制父 $c=P_r(x)$，坏块宽 $d=x-c$。令

$$
\phi_b(i)=\begin{cases}i,&i<c,\\i+bd,&i\ge c.\end{cases}
$$

取原 $[n]$ 后，旧前缀不变；第 $b$ 份副本，$1\le b\le n$，其父为

$$
\begin{aligned}
P'_q(i+bd)&=\phi_b(P_q(i))&& (c<i<x),\\
P'_q(c+bd)&=\phi_{b-1}(P_q(x))&& (q<r),\\
P'_q(c+bd)&=P_q(c)&& (q\ge r).
\end{aligned}\tag{9.2}
$$

缺项仍为缺项。该公式是第 2 节引用的原 BMS 父表复制公式。
也可从递归父搜索核对：第一份副本的首列低坐标保持旧末列值，活动行及以上改为控制父值；
后续副本按 (9.2) 承接上一份的末列模板，非首列的相应父子子树一起搬运。
按行和块内列号归纳，得到 (9.2) 和 (9.1)，
同时保持规范性。

对每个 $M$，$M[0]$ 和 $M[1]$ 都是 $M[n]$ 的前缀，$n\ge1$。
非零末列的正指标展开不减少列数；零末列删除恰少一列。以下定量比较要用这些
**实际展开性质**，不使用一般的“序数更大，固定指标计算就更长”。

## 10 祖先覆盖的完整模拟与计数

### 10.1 定义与控制准备

称 $M$ 被 $N$ 祖先覆盖，指有严格递增列映射 $f$，把末列映到末列，且

$$
p\prec_q^M i\Longrightarrow f(p)\prec_q^N f(i).\tag{10.1}
$$

只检查源直接父边即可。目标可有额外列、边和高行；空源取空映射。

设源末列控制为 $(r,c)$。目标末列控制为 $(R,p)$。由覆盖 $R\ge r$。
定义一次准备操作：目标先取 $[1]$，再反复取 $[0]$ 截回原宽度。
前缀不变，新末列的数字为

$$
a'_x(q)=\begin{cases}a_x(q),&q<R,\\a_p(q),&q\ge R.\end{cases}\tag{10.2}
$$

这是非空真实下降，在第 $R$ 坐标严格降低，低坐标不变。末列坐标受固定前缀
及最初末列的有限最大值约束，故这个同宽操作不能无限执行。

若 $R>r$，它保持全部源末列所需低行祖先。若 $R=r$ 但 $p>f(c)$，
则 $f(c)\prec_r p$，新末列继承 $p$ 的第 $r$ 行祖先，仍保留
$f(c)$ 和更早的必要祖先。其他源列不变。于是只要目标控制不是
$(r,f(c))$，准备可以继续并保持覆盖。它不能先失去活动行，因为必须保留
$f(c)$。有限性遂保证最终到达

$$
(R,p)=(r,f(c)).\tag{10.3}
$$

### 10.2 同步复制

源删末列时，目标用 $[0]$ 截到倒数第二源列的映像；源删空则目标也截空。
否则先准备到 (10.3)，两边同步取同一正指标 $n$。设坏块宽分别为
$d_M=x-c$ 和 $d_N=f(x)-f(c)$。旧前缀保留映射；副本映射定义为

$$
f_n(i+bd_M)=f(i)+bd_N\quad(c\le i<x,\ 1\le b\le n).\tag{10.4}
$$

它严格递增。对 (9.2) 分三类核对覆盖：非首列连同原覆盖链一起搬运；
首列在 $q<r$ 时承接旧末列的父链，控制父是这些低行的祖先，故跨块链在相同
切点处接续；首列在 $q\ge r$ 时继承旧切点的祖先，而该切点已被 $f(c)$ 覆盖。
沿副本从左到右归纳，全部源父链都得到目标祖先链。最后若目标尚有未命中的尾列，
用 $[0]$ 截掉以恢复末列对齐；向左的边不受截尾影响。

因此源的每一步都由目标的非空有限下降模拟，而且目标只用指标 $0,1,n$。
这证明的是任意覆盖的模拟，不要求源和目标具有特殊共同生成历史。

### 10.3 将混合指标补足为固定指标

若 $P$ 是 $Q$ 的前缀，而 $Q$ 的固定 $[n]$ 轨道终止，$n\ge1$，
这条轨道必经过 $P$：每步保留删末列前缀，宽度至多减少一列，故不能跳过
$P$ 的宽度。在到达该宽度之前，$P$ 本身未被修改。

因为 $Q[0],Q[1]$ 是 $Q[n]$ 的前缀，任何只用 $0,1,n$ 的下降都是
固定 $[n]$ 轨道的子序列，每个真步骤占非空区间。若目标固定轨道终止，模拟说明
源固定轨道也终止，并有

$$
\boxed{d_n(M)\le d_n(N),\qquad s_M(n)\le s_N(n).}\tag{10.5}
$$

第二式还需一项计数：每个源零末列删除，在目标中截掉至少一列；正指标的非零
末列步骤不减少列数，所以对应区间至少含一次目标零末列删除。不同源步骤的区间
不重叠，故可以分别计入。

### 10.4 非标准辅助式也终止

记标准对角链

$$
\Delta_{k,m}=(0^k)(1^k)\cdots((m-1)^k)=B_{k+1}[m-1].\tag{10.6}
$$

每个高度至多 $k$、宽度至多 $m$ 的规范父表式，都被 $\Delta_{k,m}$
覆盖：任取末列对齐的严格递增列映射，目标每一行的任意较早列都是祖先。
标准 BMS 良序性保证目标下降终止，(10.5) 因而适用于这些非标准辅助式。
更一般地，逐步模拟排除它们的任何无限展开链。

特别地 $R_h$ 的固定下降终止；对 $H\ge h$，逐列恒等给出
$R_h$ 被 $R_H$ 覆盖，因此

$$
d_1(R_h)\le d_1(R_H),\qquad s_{R_h}(1)\le s_{R_H}(1).\tag{10.7}
$$

这补齐第 1、4、8 节所用的计数终止性，而不依赖 Laver 初始化。

## 11 行数换宽度

取 $k\ge2,m\ge3$。对 $\Delta_{k,m}$ 的末列执行 $m-2$ 次
“$[1]$ 后截回原宽度”，末列依次变为

$$
((m-1)^{k-1},m-2),\ldots,((m-1)^{k-1},1).
$$

此时最高行父为首列。再取一次 $[1]$，宽度变为 $2m-2$，
前 $k-1$ 行恰为完整对角链 $0,1,\ldots,2m-3$。由 (10.5) 得

$$
s_{\Delta_{k,m}}(1)\ge s_{\Delta_{k-1,2m-2}}(1).\tag{11.1}
$$

另一方面，$R_H[1]$ 是

$$
(0^H)(1^H)(1^{H-1},0)(2^{H-1},1).
$$

其第 0、2、3 列在前 $H-1$ 行覆盖 $\Delta_{H-1,3}$。从宽度 3
迭代 (11.1)，宽度递推为 $m\mapsto2m-2$，于是

$$
\boxed{s_{R_H}(1)\ge s_{\Delta_{H-1-u,\,2+2^u}}(1)
\quad(0\le u\le H-2).}\tag{11.2}
$$

由第 10.4 节，右侧还控制任意不超过该高度和宽度的规范辅助矩阵。

## 12 将 FGH 精确编译成 Hardy

对矩阵 $M$，定义 $W(M)$：加一个全零首列，原每列的第 0 坐标加 1，
其他坐标不变。不增加行数。父表写法是：先加空列，原空列变为 $[0]$，
原非空父列表 $[p_0,\ldots,p_r]$ 变为 $[p_0+1,\ldots,p_r+1]$。
这是规范父表，未宣称它是标准可达式。

对任何 $n\ge0$，有精确恒等式

$$
W(\varnothing)=Z,\qquad W(MZ)[n]=W(M)^{\frown(n+1)},\qquad
W(M)[n]=W(M[n])\quad(M\text{ 末列非零}).\tag{12.1}
$$

第二式中活动行为第 0 行，坏根是新加首列，留下原块再附加 $n$ 份。
第三式中原活动行不变，原父列号整体加 1；新增首列不会插入原非零坐标与其父之间。
第 0 坐标统一加 1 不改变原坏块差值和高行父搜索，(9.2) 因而逐项相同。
$n=0$ 时两边均是相应删尾，亦成立。

定义辅助 Hardy 计算

$$
\mathcal H_\varnothing(x)=x,\quad
\mathcal H_{MZ}(x)=\mathcal H_M(x+1),\quad
\mathcal H_M(x)=\mathcal H_{M[x]}(x)\quad(M\text{ 末列非零}).\tag{12.2}
$$

对标准 $M$ 作良基归纳，(12.1) 证明

$$
\boxed{\mathcal H_{W(M)}(x)=F_M(x),}\tag{12.3}
$$

并同时证明该辅助计算终止。空式和非零末列情形直接代入；若 $M=AZ$，
先产生 $x+1$ 份 $W(A)$。每份以零列开头，坏块不能跨过这个根，故依次独立执行，
每份将当前输入 $y$ 变为 $F_A(y)$，总结果正是 $F_A^{\circ(x+1)}(x)$。
这里没有预设所有非标准 Hardy 计算都终止。

## 13 一行森林控制参数增长

### 13.1 森林求值

一行规范矩阵是有限有序森林的先序深度列表。令

$$
V_q(\varnothing)=0,\quad V_q(FG)=V_q(F)+V_q(G),\quad
V_q(\operatorname{node}(F))=q^{V_q(F)}.
$$

固定原指标 $[n]$ 时，$s_F(n)=V_{n+1}(F)$。证明：删除零末列使
$V_{n+1}$ 减 1，非零末列展开保持它；后一断言在活动父节点处就是
$q^{a+1}=q\,q^a$，再代入外层指数和加法。终点求值为零，故计数等式成立。

记 $F_x$ 为深度 $0,1,\ldots,x$ 的单链森林，并设

$$
e_0=1,\qquad e_{x+1}=2^{e_x}.
$$

于是 $s_{F_x}(1)=e_x$。

### 13.2 对角行变换和根模板

$\Sigma(M)$ 表示添加一个零首列，再给原各列添加新的第 0 坐标
$1,2,\ldots,|M|$，原坐标移至高一行。若原第 $j$ 列父列表为 $C$，
新父列表为

$$
[j]\mathbin{{}^\frown}[p+1:p\in C].\tag{13.1}
$$

它增加一行，第 0 行成为完整祖先链，且保持规范性。

固定非零末列矩阵 $M$，原最高活动行 $r$、控制父 $p$。写

$$
\Sigma(M)=A B_0 C_0,\qquad d=|B_0|=|M|-1-p\ge1,\qquad R=r+1.
$$

$C_0$ 的第 0 行父为 $B_0$ 末列，第 $R$ 行父为 $B_0$ 首列，
所有有定义的父都在 $B_0$ 内，在 $R$ 以上无父；前一点由高行祖先也是低行祖先得到。
根模板 $C_b$ 保留这些内部父号，只把所在块换成当前长度 $d$ 的 $B_b$。

对任意有限一行森林 $F$，定义装饰 $E_b(F)$：每个森林根换成完整
$C_b$，非根只保留第 0 行父，指向对应森林父的映像；高行无父。
每个根的第 0 行父接在 $B_b$ 末列，非根按原规范森林向左接续；
根的高行父沿这条低行祖先链接回 $B_b$，故装饰仍是规范父表。
考虑状态

$$
\text{冻结前缀}\ B_bE_b(F).\tag{13.2}
$$

### 13.3 两种局部转移

若森林末点非根，目标末列只有第 0 行父，坏块始于其森林父，不进入 $B_b$。
由 (9.2)，一次固定 $[1]$ 恰把 $E_b(F)$ 变成 $E_b(F[1])$：
复制区内的森林父随副本移动，区外的固定；若复制区首点为森林根，其高父全在
$B_b$ 中，副本仍是同一根模板。$B_b$ 和冻结前缀不变。

若森林末点为根，目标末列是 $C_b$，控制父为 $B_b$ 首列，活动行为 $R$。
令 $F^-$ 删去末根。一次固定 $[1]$ 保留旧 $B_bE_b(F^-)$，并复制整个
这个块。副本头 $d$ 列成为 $B_{b+1}$，后面恰是 $E_{b+1}(F^-)$：
复制根的父原在 $B_b$ 中，故搬到新块；非根按森林父搬运。因此新活动状态为

$$
\text{更长的冻结前缀}\ B_{b+1}E_{b+1}(F^-).\tag{13.3}
$$

这两个转移各只使用一次目标 $[1]$。故活动森林的每次后继删除恰生成一份新坏块。

### 13.4 出生块的父边

当生成至 $B_b$ 时，选取原 $A$ 和 $B_0,\ldots,B_b$，跳过冻结森林列。
这些列与 $\Sigma(M[b])$ 有保持直接父的列映射。

对 $b$ 归纳。基础 $b=0$ 是删去旧末列。生成新块时，首列在 $R$ 以下
继承当前 $C_b$ 的父，故接到上一块内部的对应位置；在 $R$ 及以上继承
旧坏块首列的父，接回同一共享前缀。非首列的块内父随副本移动，块外父保留。
这正是 (9.2) 的下一份副本公式；第 0 行也接到上一坏块的末列。冻结森林步骤不修改
已选中的块，归纳成立。

运行活动森林到空时，当前 $B_b$ 末列也成为整个目标末列，所以映射为末列对齐的
祖先覆盖。新块总数为

$$
b=s_F(1).\tag{13.4}
$$

### 13.5 尾部参数链

取 $F=F_x$，初始装饰恰为 $\Sigma(MZ^x)$。由 (13.4)，其固定轨道经过
一个覆盖 $\Sigma(M[e_x])$ 的矩阵。对 $x\ge1$，有 $e_x\ge2x$：
$e_1=2$，归纳用 $2^{2x}\ge2(x+1)$。所以 $M[e_x]$ 在前缀 $M[x]$
之后至少多出 $(e_x-x)d\ge x$ 列。

$\Sigma(M[e_x])$ 又覆盖 $\Sigma(M[x]Z^x)$：前缀恒等，最后的 $x$
个参数列映到目标最后 $x$ 列；这些参数列仅要求第 0 行祖先，目标完整链提供
所有跨空隙关系。用 (10.5) 得

$$
\boxed{s_{\Sigma(MZ^x)}(1)\ge s_{\Sigma(M[x]Z^x)}(1)
\quad(x\ge1,\ M\text{ 末列非零}).}\tag{13.5}
$$

令 $K(M,x)=s_{\Sigma(MZ^x)}(1)$。Hardy 的后继步骤满足字面等式
$K(MZ,x)=K(M,x+1)$，极限步骤由 (13.5) 使 $K$ 不增。
因此任何从 $(M,x)$ 终止于 $(\varnothing,y)$ 的 Hardy 计算，$x\ge1$，均满足

$$
\boxed{s_{\Sigma(MZ^x)}(1)\ge s_{\Sigma(Z^y)}(1)=e_y.}\tag{13.6}
$$

$\Sigma(Z^y)$ 正是一行深度 $0,1,\ldots,y$ 的链。该式保留了塔函数余量，
不只得到较弱的下界 $y$。

## 14 强计数接口和逐轮缓冲

令 $\ell(x)=\lceil\log_2(x+2)\rceil$。对 $r,x\ge1$，矩阵

$$
P_{r,x}=\Sigma(W(B_r)Z^x)
$$

有 $r+1$ 行、$x+4$ 列。若 $h=r+2+\ell(x)$，在 (11.2) 取
$u=\ell(x)$，得到高度 $r+1$、宽度 $2+2^{\ell(x)}\ge x+4$ 的对角链，
因而覆盖 $P_{r,x}$。更大的 $h$ 用 (10.7) 处理。
结合 (12.3)、(13.6)：

$$
\begin{aligned}
D(h)&\ge s_{R_h}(1)\ge s_{P_{r,x}}(1)\\
&\ge e_{\mathcal H_{W(B_r)}(x)}=e_{F_{B_r}(x)}.
\end{aligned}
$$

于是得到第二部分的统一强接口

$$
\boxed{D(h)\ge e_{F_{B_r}(x)}
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}\tag{14.1}
$$

定义行数缓冲

$$
\rho(x)=x+3+\ell(x).
$$

对整数 $x\ge1$，在 (14.1) 取 $r=x+1$ 得

$$
h\ge\rho(x)\Longrightarrow D(h)\ge e_{F_\Lambda(x)}.\tag{14.2}
$$

对标准式作良基归纳，(1.1) 给出 $F_M(x)\ge x+1$。故 $x\ge2$ 时
$y=F_\Lambda(x)\ge3$。由 $2^y\ge y+2$ 得 $\ell(y)\le y$，从而
$\rho(y)\le2y+3$。另外

$$
e_y\ge2y+3\quad(y\ge3):
$$

基础是 $e_3=16\ge9$；归纳步为
$e_{y+1}=2^{e_y}\ge2e_y\ge4y+6\ge2(y+1)+3$。因此

$$
\boxed{h\ge\rho(x),\ x\ge2\Longrightarrow
D(h)\ge e_{F_\Lambda(x)},\quad T(h)\ge\rho(F_\Lambda(x)).}\tag{14.3}
$$

这一缓冲支付下一轮的全部对数项和加性常数。若只使用
$D(h)\ge F_\Lambda(x)$，不能直接作同样的迭代替换。

## 15 初始长链足以支付内层常数

把 (2.5) 的常数写成纯有限递归：

$$
\begin{aligned}
g(x)&=x2^x,&u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),&C_{\rm line}&=w(w(1)).
\end{aligned}\tag{15.1}
$$

确切性由 $m_k(2^x)=2^{u_k(x)}$ 归纳得到；$m_\omega,m_{\omega+1}$
在指数共轭下分别为 $v,w$，所以 $m_{\omega+2}(2)=2^{w(w(1))}$。
因此没有更换文献中的链长常数。

对 $x\ge1$，$g(x)\ge2x$，且

$$
g^{\circ2}(x)\ge g(2x)=2x2^{2x}\ge(x+1)2^{x+1}>F_2(x).
$$

这些函数严格递增，$g^{\circ3}(1)=2048>256$。由 (1.3)，

$$
t<g^{\circ514}(256)<g^{\circ517}(1).\tag{15.2}
$$

置 $b_0=g^{\circ258}(1)$。直接计算小步数得
$u_1(1)=8$，以及

$$
v(1)=u_2(1)=u_1(8)=g^{\circ256}(8)=b_0.
$$

对 $k$ 归纳，每个 $u_k$ 严格递增、大于恒等函数，且随 $k$ 不减；
增加输入同时增加初值及迭代次数。因此 $v,w$ 也满足相同输入性质。
于是

$$
\begin{aligned}
C_{\rm line}&>w(1)=v(b_0)=u_{2^{b_0}}(b_0)\\
&\ge u_1(b_0)=g^{\circ2^{b_0}}(b_0)
=g^{\circ(2^{b_0}+258)}(1)\\
&\ge g^{\circ519}(1)>g^{\circ2}(t)\ge4t.
\end{aligned}\tag{15.3}
$$

其中迭代次数比较只需 $b_0\ge2048$。$t\ge2$ 且 $\ell(t)\le t$，故

$$
\boxed{h_0=C_{\rm line}+2\ge t+3+\ell(t)=\rho(t).}\tag{15.4}
$$

不需要求 $D(3)$、$T(3)$ 的精确值，也不需要展开任何上述巨大整数的十进制表示。

## 16 合并得到主定理

令

$$
x_0=t,\quad x_{i+1}=F_\Lambda(x_i),\qquad h_i=T^{\circ i}(h_0).
$$

由 (15.4)、(14.3) 对自然数 $i$ 归纳，有

$$
h_i\ge\rho(x_i),\qquad D(h_i)\ge e_{x_{i+1}}.\tag{16.1}
$$

注意 $x_{i+1}\ge x_i+1$，因此这条具体迭代序列严格递增；不需假定一般
FGH 的下标单调性，甚至不需另证 $F_\Lambda$ 的输入单调性。

置 $N=D(h_1)=D(T(h_0))$。由 (16.1) 得

$$
N\ge e_{x_2}\ge x_2+1.\tag{16.2}
$$

第一部分 (8.3) 给出

$$
q(5)>D(h_{N+1})\ge e_{x_{N+2}}\ge x_{x_2+3}.\tag{16.3}
$$

最后一个不等式只用 $N+2\ge x_2+3$、$x_i$ 严格递增和 $e_y\ge y$。
按 (1.2)，

$$
x_{x_2+3}=F_\Lambda^{\circ(x_2+1)}(x_2)
=F_{\Lambda+1}(x_2),\qquad x_2=F_\Lambda(F_\Lambda(F_3(256))).
$$

代入 (16.3)，即得到

$$
\boxed{q(5)>F_{\Lambda+1}\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).}
$$

证毕。

## 17 证明范围与依赖核对

结论是在 ZFC + I3 下关于**特定有限整数**的纸面不等式，未声称已消去 I3。
它依赖第 2 节列出的文献定理；其余所需新引理的证明均在本文件中。

依赖次序为：第 9–13 节独立给出 BMS 终止与强计数接口；第 4–8 节在该终止性基础上
给出 Laver 端点预算和可变轮数反馈；第 14–16 节支付缓冲并合并。
第 10 节不使用 Laver 引理，故正文先陈列第一部分不会造成循环证明。

两处容易混淆的接口在本文中分别处理：零端口没有见证，所以第 4 节证明的是弱带
保持，而不是凭空套用完整 BLS；新输入链不一定为搬运像，所以第 7.3 节重新执行
环境代数中的全称插入归纳，而不假设存在逆像。

完整 IBLP、IBLP 030 的某个指定 FGH 值，以及“内部结构显著强于 BMS 的新记号”
均不在本定理的结论中。$\Lambda+1$ 的出现准确来自 (16.2) 支付了至少
$x_2+1$ 次 $F_\Lambda$ 迭代，并非只凭序型较大推断固定指标数值。
有限脚本仅作局部核验，不是本文任一全称命题的证明依据。

