# 将 linedness 统一转换为低端点 BMS 层数

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

在同一个 I3 嵌入生成的代数中，下面给出一个带参数的构造：
若有临界点为 $\kappa_2$、起点高于 $\theta_6$ 或等于
$\theta_6$ 的 $m$ 段 linedness，便能构造高度 $m+2$
的闭合 BMS 相容组，且封口严格低于这串 linedness 的终点。
这不是把互不相容的见证直接算作 BMS 层，而是逐层构造全部相容等式。

**最终应用更新：**本篇的统一插入引理已与一般输入的 FGH 计数接口接上，见
[周期三十二的 BMS 下界](<laver-period-32-BMS-bound.zh-CN.md>)。该应用直接使用
Qi 已发表的 $(\kappa_0,\kappa_1,\theta_5)$ 长链，不依赖本篇末尾较早的
标记初始化输入。以下大参数 $B$ 的记录保留为历史；同一下界也可从新的
更长链重新得到。公理条件仍为 I3，证明尚未 Lean 形式化。

结合本目录已有的保端点重定位，得到
$$
\boxed{q(5)>D_2(R_{B+2}),\qquad
B=g^{258}(1),\quad g(n)=n2^n,\quad
R_h=(0^h)(1^h)(1^h).}
\tag{1}
$$
其中 $q(5)$ 是普通二元 Laver 表首行周期首次达到 32 的阶参数，
$D_2$ 是父表新指标下反复取 $[2]$ 到空的次数，等于原 BM4
反复取 $[1]$ 的次数。式 (1) 还没有完成与
$F^{\mathrm{BMS}}_{B_{11}}(10)$ 的指定数值比较。

本篇的统一转换只使用应用恒等式、membership 截断、严格单调性和
[两层初始化](<short-terminal-initialization.zh-CN.md>)。式 (1) 的大参数
输入另使用[标记阶段前缀重定位](<marked-prefix-rebase.zh-CN.md>)。
因此其公理假设仍是 I3，没有将条件性的嵌入构造改称无条件算术证明。

## 记号与基础等式

所有嵌入都属于固定的 $\operatorname{Iter}(j)$。
$a(b)$ 表示 application，$a\circ b$ 才表示普通复合。
下文对一个复合词 $A=a_1\circ\cdots\circ a_t$，约定
$A(b)=a_1(a_2(\cdots(a_t(b))\cdots))$。它满足
$$
A(b(c))=A(b)(A(c)),\qquad A(b)(A(x))=A(b(x)).
\tag{2}
$$
这些由 LD 和应用的点像恒等式对词长归纳；并非从有限点像认同两个嵌入。

写 $a\equiv_\delta b$ 表示 membership 截断等价。使用：
$$
a(b)\equiv_{\operatorname{crit}(a)}b,
\qquad
a\equiv_\delta b\Longrightarrow
T(a)\equiv_{T(\delta)}T(b).
\tag{3}
$$
截断可以降低并取传递闭包。只有某一侧的输出**严格低于**截断点时，
才能由截断等价读取点像相等。

沿用两层初始化的 $K=j_{(11)}$、$\mu=\theta_4$ 和
\(\theta_0=\kappa_0,\theta_1=\kappa_1,
\theta_2=\kappa_2,\theta_3=\kappa_3\)。需要的文献等式是
$$
\begin{gathered}
K=j_{(10)}(j),\quad
\operatorname{crit}(j_{(10)})=\kappa_1,\quad
j_{(10)}(\kappa_1)=\kappa_2,\quad
j_{(10)}(\kappa_2)=\mu,\\
j_{(3)}(\kappa_0)=\kappa_2,\quad
j_{(3)}(\kappa_1)=\gamma_3,\quad
j_{(3)}(\kappa_2)=\kappa_3,\quad
K(\kappa_1)=\kappa_3,\\
K\equiv_{\gamma_3}j_{(3)},\qquad
\kappa_2<\gamma_3<\kappa_3.
\end{gathered}
\tag{4}
$$
最后一条截断等式来自
$K\equiv_\mu j\circ j$ 与
$j_{(3)}\equiv_{\gamma_3}j\circ j$，见
[Dougherty 第一篇第 5 节](https://arxiv.org/pdf/math/9205202)。

## 前端插入引理

设已有高度 $h$ 的闭合相容组：
$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1}<C,
$$
$$
\operatorname{crit}(K_i)=U_0,\qquad
K_i(U_t)=V_t\ (t\le i),\qquad K_i(V_0)=V_{i+1},
\tag{5}
$$
并有封口嵌入 $L:V_0\mapsto V_{h+1}\mapsto C$，其临界点为
$V_0$。设 $U_0=\kappa_0,U_1=\kappa_1$。

假设另有嵌入 $D$ 与点 $\delta$ 满足
$$
\begin{gathered}
\operatorname{crit}(D)=\kappa_0,\quad
D(\kappa_0)=V_0,\quad D(\kappa_1)=\delta,\quad D(V_0)=V_1,\\
V_0<\delta<V_1,\qquad K_i\equiv_\delta D\quad(1\le i\le h).
\end{gathered}
\tag{6}
$$
取任意临界点为 $\kappa_1$ 的嵌入 $T$，令
$v=T(D)(\kappa_1)$。新的源、目标与拥有者分别取
$$
\begin{aligned}
U'&=(\kappa_0,\kappa_1,T(U_1),\ldots,T(U_h)),\\
V'&=(T(V_0),v,T(V_1),\ldots,T(V_{h+1})),\\
K'&=(T(D),T(K_1),\ldots,T(K_h)).
\end{aligned}
\tag{7}
$$
封口取 $T(L)$，末端为 $T(C)$。

因为 $\kappa_0<\kappa_1<T(\kappa_1)$，由单调性和应用恒等式，
$$
T(V_0)<v<T(D)(T(\kappa_1))=T(\delta)<T(V_1).
\tag{8}
$$
搬运 (6) 的截断等式后，所有旧拥有者在新源点 $\kappa_1$
的像均为 $v$；读值的严格守卫正是 $v<T(\delta)$。
其余边由 (2) 直接搬运。新最低拥有者在首目标的像为
$T(D)(T(V_0))=T(V_1)$，故全部 (5) 成立。
封口的三点也由 (2) 搬运。

此外，新组全部拥有者在 $T(\delta)$ 以下与最低拥有者相等，
而新的第一个正目标 $v$ 严格低于该界。这条共同截断是下一次
插入所需的归纳不变量。

## 任意一段 linedness 提供的截断恒等式

设 $\operatorname{crit}(Q)=\kappa_2$，令
$$
T=Q(j_{(10)}),\qquad Z=Q(j_{(3)}).
$$
于是
$$
\operatorname{crit}(T)=\kappa_1,\qquad T(\kappa_1)=Q(\kappa_2).
\tag{9}
$$
由 $Q(j)\equiv_{\kappa_2}j$ 和 (4)，
$$
Q(K)=T(Q(j))\equiv_{T(\kappa_2)}T(j),\qquad
Q(K)\equiv_{Q(\gamma_3)}Z.
\tag{10}
$$
先命名 $T(j)(\kappa_1)$，由
$$
T(j)(\kappa_1)<T(j)(T(\kappa_1))=T(\kappa_2)
$$
可合法读取第一条截断。因此
$$
T(j)(\kappa_1)=Q(K)(\kappa_1)=Q(\kappa_3),
\quad Q(\gamma_3)<Q(\kappa_3)<T(\kappa_2).
\tag{11}
$$
降低第一条截断界后，与第二条合并得
$$
T(j)\equiv_{Q(\gamma_3)}Q(j_{(3)}).
\tag{12}
$$

若 $Q_*$ 为另一个临界点为 $\kappa_2$ 的嵌入，或为空复合，
则 $Q_*(j)\equiv_{\kappa_2}j$。所以对
$X=T(Q_*(j))$，同样有
$$
X\equiv_{Q(\gamma_3)}Z,\qquad X(\kappa_1)=Q(\kappa_3).
\tag{13}
$$
当 $Q_*$ 为空复合时，直接取 $X=T(j)$。

## 统一重建下一次插入所需的低拥有者

假设当前最低拥有者可写为
$$
K_1=A(j_{(3)}),\qquad A=P\circ T\circ Q_*,
\tag{14}
$$
其中 $T,Q,Q_*$ 如上一节，$P$ 是每个因子的临界点均大于
$\kappa_1$ 的复合词。因此 $P$ 固定 $\kappa_0,\kappa_1$。
当前组的最前两个源点为 $\kappa_0,\kappa_1$，且全部拥有者
在某个 $\varepsilon>V_1$ 以下与 $K_1$ 相等。

令
$$
Y=P(X)=A(j),\quad Z'=P(Z),\quad
b=P(Q(\kappa_2))=A(\kappa_1),\quad
\zeta=P(Q(\gamma_3)),\quad W=A(j_{(2)}).
\tag{15}
$$
应用恒等式给出
$$
\begin{aligned}
&\operatorname{crit}(Y)=\operatorname{crit}(Z')=\kappa_0,\\
&Y(\kappa_0)=Z'(\kappa_0)=b,\quad
Y(\kappa_1)=P(Q(\kappa_3)),\\
&Z'(\kappa_1)=\zeta,\quad
Z'(b)=P(Q(\kappa_3)),\quad
b<\zeta<Y(\kappa_1).
\end{aligned}
\tag{16}
$$
同时 $\operatorname{crit}(W)=b>\kappa_1$，且
$W(b)=A(\kappa_2)=V_0$。

定义
$$
D=W(Z'),\qquad \delta=W(\zeta).
\tag{17}
$$
因 $W$ 固定 $\kappa_0,\kappa_1$，(16) 给出
$$
\operatorname{crit}(D)=\kappa_0,\quad
D(\kappa_0)=V_0,\quad D(\kappa_1)=\delta,
$$
$$
D(V_0)=W(P(Q(\kappa_3)))=W(Y)(\kappa_1)=K_1(\kappa_1)=V_1.
\tag{18}
$$
由 (16) 严格单调地搬运，还得到 $V_0<\delta<V_1$。
搬运 (13) 两次则给
$$
K_1=W(Y)\equiv_\delta W(Z')=D.
$$
由于 $\delta<V_1<\varepsilon$，当前所有拥有者都与 $D$
在 $\delta$ 以下相等；故前端插入引理的全部条件满足。

再用下一个 $T'=Q'(j_{(10)})$ 插入，新最低拥有者为
$$
T'(D)=A'(j_{(3)}),\qquad
A'=P'\circ T'\circ Q,
$$
$$
P'=T'(W)\circ T'(P).
\tag{19}
$$
这里 $T'(P)$ 表示逐因子搬运。
每个新因子的临界点都大于 $\kappa_1$：旧因子及 $W$
的临界点大于 $\kappa_1$，再取 $T'$-像即可。
所以 (14) 的形式与共同截断不变量均保持，构造可继续任意指定的有限次数。

## 从两层组开始的归纳与端点界

取[两层初始化](<short-terminal-initialization.zh-CN.md>)的
$$
U=(\kappa_0,\kappa_1,\kappa_2),\quad
V=(\kappa_3,\theta_5,\alpha,\zeta_0),\quad
(K_1,K_2)=(f,J),\quad C_0=\rho<\theta_6.
$$
该处的 $e$ 满足
$$
\operatorname{crit}(e)=\kappa_2,\quad
e(\kappa_2)=\kappa_3,\quad e(\kappa_3)=\theta_5.
$$
第一次所需低拥有者及截断点取
$$
D_0=e(j_{(3)}),\qquad \delta_0=e(\gamma_3).
\tag{20}
$$
由 (4)，$D_0$ 满足 (6)。其中
$f=e(K)\equiv_{\delta_0}D_0$，而
$J=p(f)\equiv_{\operatorname{crit}(p)}f$，
$\delta_0<\theta_5<\operatorname{crit}(p)$。

现在给定一串长度为 $m$ 的 linedness：
$$
\operatorname{crit}(Q_r)=\kappa_2,\quad
Q_r(\kappa_2)=a_r,\quad Q_r(a_r)=a_{r+1},
\quad 0\le r<m,
\tag{21}
$$
其中 $a_0\ge\theta_6>\max(\mu,\rho)$。依次用
$T_r=Q_r(j_{(10)})$ 插入。

第一次插入后，最低拥有者为
$T_0(e(j_{(3)}))$，即 (14) 中
$P=T_0(e),T=T_0,Q_*$ 为空复合的情形。
因此上一节完成所有后续步骤。插入 $r$ 次的高度是 $r+2$。

若当前端点为 $C_r<a_r$，由 (4) 与 (21)，
$$
C_{r+1}=T_r(C_r)<T_r(a_r)
=Q_r(j_{(10)}(\kappa_2))=Q_r(\mu)
<Q_r(a_r)=a_{r+1}.
\tag{22}
$$
初始 $C_0=\rho<a_0$，所以对每个 $r\le m$ 都有
$C_r<a_r$。这证明了开头的统一转换定理。

## 十六段的有限输入与大参数输入

先给出一个不需要展开大参数的具体输入。
32 步标记启动和两次重定位后，已有八段
$$
(\kappa_0;\kappa_1=x_0<x_1<\cdots<x_8)
$$
及第二行拥有者 $G$，满足
$$
G(\kappa_0)=\kappa_1,\quad G(\kappa_1)=x_8,\quad
G(x_8)=y<\theta_6.
$$
八段的第一段仍是 $j:\kappa_0\mapsto\kappa_1\mapsto\kappa_2$。
将它用 $G$ 搬运，得到一段
$(\kappa_1;x_8,G(\kappa_2))$。因 $\kappa_2<x_8$，其末端小于
$y$。由 [Qi 引理 2.3](https://arxiv.org/html/2501.06733v5#S2)，
与原八段相乘得到十六段
$(\kappa_0;\kappa_1,\ldots,G(\kappa_2))$，终点低于 $\theta_6$。

令 $L_3$ 为三层初始化的独立封口，取应用项
$$
E=L_3(K).
$$
因为 $L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7$，有
$$
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,
\quad E(\theta_6)=L_3(\theta_5)<\theta_7<\kappa_4.
\tag{23}
$$
用 $E$ 搬运十六段，得到 (21)，且末端小于 $\theta_7$。
统一转换给出高度 18 的闭合组，封口低于 $\theta_7$。
由[带实现的删行计数](<ribbon-initialization.zh-CN.md>)，
$$
\boxed{q(5)>D_2(R_{18}).}
\tag{24}
$$

更一般地，[保端点重定位的明确重复块](<marked-prefix-rebase.zh-CN.md>)
给出 $(\kappa_0,\kappa_1,x)$ 的 $B=g^{258}(1)$ 段见证，
且 $x$ 严格低于未变的末端 $\Theta_0=\theta_6$。
用同一个 $E$ 搬运后，起点为 $\theta_6$，终点仍低于
$\theta_7$。把 $m=B$ 代入统一转换，便得到 (1)。
这里用的是对指定有限整数 $B$ 的归纳，不是把所有有限高度放到同一
端点下的无界构造；后者会与临界点集合的局部有限性冲突。

## 核验范围与剩余数值比较

十六段输入证书（历史参考：`high_start_lining_certificate.py`）保留实际应用项，
核验了 (21) 的具体见证和 (23) 的严格端点界。
统一插入证书（历史参考：`lined_front_fan_certificate.py`）按 (14)—(22) 生成有限实例，
检查所有源目标顺序、相容边、共同截断和封口。它有明确的时间、点数、
拥有者数和事实数上限；预算耗尽返回 UNKNOWN，不当作通过或反例。
这些程序是有限代数检查，不是 Lean 形式化；任意指定 $m$ 的结论来自
上述归纳证明。

本篇补上了“巨大 linedness 参数如何成为巨大 BMS 层数”的接口。
随后[森林控制器](<diagonal-forest-hardy-proof.zh-CN.md>)又补上固定下降与 FGH
的数值比较；任意行数的量词及整个 Laver 应用见开头的最终证明链接。
该比较并非只凭 $R_{18}>B_{11}$ 或层数极大作出。
