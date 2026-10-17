# 三行 BMS 种子的低端点实现

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

在 I3 假设下，普通 Laver 表第一行周期首次达到 32 的阶参数满足
$$
q(5)>D_2(R_3),\qquad R_3=(000)(111)(111).
\tag{1}
$$
这里括号是 BMS 的列；$D_2$ 是父表表示反复作新 $[2]$ 到空的次数，即原 BM4 反复作 $[1]$ 的次数。$q(N)$ 与 BMS 下标沿用研究总览（历史参考：`README.zh-CN.md`）。

式 (1) 由本篇的有限初始化和[带实现的保持性及删行计数](<ribbon-initialization.zh-CN.md>)组成。不是用有限下降测试推断下界。它尚未达到十一行的 BMS[10] 目标，也没有将 $D_2$ 换算为指定的 FGH 值。

## 重复一列的种子与较弱的初始化条件

记
$$
B_h=(0^h)(1^h),\quad S_h=(0^h)(1^h)(2^h),\quad
P_h=(0^h)(1^h)(2,0^{h-1}),\quad R_h=(0^h)(1^h)(1^h).
$$
父表中 $P_h=((),0^h,(1))$，$R_h=((),0^h,0^h)$。直接展开给出
$$
P_h[2]=R_h,\qquad D_2(P_h)=1+D_2(R_h).
\tag{2}
$$
这些是标准后代，而不是任意非标准矩阵。从 $S_h$ 作
$h(h+1)/2-1$ 次新 $[1]$ 就得到 $P_h$：当末父列为 $1^a$ 时，一步变成
$1^{a-1}0^{h-a+1}$，再作 $h-a+1$ 步便成为 $1^{a-1}$。对 $a=h,\ldots,2$ 求和即得上述次数。新 $[1]$ 是原正展开的一个前缀，因而保留标准性。又有
$$
B_h<R_h<P_h\le S_h<B_{h+1}.
\tag{3}
$$
整个 $R_h$ 族共尾于 BMS 极限。式 (3) 只是序位关系，不蕴含某一给定 FGH 数值的大小。

采用[相容映射组](<ribbon-initialization.zh-CN.md>)的记号：
$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1},
$$
$$
\operatorname{crit}(K_k)=U_0,\quad
K_k(U_i)=V_i\ (0\le i\le k),\quad K_k(V_0)=V_{k+1}.
\tag{4}
$$
只需再找一个嵌入 $L$，满足
$$
\operatorname{crit}(L)=V_0,\qquad L(V_0)=V_{h+1}.
\tag{5}
$$
则 $R_h$ 有末端为 $L(V_{h+1})$ 的带实现。

证明取三个列带分别为 $U_i$、$V_i$、$L(V_i)$，其中 $0\le i\le h$，总末端是 $L(V_{h+1})$。第一正列由 $K_k$ 实现；第二正列由 $L(K_k)$ 实现。由于 $L$ 固定全部 $U_i$，应用恒等式给出
$$
L(K_k)(U_i)=L(V_i),\qquad
L(K_k)(L(V_0))=L(V_{k+1}).
$$
两列的父都是零列，恰好实现 $R_h$。源列不需要正端口见证。证毕。

相比用最高 $K_h$ 的第三临界像作为末端，(5) 允许独立选择 $L$，因此是较弱的初始化条件。若 $h\ge3$ 且
$$
L(V_{h+1})\le j(\gamma_{N-1}),
$$
删行计数立即给出 $D_2(R_h)<q(N)$。

## 使用的文献点像

固定 I3 嵌入 $j$，所有以下项都在同一个 $\operatorname{Iter}(j)$ 中。应用写作 $a(b)$，不能读成函数复合。令 $K=j_{(11)}$，并取
$$
(\theta_0,\ldots,\theta_8)=
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,
j_{(7)}(\kappa_2),j_{(11)}(\kappa_3),j_{(10)}(\kappa_3),
j_{(11)}(j_{(11)}(\kappa_3)),j_{(9)}(\kappa_3)).
$$
所需文献事实是
$$
\theta_0<\cdots<\theta_8<\kappa_4,\quad
K(\theta_i)=\theta_{i+2}\quad(0\le i\le5),
\tag{6}
$$
以及
$$
\theta_2<\gamma_3<\theta_3=\gamma_4,\qquad
\operatorname{crit}(j_{(8)})=\gamma_3,\quad
j_{(8)}(\gamma_3)=\theta_3,\quad j_{(8)}(\theta_3)=\theta_4.
\tag{7}
$$
(6) 见 [Qi 第 5 节](https://arxiv.org/html/2501.06733v5#S5)；(7) 见 [Dougherty 第一篇第 5 节表 2](https://arxiv.org/pdf/math/9205202)。还使用 $j(\theta_i)=\theta_{i+1}$ 对 $0\le i\le2$ 成立，及 $j(\theta_3)=\kappa_4$。

下面各等式只从这些输入、低于临界点的固定性和
$$
a(b)(a(x))=a(b(x)),\qquad
\operatorname{crit}(a(b))=a(\operatorname{crit}(b))
\tag{8}
$$
推导。

## 显式的两层组

依次定义
$$
a=K(K),\ b=K(j),\ c=a(b),\ d=c(K),\ e=d(j),\
f=e(K),\ g=f(K),\ r=g(f),\ p=f(b),\ s=r(d),\
J=p(f),\ L_2=s(g).
\tag{9}
$$
先由 (8) 得到
$$
\begin{aligned}
a &: (\theta_2,\theta_3,\theta_4,\theta_5)
       \mapsto(\theta_4,\theta_5,\theta_6,\theta_7),\\
b &: (\theta_2,\theta_3,\theta_4)\mapsto(\theta_3,\theta_4,\theta_5),\\
c &: (\theta_4,\theta_5,\theta_6)\mapsto(\theta_5,\theta_6,\theta_7),\\
d &: (\theta_0,\theta_1,\theta_2,\theta_3)
       \mapsto(\theta_2,\theta_3,\theta_5,\theta_6),\\
e &: (\theta_2,\theta_3,\theta_5)\mapsto(\theta_3,\theta_5,\theta_6).
\end{aligned}
$$
定义点
$$
\alpha=e(\theta_4),\quad\beta=f(\theta_2),\quad
\zeta=f(\theta_4),\quad\eta=r(\theta_3),\quad\rho=r(\theta_5).
$$
逐次用严格单调性得到
$$
\theta_5<\beta<\alpha<\zeta<\eta<\rho<\theta_6.
\tag{10}
$$
所需点像为
$$
\begin{aligned}
f &: (\theta_0,\theta_1,\theta_3,\theta_5)
        \mapsto(\theta_3,\theta_5,\alpha,\theta_6),\\
g &: (\theta_3,\theta_5,\beta,\alpha)
        \mapsto(\beta,\alpha,\zeta,\theta_6),\\
r &: (\theta_0,\theta_1,\theta_2,\beta)
        \mapsto(\beta,\alpha,\zeta,\theta_6),\\
p &: (\beta,\alpha,\zeta)\mapsto(\alpha,\zeta,\theta_6),\\
s &: (\beta,\alpha,\zeta)\mapsto(\zeta,\eta,\rho),\\
J &: (\theta_0,\theta_1,\theta_2,\theta_3,\theta_4)
        \mapsto(\theta_3,\theta_5,\alpha,\zeta,\theta_6).
\end{aligned}
\tag{11}
$$
这里一行内输入不必按大小排列，例如 $g$ 那一行只罗列四个对应等式。

$f,J$ 的临界点都是 $\theta_0$，而
$$
\operatorname{crit}(L_2)=\theta_3,\qquad
L_2(\theta_3)=\zeta,\qquad L_2(\zeta)=\rho.
$$
因此
$$
U=(\theta_0,\theta_1,\theta_2),\quad
V=(\theta_3,\theta_5,\alpha,\zeta),\quad
(K_1,K_2)=(f,J)
$$
满足 (4)，并有满足 (5) 的 $L_2$。

## 第三层与独立的末端见证

令
$$
\delta=J(\gamma_3),\quad H=J(j_{(8)}),\quad J_3=H(J).
$$
由 (7) 和 (11)，
$$
\alpha<\delta<\zeta,\quad
\operatorname{crit}(H)=\delta,\quad H(\delta)=\zeta,\quad H(\zeta)=\theta_6.
$$
故 $H$ 固定 $\theta_0,\theta_1,\theta_2,\gamma_3,\theta_3,\theta_5,\alpha$，从而
$$
J_3:(\theta_0,\theta_1,\theta_2,\gamma_3,\theta_3)
       \mapsto(\theta_3,\theta_5,\alpha,\zeta,\theta_6).
\tag{12}
$$

再令
$$
A=c(d),\qquad L_3=A(j(j)).
$$
由前述 $c,d$ 点像与固定性，
$$
A:(\theta_1,\theta_2,\theta_3)\mapsto(\theta_3,\theta_6,\theta_7).
$$
由于 $j(j)$ 的临界序列始于
$\theta_1\mapsto\theta_2\mapsto\theta_3$，所以
$$
\operatorname{crit}(L_3)=\theta_3,\quad
L_3(\theta_3)=\theta_6,\quad L_3(\theta_6)=\theta_7.
\tag{13}
$$
于是得到完整三层初始化
$$
U=(\gamma_0,\gamma_1,\gamma_2,\gamma_3),\quad
V=(\theta_3,\theta_5,\alpha,\zeta,\theta_6),\quad
(K_1,K_2,K_3)=(f,J,J_3),\quad L=L_3.
$$
末端是 $\theta_7<\kappa_4=j(\gamma_4)$。将 $h=3,N=5$ 代入初始化引理，得到 (1)。

独立代数核验程序（历史参考：`three_row_certificate.py`）只载入 (6)–(7) 与 $j$ 的基本点像，然后核验 17 个派生应用项和全部相容关系。程序没有导入 M 历史搜索；它核验的是有限代数推导，不是 Lean 形式化，也不重新证明文献输入。

## 保留周期端点而扩大源点区间

上面的源点用尽了 $\gamma_4$ 以下四个临界点，因此不能保持 $V_0=\gamma_4$ 继续向源列尾部加点。下面可以消除这个位置限制，但尚未给出额外八层见证。

令
$$
T=j_{(9)}(j_{(15)}),\qquad Q=j_{(9)}(j_{(14)}).
$$
[Dougherty 第一篇第 5 节末段](https://arxiv.org/pdf/math/9205202)证明
$$
Q(T(T(\theta_6)))<\kappa_4.
\tag{14}
$$
表 2 与应用恒等式又给出
$\operatorname{crit}(T)=\gamma_1$、$T(\gamma_1)=\theta_8$。
由于
$$
\theta_7<\theta_8=T(\gamma_1)<T(\theta_6),
$$
有
$$
T(\theta_7)<T(T(\theta_6))\le Q(T(T(\theta_6)))<\kappa_4.
\tag{15}
$$
把上面的全部点与嵌入统一经 $T$ 搬运，仍是末端低于 $\kappa_4$ 的三层组。

现在令 $B=T(j_{(7)})$。表 2 给出
$j_{(7)}(\gamma_0)=\gamma_3$、$j_{(7)}(\gamma_1)=\gamma_4$，故
$$
B(\gamma_0)=T(\gamma_3),\qquad B(\theta_8)=T(\gamma_4).
$$
又因 $\gamma_8<\theta_8$，严格单调性给出八个明确的候选源点
$$
T(\gamma_3)<B(\gamma_1)<\cdots<B(\gamma_8)<T(\gamma_4).
\tag{16}
$$
这些点都属于同一 $\operatorname{Iter}(j)$ 的临界点集合。它们只解决源点的位置问题；仍需构造相容的额外行嵌入及保界末端见证，不能据此宣称已有十一层初始化。

## 带独立末端见证的升层条件

(5) 的独立见证可以随升层一起搬运。设已有高度 $h$ 的组和 $L$，记
$$
J=K_h,\quad S=V_{h+1}=J(V_0),\quad C=L(S).
$$
选取 $U_h<u<V_0$，令 $\beta=J(u)$。若嵌入 $H$ 满足
$$
\operatorname{crit}(H)=\beta,\qquad H(\beta)=S,
\tag{17}
$$
则用 $H(J)$ 作为新的最高行嵌入，增加源点 $u$、目标点 $H(S)$，并把末端见证改为 $L'=H(L)$。

因为 $\beta>V_h\ge V_0$，$H$ 固定旧源点及 $V_0,\ldots,V_h$。式 (8) 给出全部新相容关系，同时
$$
\operatorname{crit}(L')=V_0,\quad
L'(V_0)=H(S),\quad L'(H(S))=H(C).
\tag{18}
$$
因此只需再控制 $H(C)\le\Theta$，就完成一次保界升层。这里的 $C$ 是独立见证的第二临界像，不再强制等于 $J^{\circ3}(U_0)$。

对 (16) 的八个点，(17)–(18) 是接下来所需的具体条件。它们尚未全部得到。即使得到十一层，还需另证相应下降长度超过指定 $F^{\rm BMS}_{B_{11}}(10)$；种子序位更大不能代替这个数值比较。

