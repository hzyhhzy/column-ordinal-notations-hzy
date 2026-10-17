# 一个仍低于 q(5) 端点的高共同根长链

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本文证明一个有限嵌入代数引理，并将它接入已有的递归 corridor。
它解决了具体的端点资源问题；**没有因此宣布完成“内部结构实质超过 BMS”
的主目标**，也没有证明原先猜测的
$K(\theta_6)<j(\gamma_5)$ 或 $K(\theta_6)<j(\gamma_6)$。

关键是换掉搬运者：使用 $A=S(f)$，不再使用 $K(K)(f)$。
全篇在 ZFC + I3 下固定 $j:V_\lambda\to V_\lambda$，
所有拥有者均属于固定的 $\operatorname{Iter}(j)$。括号 $u(v)$ 表示 application；
普通复合另外写成 $u\circ v$。

## 1. 所用的既有有限事实及其来源

沿用
$$
K=j_{(11)},\qquad \mu=\theta_4,\qquad
\nu=j_{(9)}(\gamma_3),\qquad \theta_8=j_{(9)}(\kappa_3).
$$
这里 $\theta_i=\kappa_i$ 对 $0\le i\le3$ 成立；
$\kappa_2<\gamma_3<\kappa_3$。需要的严格次序是
$$
\kappa_3<\mu<\theta_5<\theta_6<\theta_7<\nu<\theta_8<\kappa_4.
\tag{1}
$$
$K(\theta_i)=\theta_{i+2}\;(0\le i\le5)$、
$j_{(9)}(\kappa_2)=\mu$、
$j_{(4)}:\kappa_2\mapsto\gamma_3\mapsto\kappa_3$，来自
[Dougherty I，第 5 节](https://arxiv.org/pdf/math/9205202) 的有限点像计算。
有关 $\theta_i$ 的同一组织方式也见
[Qi，第 5 节](https://arxiv.org/html/2501.06733v5#S5)。
严格比较 $\theta_7<\nu$ 的双截断推导已完整写在
[端点搬运文稿](<promoted-bms-feedback.zh-CN.md#比原有端点界更强的一条比较>)，
并非从 $\theta_7<\theta_8$ 猜出来的。

为明确 $f$ 的来源，定义实际项
$$
a_*=K(K),\quad b_*=K(j),\quad c_*=a_*(b_*),\quad
d_*=c_*(K),\quad e_*=d_*(j),\quad f=e_*(K).
\tag{2}
$$
仅用 application 恒等式 $u(v)(u\xi)=u(v\xi)$ 和固定性，得到
$$
\begin{aligned}
a_* &: \theta_2\mapsto\theta_4,\quad
       \theta_3\mapsto\theta_5,\quad
       \theta_4\mapsto\theta_6,\quad
       \theta_5\mapsto\theta_7,\\
b_* &: \theta_2\mapsto\theta_3\mapsto\theta_4\mapsto\theta_5,\\
c_* &: \theta_4\mapsto\theta_5\mapsto\theta_6\mapsto\theta_7,\\
d_* &: \theta_0\mapsto\theta_2,\quad
       \theta_1\mapsto\theta_3,\quad
       \theta_2\mapsto\theta_5,\quad
       \theta_3\mapsto\theta_6,\\
e_* &: \theta_2\mapsto\theta_3\mapsto\theta_5\mapsto\theta_6.
\end{aligned}
\tag{3}
$$
例如 $d_*(\theta_3)=c_*(K(\theta_3))=c_*(\theta_5)=\theta_6$，
因为 $c_*$ 固定 $\theta_3<\operatorname{crit}(c_*)=\theta_4$。
$e_*$ 的临界点是 $\theta_2$，故固定 $\theta_0,\theta_1$。所以
$$
\boxed{f(\kappa_0)=\kappa_3,\qquad
f(\kappa_1)=\theta_5,\qquad f(\theta_5)=\theta_6.}
\tag{4}
$$
最后一式特别要用 $\theta_5=e_*(\theta_3)$：
$$
f(\theta_5)=e_*(K)(e_*(\theta_3))
=e_*(K(\theta_3))=e_*(\theta_5)=\theta_6.
$$

令
$$
S=j_{(9)}(j_{(4)}).
$$
上述真实点像给出
$$
\operatorname{crit}(S)=\mu,\qquad S(\mu)=\nu,\qquad S(\nu)=\theta_8.
\tag{5}
$$
于是 $S$ 固定 $\kappa_0,\kappa_1,\kappa_2,\kappa_3$，而
$$
\theta_7<\nu<S(\theta_5)<S(\theta_6)<S(\theta_7)<\theta_8<\kappa_4.
\tag{6}
$$
其中首个像的下界来自 $\mu<\theta_5$，最后一个像的上界来自
$\theta_7<\nu$。另外 $\theta_5<S(\theta_5)$，
因为已有 $S(\theta_5)>\nu>\theta_5$，不需要额外调用“所有临界点都会被移动”。

## 2. 短搬运引理

取
$$
A=S(f),\qquad Z=A(\theta_5),\qquad u_0=S(\theta_5).
\tag{7}
$$
因为 $S$ 固定 $\kappa_0,\kappa_1,\kappa_3$，由 (4) 得
$$
A(\kappa_0)=\kappa_3,\qquad A(\kappa_1)=u_0.
\tag{8}
$$
又由严格单调性和 $\theta_5<S(\theta_5)$，
$$
\boxed{Z=A(\theta_5)<A(S(\theta_5))
=S(f(\theta_5))=S(\theta_6)<\kappa_4.}
\tag{9}
$$
这里不曾把 $A(\theta_5)$ 错写成 $S(f(\theta_5))$：两者是严格小于关系。
此外 $\kappa_1<\theta_5$ 给出
$$
u_0=A(\kappa_1)<A(\theta_5)=Z.
\tag{10}
$$

因此，**对任意实际 $M$-lined 链 $(\kappa_0;\kappa_1,\ldots,\theta_5)$**，
逐点、逐拥有者取 $A$-像，得到实际 $M$-lined 链
$$
\boxed{(\kappa_3;S(\theta_5),\ldots,Z),\qquad
\theta_7<S(\theta_5)<Z<S(\theta_6)<\theta_8<\kappa_4.}
\tag{11}
$$
此量词只搬运已经存在的一条有限链，不假定任意长度的原链。

还有一个更一般的窗口结论：
$$
x<u_0=S(\theta_5)\quad\Longrightarrow\quad A(x)<S(a).
\tag{11a}
$$
这是因为 $A(u_0)=S(a)$。这里的输入上界是 $u_0$，不是仅仅 $\theta_5$。

## 3. 已发表的大链输入

用 $C_{\rm line}$ 记此前调用的实际大链长度：
$$
(\kappa_0;\kappa_1,\ldots,\theta_5)
\quad\text{是 }C_{\rm line}\text{-lined}.
\tag{12}
$$
它是 [Qi 的 Proposition 1.3(1)、Theorem 2.25 与 Lemma 3.3](https://arxiv.org/html/2501.06733v5)
所给的有限实际嵌入见证，本文沿用其常数约定
$2^{C_{\rm line}}=m_{\omega+2}(2)$。证明 (11) 不依赖如何估计这个常数。
特别不能用“$\theta_5$ 以下有很多临界点”替代 (12) 的 lined 性质。

将 (12) 代入 (11)，共同根为 $\kappa_3$，而原始反馈模板使用
$$
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7.
$$
所以
$$
k<\kappa_3<a<c<u_0.
\tag{13}
$$
这恰好闭合了
[递归 corridor 的高共同根条件](<small-period-recursive-corridor.zh-CN.md#2-一条提高了共同根的长链可支持可变深度升级>)，
并且不需要转到 $q(6)$ 或 $q(7)$。

## 4. 接入递归模板的精确结论

令 $D(h)$ 为原 BM4 对 $(0^h)(1^h)(1^h)$ 反复取 $[1]$ 到空的总次数，
$T(h)=D(h)+2$，并递归定义
$$
F_0=T,\qquad
F_{i+1}(h)=F_i^{\circ(D(F_i(h))+1)}(h).
\tag{14}
$$
设 (11) 的各段拥有者为
$H_i:\kappa_3\mapsto u_i\mapsto u_{i+1}$，
$0\le i<C_{\rm line}$。因为
$\kappa_2<\kappa_3<\theta_6$ 且 $c<u_i$，
$$
H_i\text{ 固定 }\kappa_0,\kappa_1,k,\qquad
H_i(a)>u_i,\qquad H_i(c)<u_{i+1}.
\tag{15}
$$
按已有递归模板引理归纳，每个 $F_i$ 都有入口 $b$ 的自然实现，
第 $i+1$ 个出口可取 $H_i(c)<u_{i+1}$。于是对已有入口封口低于 $b$
的高度 $h\ge3$ 的 fan，得到高度 $F_{C_{\rm line}}(h)$、封口低于
$Z<\kappa_4=j(\gamma_4)$ 的 fan。带计数给出
$$
q(5)>D(F_{C_{\rm line}}(h)).
\tag{16}
$$

还可以**明确地再升级一次**。前一出口低于 $Z<S(a)$，且 $S$ 固定
$\kappa_0,\kappa_1,k$、$S(c)<\kappa_4$。故再以 $H=S$ 使用一次同一引理，得到
$$
\boxed{q(5)>D(F_{C_{\rm line}+1}(h)).}
\tag{17}
$$
这仍只对已有入口 fan 所支持的 $h$ 声明；没有假定任意自然数高度都能在同一入口下初始化。

### 4.1 链长也可以从已有 fan 的计算产生

由 (11a)，链长不必锁死为 $C_{\rm line}$。若已有高度 $y$、封口
$C<u_0$ 的 fan，令
$$
N=D(y),\qquad m=\lfloor\log_2N\rfloor.
$$
全局带计数给出 $\gamma_{2^m}\le\gamma_N<C<u_0$。
Dougherty 的实际 $m$-lined 链
$(\gamma_0;\gamma_1,\ldots,\gamma_{2^m})$ 取 $A$-像后，得到
$$
(\kappa_3;u_0,\ldots,A(\gamma_{2^m})),\qquad
A(\gamma_{2^m})<A(C)<S(a).
\tag{18}
$$
这里没有额外的降根乘链，因此长度是 $m$，不能把它直接写成 $N$。

例如从高度 $h$ 的入口 fan 先执行一次 $T$，得到高度 $T(h)$、
封口低于 $c<u_0$ 的 fan。取
$$
m(h)=\lfloor\log_2 D(T(h))\rfloor.
$$
使用 (18) 支持 (14) 的 $m(h)$ 层模板升级，再用 $S$ 升级一次，可得
$$
\boxed{q(5)>D(F_{m(h)+1}(h)).}
\tag{19}
$$
用于产生链的那份 fan 和用于执行新模板的初始 fan 可以保留为两个有限见证；
不需要倒转一次 $T$，也没有让链长依赖最后输出。

量词顺序是：先做已有的有限 $T(h)$ 构造及其 $D$ 计数，得到有限 $m(h)$；
再构造 (18) 的有限链；随后对自然模板作 $m(h)+1$ 次有限归纳；
最后将所得模板用于原输入 fan。仍然没有提供一个固定端点下任意长的无限共同见证。
搬运整个有限背景时，(11a) 变成
$x<Q(u_0)\Rightarrow Q(A)(x)<Q(S(a))$，
因此这个参数化过程也保持所需的整背景自然性。

## 5. 结论边界

已完成的是一条**具体实际大链在 $q(5)$ 窗口内的严格端点证明**，
以及将它接入既有自然模板的有限归纳。(11) 的每段拥有者都可以供后续内部结构构造使用。
本文没有把 $D$ 黑盒的可变深度递归等同于某个已建立的超 BMS 序数记号；
没有从有限 $C_{\rm line}$ 偷渡出一个固定窗口内任意长的链；
也不声称 $K(\theta_6)$ 的旧候选上界已被证明或证伪。

有限接口核验见 small_period_sf_endpoint_certificate.py（历史参考：`small_period_sf_endpoint_certificate.py`）。
它只验证 (7)—(11) 的点像与严格次序，不运行 $D$、不物化 $C_{\rm line}$ 条边。
