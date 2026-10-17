# 一个有实际拥有者的 native／mark 种子

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。在 ZFC + I3 下，固定原来的 $\operatorname{Iter}(j)$。
这里给出明确有限 application 项 $H$，满足
$$
\operatorname{crit}(H)=\kappa_0,\quad
H(\kappa_0)=t>\kappa_3,\quad H(\kappa_2)=v,\quad H(t)=E<\kappa_4.
\tag{1}
$$
它不是把这些等式当作新假设，也不需要搜索某个合适的拥有者。
这个 $H$ 已经出现在原三行初始化中：它正是原来的 $r_*$。

## 1. 实际有限项

设 $K=j_{(11)}$，并沿用
$$
\theta_0=\kappa_0,\quad\theta_1=\kappa_1,\quad
\theta_2=\kappa_2,\quad\theta_3=\kappa_3,
$$
$$
\kappa_3<\mu=\theta_4<\theta_5<\theta_6<\theta_7<\kappa_4,
\qquad K(\theta_i)=\theta_{i+2}\quad(0\le i\le5).
\tag{2}
$$
这是既有的有限 $j,K$ 初始化。定义
$$
a_*=K(K),\quad b_*=K(j),\quad c_*=a_*(b_*),\quad
d_*=c_*(K),\quad e_*=d_*(j),\quad f=e_*(K),
$$
$$
\boxed{g=f(K),\qquad H=g(f).}
\tag{3}
$$
全篇括号都是 application，不是普通复合。其临界点由
$\operatorname{crit}(u(v))=u(\operatorname{crit}(v))$ 计算。

此前有限推导给出
$$
\operatorname{crit}(e_*)=\kappa_2,\qquad
e_*(\kappa_2)=\kappa_3,\quad
e_*(\kappa_3)=\theta_5,\quad e_*(\theta_5)=\theta_6,
\tag{4}
$$
以及
$$
\operatorname{crit}(f)=\kappa_0,\qquad
f(\kappa_0)=\kappa_3,\quad f(\kappa_1)=\theta_5,
\quad f(\theta_5)=\theta_6.
\tag{5}
$$
(4)—(5) 的逐项推导已在
[短搬运引理第 1 节](<small-period-endpoint-Sf.zh-CN.md#1-所用的既有有限事实及其来源>)
完整列出；它们只用 (2)、application 点像恒等式及固定性。

定义三个命名临界点
$$
\alpha=e_*(\mu),\qquad \beta=f(\kappa_2),\qquad \zeta=f(\mu).
\tag{6}
$$
因为 $\kappa_3=e_*(\kappa_2)$，
$$
f(\kappa_3)=e_*(K)(e_*(\kappa_2))
=e_*(K(\kappa_2))=e_*(\mu)=\alpha.
\tag{7}
$$
由严格单调性，
$$
\boxed{\kappa_3<\theta_5<\beta<\alpha<\zeta<\theta_6<\kappa_4.}
\tag{8}
$$
具体而言，$\kappa_1<\kappa_2<\kappa_3$ 的 $f$-像给出
$\theta_5<\beta<\alpha$，而 $\kappa_3<\mu<\theta_5$ 的 $f$-像给出
$\alpha<\zeta<\theta_6$。这些点都是同一个环境代数中的真实临界点，
不是仅仅为了让图样有序而随意命名的序数。

## 2. H 的全部必要点像

首先 $\operatorname{crit}(g)=f(\kappa_0)=\kappa_3$，所以 $g$ 固定
$\kappa_0,\kappa_1,\kappa_2$。由 application 恒等式，
$$
\begin{aligned}
g(\kappa_3)&=g(f(\kappa_0))=f(K(\kappa_0))=f(\kappa_2)=\beta,\\
g(\theta_5)&=g(f(\kappa_1))=f(K(\kappa_1))=f(\kappa_3)=\alpha,\\
g(\beta)&=g(f(\kappa_2))=f(K(\kappa_2))=f(\mu)=\zeta,\\
g(\alpha)&=g(f(\kappa_3))=f(K(\kappa_3))=f(\theta_5)=\theta_6.
\end{aligned}
\tag{9}
$$
因 $H=g(f)$，
$$
\operatorname{crit}(H)=g(\kappa_0)=\kappa_0.
$$
将 $g$ 固定的三个低点分别代入，得到
$$
\begin{aligned}
H(\kappa_0)&=g(f(\kappa_0))=g(\kappa_3)=\beta,\\
H(\kappa_1)&=g(f(\kappa_1))=g(\theta_5)=\alpha,\\
H(\kappa_2)&=g(f(\kappa_2))=g(\beta)=\zeta.
\end{aligned}
\tag{10}
$$
最后 $\beta=g(\kappa_3)$，故
$$
H(\beta)=g(f)(g(\kappa_3))=g(f(\kappa_3))=g(\alpha)=\theta_6.
\tag{11}
$$
所以取
$$
\boxed{t=\beta,\qquad v=\zeta,\qquad E=\theta_6}
\tag{12}
$$
就满足 (1)，并额外获得 $H(\kappa_1)=\alpha\in(t,v)$。

## 3. 对目标种子的精确接口

命名点表取
$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,t,v,E),
$$
地址分别为 $0,1,2,3,4,5,6$。同一个 $H$ 实现：

- core $(0,2,4)$、步长 $2$、隐含端点 $5$：关系为
  $H(\kappa_0)=t$、$H(\kappa_2)=v$；
- core $(0,2,4,5)$、步长 $2$、隐含端点 $6$：再加
  $H(t)=E$。

因此这两行的共享接缝由真正相同的拥有者实现，不是只依赖有限点像相似。
若 native 操作确实要求插入源 $\kappa_1$ 的对应像，则该像恰为
$\alpha$，且已有严格位置 $t<\alpha<v$。插值后的单桥行
$$
(\kappa_0,\kappa_1,\kappa_2,t,\alpha,v),\qquad L=3,
\quad\text{隐含端点 }E
$$
仍由 $H$ 实现，因为其四条配对恰是 (10)—(11)。

此处先完成所需拥有者及单桥点像接口。下一小节补齐第 3 行的真实 owner；
但实际 native／mark guard 是否恰好选择这份源包、插入后其余各行的隐含端点是否保持，
仍须由调用者按完整状态规则另行核对。本篇不把这些未在此检查的语法条件包装成已证。

### 3.1 补齐原先无主的第 3 行

上述具体点表的第 3 行是 core $(0,3)$、步长 $1$、隐含端点 $4$。
只将它当作无主零行并不适合后续复制：若复制把其首地址 $0$ 送到正地址，
新行就需要真实拥有者。这里可以明确补齐，而不改变点表或其他行。

记 $j_{(2)}=j(j)$、$j_{(3)}=j_{(2)}(j)$，定义
$$
X=e_*(j_{(3)}),\qquad R=f(j_{(2)}),\qquad
\boxed{W=R(X)=f(j_{(2)})(e_*(j_{(3)})).}
\tag{13}
$$
标准的小点像为
$$
j_{(2)}(\kappa_1)=\kappa_2,\qquad
j_{(3)}(\kappa_0)=\kappa_2,\qquad j_{(3)}(\kappa_2)=\kappa_3.
$$
$e_*$ 固定 $\kappa_0$，且 $e_*(\kappa_2)=\kappa_3$，所以
$$
\operatorname{crit}(X)=\kappa_0,\quad
X(\kappa_0)=e_*(\kappa_2)=\kappa_3,
\quad X(\kappa_3)=e_*(j_{(3)}(\kappa_2))=\theta_5.
\tag{14}
$$
另一方面，
$$
\operatorname{crit}(R)=f(\kappa_1)=\theta_5,\qquad
R(\theta_5)=f(j_{(2)}(\kappa_1))=f(\kappa_2)=\beta.
\tag{15}
$$
$R$ 固定 $\kappa_0,\kappa_3$，故
$$
\boxed{\operatorname{crit}(W)=\kappa_0,\quad
W(\kappa_0)=\kappa_3,\quad W(\kappa_3)=\beta.}
\tag{16}
$$
于是完整五行 seed 可以全部给出 owner：
$$
\begin{array}{c|c|c|c|c}
\text{行号}&\text{core}&L&\text{隐含端点}&\text{owner}\\\hline
1&(0,1)&1&2&j\\
2&(0,1,2)&1&3&j\\
3&(0,3)&1&4&W\\
4&(0,2,4)&2&5&H\\
5&(0,2,4,5)&2&6&H
\end{array}
\tag{17}
$$
末行地址 $4$ 的标记另外保留；两行 $H$ 的接缝仍是真正同 owner。
每一行按步长配对的点像以及临界点均已核对。因此这份 seed 不再依赖“零行永远不用 owner”
的弱语义；后续若把第 3 行整体取实际 $Q$-像，已有真正的 $Q(W)$ 可用。
这仍不等于已经检查后续任意一步的所有重编号与补全条件。

### 3.2 下一次 short [2] 所需的两个复制拥有者

令 $\eta=H(\kappa_3)$。由 $\kappa_2<\kappa_3<\beta$ 及 (10)—(11)，
$$
\beta<\alpha<\zeta<\eta<\theta_6.
\tag{18}
$$
使用同一复制者 $H$，新两行的拥有者取实际项
$$
J_6=H(j),\qquad W_7=H(W).
$$
二者临界点均为 $H(\kappa_0)=\beta$。由 application 点像恒等式，
$$
\boxed{J_6:\beta\mapsto\alpha\mapsto\zeta\mapsto\eta,\qquad
W_7:\beta\mapsto\eta\mapsto\theta_6.}
\tag{19}
$$
第一条是 $j:\kappa_0\mapsto\kappa_1\mapsto\kappa_2\mapsto\kappa_3$
的 $H$-像。第二条是刚补齐的
$W:\kappa_0\mapsto\kappa_3\mapsto\beta$ 的 $H$-像。
尤其 $W_7(\eta)=H(W(\kappa_3))=H(\beta)=\theta_6$，
因此这次复制并未失去末端预算。

在点表
$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\beta,\alpha,\zeta,\eta,\theta_6)
$$
中，第 6 行 core $(4,5,6)$、$L=1$、隐含端点 $7$，由 $J_6$ 实现；
第 7 行 core $(4,7)$、$L=1$、隐含端点 $8$，由 $W_7$ 实现。
这正是旧无主行首地址从 $0$ 变为正地址 $4$ 时缺少的拥有者；
现在已有明确项，而不是继续套用零端口例外。

## 4. 有限核验

small_period_native_mark_seed_certificate.py（历史参考：`small_period_native_mark_seed_certificate.py`）
调用既有 `three_row_certificate.py` 的真实 application 构造，并直接断言 (8)、(10)、(11)
及两条步长为 2 的 bridge 行、插值后步长为 3 的单桥行的配对；
还实际构造 (13) 的 $W$，检查 (16) 和 (17) 的全部行。
证书也构造 $H(j),H(W)$，检查 (19) 及下一次复制的第 6、7 行。
不运行 M、不枚举 BMS 下降，也不引入抽象的未给出拥有者。
