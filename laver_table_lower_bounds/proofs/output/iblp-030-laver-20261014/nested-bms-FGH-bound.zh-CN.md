# 两次行数反馈给出的三层 BMS FGH 下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

按“Laver 与 BMS 对接”和“D 与 FGH 及全部放缩”分成两部分的简洁入口，见
[两部分证明总结](<q5-BMS-FGH-two-part-summary.zh-CN.md>)。那里将最内层输入保守取为
256，并核对 $F_3(256)=F_2^{\circ257}(256)$；本篇保留较强的 257 版本。

2026-10-14。在 **ZFC + I3** 下，已有两次 BMS 行数反馈可以与
[BMS 固定指标下降的 FGH 估计](<../iblp-laver-bms-20261013/BMS-fixed-index-to-FGH-summary.zh-CN.md>)
严格接合。结论不只是单层 BMS：若 $\Lambda$ 表示 BMS 极限，且
$t=F_3(257)$，则

$$
\boxed{q(5)>F_\Lambda\bigl(F_\Lambda(F_\Lambda(t))\bigr).}
\tag{1}
$$

第一轮反馈单独就给出两层版本
$q(5)>F_\Lambda(F_\Lambda(t))$。第二轮再增加一层。
这是嵌套 FGH 的数值下界，不是把 BMS 极限外加后继当成一个新的结构性增强记号。
纸面证明如下；尚未 Lean 形式化。

## 1. 函数与下标约定

$q(5)$ 是普通二元 Laver 表首行周期首次达到 32 的阶参数：

$$
q(5)=\min\{m:\text{有 }2^m\text{ 个元素的表首行周期至少为 }32\}.
$$

记

$$
B_r=(0^r)(1^r),\quad R_h=(0^h)(1^h)(1^h),\quad
D(h)=\text{从 }R_h\text{ 固定取原 BM4 }[1]\text{ 到空的总步数},
\quad T(h)=D(h)+2.
$$

原 BM4 `[1]` 等于父表新指标的 `[2]`。FGH 使用原 BM4 基本列：

$$
F_\varnothing(x)=x+1,\qquad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\qquad
F_M(x)=F_{M[x]}(x)\quad(M\text{ 末列非零}),
$$

其中 $Z$ 为零列，$\Lambda[x]=B_{x+1}$，所以
$F_\Lambda(x)=F_{B_{x+1}}(x)$。本文的“三层”是同一个
$F_\Lambda$ 的三次函数复合，不是三行 BMS。

## 2. 使用已发表链长扩大反馈的输入范围

令 $C=f(p_{\omega+2},1)$。为避免依赖未展开的 BLP 递归，
可等价地用下面的纯有限整数递归定义它：

$$
\begin{aligned}
g(x)&=x2^x, & u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ 2^x}(x), & v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ 2^x}(x), & C&=w(w(1)).
\end{aligned}
\tag{2}
$$

[单层 BMS FGH 证明](<../iblp-laver-bms-20261013/laver-period-32-BMS-bound.zh-CN.md>)
第 2、4 节已核对：Qi 命题 1.3(1) 的证明提供同一
$\operatorname{Iter}(j)$ 中的实际 $C$-lined 链
$(\kappa_0,\kappa_1,\theta_5)$，且

$$
C>4t,\qquad t=F_3(257).
\tag{3}
$$

这里使用该证明中的链见证，不是从临界点下标很大倒推 linedness。
式 (2) 来自 $2^C=m_{\omega+2}(2)$ 的指数共轭。

已有初始化给出

$$
E=L_3(K),\quad K=j_{(11)},\quad
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,\quad
E(\theta_6)=\tau=L_3(\theta_5),\quad \theta_5<\theta_6.
$$

把上述 $C$ 段链整体取 $E$-像，末端为
$E(\theta_5)<\tau$。
[统一前端插入](<../iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md>)
遂给出高度 $C+2$ 的闭合相容组，封口严格低于 $\tau$。
对任意 $3\le h\le C+2$，取原链的前 $h-2$ 段，也得到同样封口条件的高度 $h$ 组。

这比早期采用 $g^{\circ258}(1)+2$ 的输入上界更宽，而且不依赖标记启动历史。

### 两轮反馈均保持在同一个周期端点以下

[第一轮反馈](<root-lowered-bms-feedback.zh-CN.md>)的局部引理说：
输入为高度 $h$、封口低于 $\tau$ 的组时，输出高度为 $T(h)$，
封口低于 $\theta_7$。

[第二轮搬运证明](<promoted-bms-feedback.zh-CN.md>)取
$S=j_{(9)}(j_{(4)})$，已经证明

$$
S(\kappa_2)=\kappa_2,\qquad
\theta_7<S(\tau),\qquad S(\theta_7)<\theta_8<\kappa_4.
$$

第一轮输出因此能输入搬运后的反馈条件，得到高度 $T(T(h))$、
封口低于 $S(\theta_7)<\kappa_4$ 的组。
带实现与删端点计数对这些组分别给出

$$
\boxed{q(5)>D(T(h)),\qquad q(5)>D(T(T(h)))
\quad(3\le h\le C+2).}
\tag{4}
$$

新输入没有改变两轮的局部证明。第二轮之后没有在此继续搬运；
式 (4) 不意味着任意多轮反馈都可放在 $\kappa_4$ 以下。

## 3. 森林估计保留的余量

只使用总结中的 $D(h)\ge F_{B_r}(x)$ 还不能直接迭代：
下一轮不只需要 $F_{B_r}(x)$ 行，还有行数开销。
需要返回其证明，而不是忽略这个开销。

定义

$$
e_0=1,\qquad e_{y+1}=2^{e_y},\qquad
\ell(x)=\lceil\log_2(x+2)\rceil.
$$

[森林控制器证明](<../iblp-laver-bms-20261013/diagonal-forest-hardy-proof.zh-CN.md>)
式 (9) 实际给出更强的终点估计：若 Hardy 计算输出为 $y$，
控制森林的后继删除数至少为 $e_y$，而不只是至少为 $y$。
保留它，并使用同一行宽预算，得到

$$
\boxed{D(h)\ge e_{F_{B_r}(x)}
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}
\tag{5}
$$

具体链条为

$$
D(h)\ge s_{R_h}(1)
\ge s_{\Sigma(W(B_r)Z^x)}(1)
\ge e_{H_{W(B_r)}(x)}
=e_{F_{B_r}(x)}.
$$

全部不等式和尺寸条件与用户提供的总结相同，只是不在最后把 $e_y$ 放松为 $y$。
辅助矩阵的终止和覆盖也沿用原证明，不新增其良基性假设。

## 4. 一轮输出支付下一轮全部行数

令

$$
\rho(x)=x+3+\ell(x).
$$

取 $r=x+1$，式 (5) 变为

$$
h\ge\rho(x)\quad\Longrightarrow\quad
D(h)\ge e_{F_\Lambda(x)}.
\tag{6}
$$

对任意标准下标，良基归纳给出 $F_M(x)\ge x+1$：
零项直接成立，后继是至少一次严格增值的迭代，极限使用其较小基本项的归纳假设。
因此 $x\ge2$ 时，$y=F_\Lambda(x)\ge3$。

对 $y\ge2$，由 $2^y\ge y+2$ 得 $\ell(y)\le y$，故
$\rho(y)\le2y+3$。又对 $y\ge3$，

$$
e_y\ge2y+3>y.
\tag{7}
$$

后式的基础为 $e_3=16\ge9$；归纳步用
$2^{e_y}\ge2e_y\ge4y+6\ge2(y+1)+3$。

所以 (6) 给出所需的带开销结论

$$
\boxed{h\ge\rho(x),\ x\ge2
\quad\Longrightarrow\quad
T(h)=D(h)+2\ge\rho(F_\Lambda(x)).}
\tag{8}
$$

没有使用一般的 FGH 序数单调性，也没有将 $D$ 与 $F_\Lambda$ 认同。

## 5. 两次反馈与三次 FGH 计算

更一般地，取任意 $x\ge2$ 满足

$$
x+1+\ell(x)\le C.
\tag{9}
$$

置 $h_0=C+2$、$h_1=T(h_0)$、$h_2=T(h_1)$，
并令 $x_0=x$、$x_{i+1}=F_\Lambda(x_i)$。
式 (9) 恰好保证 $h_0\ge\rho(x_0)$。
两次应用 (8)，得到

$$
h_1\ge\rho(x_1),\qquad h_2\ge\rho(x_2).
$$

因此 (4)、(6) 分别给出

$$
\boxed{q(5)>D(h_1)\ge e_{x_2}>x_2
=F_\Lambda(F_\Lambda(x)),}
\tag{10}
$$

$$
\boxed{q(5)>D(h_2)\ge e_{x_3}>x_3
=F_\Lambda(F_\Lambda(F_\Lambda(x))).}
\tag{11}
$$

取 $x=t=F_3(257)$，由 (3) 和 $\ell(t)\le t$，
$t+1+\ell(t)\le2t+1<C$，故 (9) 成立，证明 (1)。
同样可以取 $x=\lfloor(C-1)/2\rfloor$；它也直接满足预算，
不必先证明输入单调性。

## 6. 本结论与继续研究的区别

两层或三层嵌套数值下界已由上面的纸面推导得到。
此前只整理的单层 $F_\Lambda(F_3(257))$ 是不使用反馈的基础结论，
并非目前能给出的全部下界。

本结论仍没有交付一个通过内部复制或补全实质增强的超 BMS 记号，
也没有证明原 IBLP 030 的指定 Hardy 或 FGH 值受 $q(5)$ 控制。
不能把式 (11) 的三次函数复合重新命名为新记号，借此宣布主线完成。

有限核验只用于检查局部实现：BMS 一侧本轮重新运行了森林控制器、
FGH 到 Hardy 和祖先覆盖检查；Laver 搬运的有限证书见两轮反馈文稿。
没有实际求值 $D(h_i)$、$F_\Lambda(x_i)$ 或构造这些巨大行数的数组。
通式来自上述整数归纳、结构模拟及嵌入实现证明，不来自有限实验。
