# 小周期下的递归 corridor：已证条件式与尚缺端点

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本文只保存条件式代数结果，不宣布已经取得新的小周期下界。
记原反馈背景为
$$
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7,
\quad P(\gamma_0)=a,\ P(\gamma_1)=b,\ P(b)=c.
$$
原模板实现整数函数 $T(h)=D(h)+2$。模板的自然性指：对任何固定
$\kappa_0,\kappa_1$ 的环境嵌入 $Q$，把整个有限背景取 $Q$-像后，
仍能处理任意全局 `Iter(j)` 中的输入 fan，不要求输入是某个旧 fan 的像。
这是 [整背景搬运引理](<lined-feedback-corridor.zh-CN.md>) 使用的意义。

## 1. 升级一个自然模板的较弱端点条件

设自然模板 $F$ 的入口仍为 $b$，出口为 $d\ge c$：
高度 $h\ge3$、封口低于 $b$ 的 fan 被变成高度 $F(h)$、封口低于 $d$ 的 fan。
假设实际嵌入 $H$ 固定 $\kappa_0,\kappa_1,k$，且
$$
d<H(a),\qquad H(c)<B.
\tag{1}
$$
那么入口 $b$、出口 $H(c)$ 实现一个新自然模板
$$
\mathcal U(F)(h)=F^{\circ(D(F(h))+1)}(h).
\tag{2}
$$

证明：先执行一次 $F$，得到高度 $F(h)$、封口 $C<d$ 的 fan。
令 $N=D(F(h))$。全局计数给出 $\gamma_N<C<d<H(a)<H(b)$。
仍然使用原来的 $H(P)$，而不是新模板的内部链生成器，将全局 Dougherty
链搬运并降根、收缩，得到 $N$-lined 的 $(k,H(a),Z)$，其中
$$
Z<H(P)(H(b))=H(c).
$$
链的每一段 $Q_i:k\mapsto u_i\mapsto u_{i+1}$ 满足
$Q_i(b)>u_i$、$Q_i(d)<u_{i+1}$，因为 $k<b$ 且 $d<H(a)\le u_i$。
所以沿链搬运整个 $F$ 模板，共执行 $N$ 次。连同第一步即为 (2)。
对有限证明的全部背景再作整体搬运，保持同样的公式和严格守卫，故新模板自然。

重要区别：需要的末端是 $H(c)$，不是更强的 $H(d)$。
此处 $c=\theta_7$ 始终是原始链生成器的出口。

## 2. 一条提高了共同根的长链可支持可变深度升级

若有实际 $M$-lined 链
$$
(r;u_0,\ldots,u_M),\qquad k<r<a<c\le u_0,
\tag{3}
$$
其每段拥有者为 $H_i:r\mapsto u_i\mapsto u_{i+1}$，则可递归定义
$$
F_0=T,\qquad F_{i+1}(h)=F_i^{\circ(D(F_i(h))+1)}(h).
\tag{4}
$$
全部模板入口仍为 $b$，第 $i+1$ 个模板出口可取 $H_i(c)\le u_{i+1}$。
原因是 $H_i$ 固定 $k$，且 $H_i(a)>u_i$、$H_i(c)\le u_{i+1}$。
上一步模板出口不大于 $u_i$，故满足 (1) 的严格入口条件。
首步允许 $c=u_0$，因为 $H_0(a)>u_0$；新 fan 的封口始终严格低于模板出口。

这是对任意给定有限 $M$ 的统一证明，不是声称固定 $B$ 下存在所有长度的链。
即使 $M$ 很大，它仍只给出新的计算下界，不能自动满足“内部结构实质超过 BMS”
的设计目标。

## 3. 一个具体的大深度链候选及其唯一新端点

令 $K=j_{(11)}$，取实际 application 项
$$
A=K(K)(f).
$$
由既有点像和 application 恒等式，
$$
A(\gamma_0)=\theta_5,\qquad
A(\gamma_1)=\theta_7,\qquad
A(\theta_5)=K(\theta_6).
\tag{5}
$$
例如 $K(K)(\kappa_3)=K(\kappa_3)=\theta_5$，因为
$\kappa_3=K(\kappa_1)$；其余两式同样读取 $K$-像上的 application 恒等式。
把既有 $C_{\rm line}$-lined $(\kappa_0,\kappa_1,\theta_5)$ 链取 $A$-像，得到
$$
(\theta_5;\theta_7,\ldots,K(\theta_6)),
$$
恰满足 (3) 的根、起点条件。因 $K$ 的临界序列开头为
$\kappa_0,\kappa_2,\mu,\theta_6$，
$$
K(\theta_6)=\kappa_4^K\ge\kappa_4.
$$
因此该链不能放进旧 $q(5)$ 预算。新的明确待证条件是
$$
K(\theta_6)<j(\gamma_5)\quad\text{或}\quad K(\theta_6)<j(\gamma_6).
\tag{6}
$$
目前未证明任一式。另由 $K=j_{(10)}(j)$、$\theta_6=j_{(10)}(\kappa_3)$，
也可把左侧写成 $j_{(10)}(\kappa_4)$。

## 4. 小周期指标与有界探测

必须区分
$$
B_5=j(\gamma_4)=\kappa_4,\quad B_6=j(\gamma_5),\quad B_7=j(\gamma_6).
$$
$q(6)$ 对应的不是 $\kappa_5$。事实上 $\gamma_6<\kappa_4$，
所以 $B_7<\kappa_5$。

小探测程序（历史参考：`small_period_promoter_probe.py`） 引入 $L_{10}$ 可见的 103 条精确点像，
检查预先列出的 application 家族相对于三个端点的条件。
一次运行 8.58 秒，118 个点名、146 个拥有者、1,127 条点像；返回 UNKNOWN。
它使用的是旧的较强守卫 $H(S(c))<B$，因此尤其不能用“未命中”否定第 1 节
的新弱守卫或 (6)。程序没有枚举 BMS 下降、Laver 巨表或无界 M 过程。
