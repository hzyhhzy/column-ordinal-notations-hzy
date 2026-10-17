# 用 BMS 下降长度生成下一轮 BMS 行数

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

本篇保留首版三行反馈。后续[降根反馈证明](<root-lowered-bms-feedback.zh-CN.md>)已经解除其内层三行限制及对数损失，得到 $q(5)>D(D(h)+2)$，涵盖此前全部可用行数；下文关于直接使用 $E$ 的端点障碍仍成立，但不再是当前方案的阻碍。

在 I3 假设及本项目已证明的带实现、统一前端插入引理下，有一个严格的嵌套下界：

$$
\boxed{
q(5)>D_2(R_H),\qquad
H=\left\lfloor\log_2 D_2(R_3)\right\rfloor+2,
\quad R_h=(0^h)(1^h)(1^h).
}
\tag{1}
$$

这里括号是 BMS 的列，$h$ 是行数；$D_2$ 是父表表示反复取新 $[2]$ 至空的总次数，等同原 BM4 反复取 $[1]$ 的次数。$q(5)$ 是首行周期首次达到 32 的 Laver 表阶参数，不是表的元素数。所有嵌入、临界点及见证都属于同一个固定 $\operatorname{Iter}(j)$。

式 (1) 已把一次 BMS 下降的结果真正用作下一轮的行数，代价是取一次二进制对数。这个首版方案只给出了三行输入，也没有证明式 (1) 本身强于此前 $g^{258}(1)+2$ 行的下界。后续较强结论来自不同的反馈嵌入及降根链，而不是将本篇尚未证明的端点条件直接视为成立。

有限代数部分见 bms_height_feedback_certificate.py（历史参考：`bms_height_feedback_certificate.py`）。下面的全称推论来自纸面证明，不以该程序替代。

## 从临界点数量恢复共同根的链

写 $\gamma_0<\gamma_1<\cdots$ 为 $\operatorname{Iter}(j)$ 的临界点枚举。由 [Dougherty 第二篇定理 3.1(c)](https://arxiv.org/pdf/math/9503204)，对每个自然数 $s$，

$$
a_s=j_{(2^{2^s}-1)}:
\gamma_0\longmapsto\gamma_{2^s}\longmapsto\gamma_{2^{s+1}}.
\tag{2}
$$

因此 $a_0,\ldots,a_{m-1}$ 显式见证

$$
(\gamma_0,\gamma_1,\gamma_{2^m})
\quad\text{是 }m\text{-lined}.
\tag{3}
$$

也就是说，其共同临界点为 $\gamma_0$，链依次经过下标为 $1,2,4,\ldots,2^m$ 的点。

若 $r\ge2^m$，还可以把最后端点提高到 $\gamma_r$。在严格不等时，取临界点为 $\gamma_{2^m}$、将它送到 $\gamma_r$ 的嵌入 $B$，将最后一段改成 $B(a_{m-1})$。这样的 $B$ 可由后继临界点搬运的有限复合给出；它固定该段的前两个点，所以其余链不变。

反过来，linedness 的临界点计数引理给出：如果 $(\gamma_0,\gamma_1,\gamma_r)$ 是 $m$-lined，则 $r\ge2^m$。参见 [Qi 引理 2.5](https://arxiv.org/html/2501.06733v5#S2)。所以对 $r\ge2$，这个特定三元组的最大链长恰为 $\lfloor\log_2 r\rfloor$。这不表示可以随意更换共同根和起点。

## 反馈所需的端点条件

沿用[统一前端插入](<../iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md>)中的记号：

$$
K=j_{(11)},\qquad \mu=\theta_4,
\qquad L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7,
\qquad E=L_3(K).
$$

其中 $E$ 的定义是 application，不是普通复合。应用点像恒等式及已知点像给出

$$
\begin{aligned}
E(\gamma_0)&=E(\kappa_0)=\kappa_2,\\
E(\gamma_1)&=E(\kappa_1)=\theta_6,\\
E(\kappa_2)&=L_3(\mu),\\
E(L_3(\mu))&=L_3(K(\mu))
 =L_3(\theta_6)=\theta_7<\kappa_4.
\end{aligned}
\tag{4}
$$

**反馈引理。** 假设 $h\ge3$，已有高度 $h$ 的闭合相容组，封口为临界点 $C$，并且额外满足

$$
E(C)<\kappa_4.
\tag{5}
$$

则令 $M=\lfloor\log_2 D_2(R_h)\rfloor$，可得

$$
q(5)>D_2(R_{M+2}).
\tag{6}
$$

**证明。** 闭合相容组提供 $R_h$ 的带实现。由[带展开与删端点计数](<../iblp-laver-bms-20261013/ribbon-initialization.zh-CN.md>)，若 $C=\gamma_r$，则

$$
D_2(R_h)<r.
$$

因此 $2^M\le D_2(R_h)<r$，从而 $\gamma_{2^M}<C$。将 (3) 的整条链取 $E$-像，得到

$$
(\kappa_2,\theta_6,E(\gamma_{2^M}))
\quad\text{是 }M\text{-lined},
$$

其端点严格低于 $E(C)<\kappa_4$。统一前端插入引理将这条链变为高度 $M+2$ 的闭合相容组，封口仍严格低于上述链端点。再次使用带实现的删端点计数，以及 $q(5)=F(4)+1$，即得 (6)。证毕。

这两次带模拟各自计算一个确定的 BMS 种子的完整下降。没有把反复执行 M 的次数藏进基本列定义；也没有把有限临界点数量当成某个序数嵌入的替代品。

## 三行输入满足额外端点条件

取[两层初始化](<../iblp-laver-bms-20261013/short-terminal-initialization.zh-CN.md>)的闭合组，封口为 $\rho<\theta_6$。定义

$$
Q=E(j),\qquad T=Q(j_{(10)}).
$$

由 (4)，

$$
Q:\kappa_2\longmapsto\theta_6\longmapsto E(\kappa_2).
\tag{7}
$$

这正是一段可以用于前端插入的链。进行一次插入后得到高度 3 的闭合相容组，封口为

$$
C_3=T(\rho).
$$

由于 $j_{(10)}(\kappa_2)=\mu<\theta_6$，

$$
\begin{aligned}
C_3
&<T(\theta_6)\\
&=Q(j_{(10)})(Q(\kappa_2))\\
&=Q(\mu)\\
&<Q(\theta_6)
 =E(\kappa_2)=L_3(\mu).
\end{aligned}
\tag{8}
$$

于是

$$
\boxed{E(C_3)<E(L_3(\mu))=\theta_7<\kappa_4.}
\tag{9}
$$

这验证了反馈引理的关键额外条件。将 $h=3$ 代入 (6)，即得 (1)。这里不是使用旧三行初始化较粗的封口 $\theta_7$，而是使用一次前端插入所得、带有更强上界 (8) 的新三行实现。

## 不能只凭旧端点上界反复反馈

此前十八行及更高行数的构造给出 $C_h<\theta_7$。它没有自动给出 (5)。事实上，下面这个普遍推断是错的：

$$
C<\theta_7\quad\Longrightarrow\quad E(C)<\kappa_4.
$$

为看清这一点，取 $\tau=E(\theta_6)=L_3(\theta_5)$。已有 $\theta_5<\theta_6$，故 $\tau<\theta_7$。另一方面，由 $K(\theta_5)=\theta_7$，

$$
E(\tau)=L_3(\theta_7).
$$

初始化中 $L_3=A(j_{(2)})$、$A(\kappa_3)=\theta_7$，而 $j_{(2)}(\kappa_3)=\kappa_4$。所以

$$
E(\tau)=L_3(A(\kappa_3))=A(\kappa_4)\ge\kappa_4.
\tag{10}
$$

这仅否定用 $C<\theta_7$ 这个粗界保证反馈安全，并不否定具体较大行数的封口可能满足 (5)。

## 旧方案的端点条件与后续替代

若仍坚持本篇的反馈嵌入 $E$，把内层换成至少十一行需要额外证明 $E(C_h)<\kappa_4$，才能得到

$$
q(5)>D_2\!\left(R_{\lfloor\log_2 D_2(R_h)\rfloor+2}\right).
$$

这个额外条件尚未对原有高行数构造证明。后续改用 $P=L_3(f)$ 并接上两段降根链，只需已有的 $C_h<\tau=E(\theta_6)$，已经得到更强、无对数损失的结论。因此不再将证明这一旧条件作为必要步骤。

也可以更换反馈嵌入：如果 $E'$ 满足 $E'(\gamma_0)=\kappa_2$、$E'(\gamma_1)\ge\theta_6$，且 $E'(C_h)<\kappa_4$，相同证明仍成立。需要分别证明这些条件，不能仅比较各嵌入的临界点。

## 有限核验

`bms_height_feedback_certificate.py` 核验三行入口的实际 application 项、相容边、membership 截断及 (8)—(9)。本次核验通过，保留 64 个点名、112 个嵌入项和 870 条点像记录，约 2 秒完成。程序不展开 $D_2(R_3)$ 的数值，默认 35 秒时限，并沿用点数、项数和事实数保护。

`feedback_cap_probe.py` 检查原十六段输入末端 $x_{16}$ 是否满足更强的充分条件 $E(E(x_{16}))<\kappa_4$。本次返回 UNKNOWN：现有有限关系未能证明或否定该比较。另一次两次插入的检查也未决定 $E(C_4)<\kappa_4$。这些未定结果不作为反例。

上述数值记录只描述证书规模。式 (1) 的数学依据是 (2)—(9) 及所引用的全称引理；其公理条件仍是 I3，没有宣称已形式化到 Lean。
