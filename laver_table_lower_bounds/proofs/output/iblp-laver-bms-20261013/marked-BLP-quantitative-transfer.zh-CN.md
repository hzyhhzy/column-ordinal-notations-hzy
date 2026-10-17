# 自然截断标记 BLP 的有限参数定量桥

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-13。本文补上前期普通标记 BLP 文稿留下的有限参数接口：后继双块抽取之后仍有完整的自然截断证书，并且可以更换 linedness 参数。结合此前的局部闭包引理，得到原 Laver 表的具体数值下界。

这不是 BMS[10] 下界的完成证明。本文最后的数 $f_\star(P_{\rm start},1)$ 与指定 BMS 快速增长值之间仍缺比较。全文是纸面证明，未 Lean 形式化。

## 规则和已用局部引理

采用普通 BLP 行型、短复制、论文的互斥 successor／limit／transient 分支。$E(k)$ 是论文辅助三点行递归；$M_\star$ 是一次短复制后左到右的完整标记及原生补全扫描。复制使用 PDF 的正确一基 guard，不能换成本地旧 Python 的少一位版本。

零项是固定首两行。若完整行是 $s_i$，压缩 core $A_i$ 删去隐含端点 $i+1$。记

$$
p(i)=A_i[-L_i-1],\quad e(i)=A_i[-L_i],\quad B(i)=A_i[-2].
$$

ordinary Sat 条件是：对 eligible 的中／短行，$B(e(i))\le p(i)$。每枚 proper mark $y$ 的实际 $p$ 链必须准确命中其步长源 $\delta$。若非终点因子为 $v_0=y,\ldots,v_{d-1}=t$，则

$$
W=j_{v_0}\circ\cdots\circ j_t,
\qquad
\Delta(W)=(j_{v_0}\circ\cdots\circ j_{v_{d-2}})(\theta_{t+1}).
$$

空复合取恒等映射。要求 $j_i\equiv_{\Delta(W)}W$，等价符号是 Laver 的 membership 截断，不是普通函数限制。

用到的局部引理来自已有文稿：

- [自然截断的复制闭包及补全读值](<../../natural-mark-lemmas/natural_trace_cutoff_semantics.md>)。
- [Sat 入口的整包传送及一次 M 闭包](<../../natural-mark-lemmas/sat_endpoint_packet_theorem.md>)。
- [实际复制因子词识别](<../../natural-mark-lemmas/copy_trace_word_identification.md>)。
- [Sat 对扫描、前缀和辅助 E 的保持](<../../natural-mark-lemmas/marked_blp_order_domain.md>) 第 9 节。
- [后继 E 的因子下界和抽取](<../../natural-mark-lemmas/marked_E_transfer_work.md>) 第 2、3、7 节。

这些引理只需普通行实现、准确 traces、Sat 和自然截断，不需把输入限制为某条特定生成历史。扫描内保存的历史截断，在每次扫描入口由当前证书重新取得；不是必须跟随根节点携带的额外历史数据。因而以下证书类是充分的。

## 证书类

固定一个 I3 嵌入 $j$，所有行嵌入及 linedness 见证都在同一个 $\operatorname{Iter}(j)$ 中。

令 $\mathcal C$ 包含满足以下条件的有限 marked BLS：

1. 全部普通行边和临界点由行嵌入实现，首两行的完整点列为 $012$、$0123$，步长均为 1。
2. 模式 Sat，全部 marks proper，全部 traces 精确。
3. 每枚 mark 的实际步长源 $\delta\ge1$，记为 PosSource。
4. 每枚 mark 满足其当前实际词的自然截断语义。
5. 携带某个有限 $m\ge1$ 的 $(\theta_0,\theta_1,\theta_2)$ 同端点 $m$-linedness 见证。

这里不要求一个固定三元组同时具有所有有限参数的见证，不需要 I2，也不把多个生成元的临界点混在一个计数函数中。

### 前缀和见证替换

限制到至少两行的前缀保持全部条件：proper 因子及其下一列都不越过所保留 owner 的范围。已有 mark 的词、自然界和真实嵌入均不变。

若同一首三元组另有一份有限 $M$-linedness 见证，可以直接替换第 5 项。前四项完全不使用 $m$ 或 linedness 见证的身份。因此这不是“另找一个更方便的行实现”；行嵌入和基数全部固定。

### 正标记源的保持

合法复制保持行内位置和步长，新源是 $\varphi(\delta)\ge\delta$。原生补全的非空包，其旧 $p\ge1$：二点 core 的一步长行没有原生包，其余普通 eligible 行的 $p$ 至少是第二个非负整数条目。新 direct marks 的源为这个 $p$ 或比它大的包源。

正确的标记补全保留旧边，新 mark 的源来自先前非空原生包。由此 PosSource 在原操作下保持。准确 trace 严格下降至 $\delta$，所以每个非终点因子都严格大于 $\delta$，因而

$$
v_0,\ldots,v_{d-1}\ge2.
\tag{Floor}
$$

结合前述局部闭包引理，有限参数允许的 $E(m)$、$M_\star$、cut 都保持 $\mathcal C$。自然 E 只需当前这份有限 $m$-linedness；证明没有使用任意大参数的共同见证。

## 任意实现的新块抽取

这是补齐定量归纳的核心。令 $q$ 有 $d\ge2$ 行、满足 PosSource 和 Sat。定义 $D(q)$：在 $q$ 后加辅助完整行 $(2,d+1,d+2)$，步长 1，然后短复制。它是 successor E 的一次加倍，不在此对任意父项新增一种基本列规则。

复制坐标是

$$
\psi(0)=0,\quad\psi(1)=1,\quad
\psi(x)=x+d-1\quad(x\ge2).
$$

所有 mark 因子至少为 2，故全部使用全因子复制分支，所有 marks 均保留。$D(q)$ 有 $2d-1$ 行。

**抽取引理。** 对 $\mathcal C$ 中任意实现 $Q\models D(q)$，令 $\nu=Q.\theta_{d+1}$。若 $(Q.\theta_0,Q.\theta_1,\nu)$ 有 $M$-linedness 见证，则有 $R\in\mathcal C$ 实现 $q$，满足

$$
R.m=M,\qquad R.\Theta=Q.\Theta,\qquad R.J=Q.J.
\tag{7}
$$

不假定 $Q$ 来自某次指定的语义复制操作。

**证明。** 对基数坐标 $2\le s\le d+1$、行嵌入坐标 $2\le s\le d$，分别设

$$
R.\theta_s=Q.\theta_{\psi(s)},\qquad
R.j_s=Q.j_{\psi(s)},
$$

并保留第 0、1 基数，取 $R.j_1=R.j_2$。复制的第二行具有完整点列 $(0,1,\psi(2),\psi(3))$，因此其嵌入的前三点也实现新的第一行。其他行由逆重编号直接恢复。

对 $q$ 中任意 mark，其 $Q$ 中的词是 $\psi(v_0),\ldots,\psi(t)$。这些因子全部在新块，不用新补造的第一行。由于 $t\ge2$，有

$$
\psi(t+1)=\psi(t)+1.
$$

因此新旧自然截断不仅都有效，而且是同一个实际序数：

$$
\Delta_R(W)=
(Q.j_{\psi(v_0)}\circ\cdots\circ Q.j_{\psi(v_{d'-2})})
(Q.\theta_{\psi(t)+1})
=\Delta_Q(\psi(W)).
\tag{8}
$$

式中 $d'$ 是该词的因子数。owner 也是同一个实际嵌入，所以自然语义逐枚保留。PosSource、准确 trace 和 proper 条件由逆坐标映射恢复。

Sat 是模式 $q$ 的纯语法性质，在抽取后未变；第一行也直接满足 Sat。给定的新 linedness 见证可替换参数而不影响其他条件。因此 $R\in\mathcal C$。最后一行和最后基数没有换，得到 (7)。证毕。

扫描时所需的历史自然界可以在新的 $R$ 上重新保存，故这里没有丢失一个未列明的生成历史前提。

## 定量定理

定义 $f_\star$ 逐字沿用 Qi 论文 Definition 2.24，只把 $M$ 替换为上述 $M_\star$，并在 E 中保留 marks：

$$
f_\star(p,m)=
\begin{cases}
m2^m,&p\text{ 为零项},\\
f_\star(\operatorname{cut}p,m),&p\text{ 不可复制},\\
\bigl(x\mapsto f_\star(\operatorname{cut}p,x)\bigr)^{2^m}(m),
&p\text{ 为 successor},\\
f_\star(p.E(m),m),&p\text{ 为 limit},\\
f_\star(p.M_\star,m),&\text{其余可复制项}.
\end{cases}
\tag{9}
$$

定义优先级如所列，零项优先。它先作为部分递归函数定义，不预设全域终止。

**定理。** 若 $P\in\mathcal C$ 实现 $p$，参数为 $m$，则 $f_\star(p,m)$ 有定义，而且

$$
(P.\theta_0,P.\theta_1,P.\Theta)
\quad\text{是}\quad f_\star(p,m)\text{-lined}.
\tag{10}
$$

**证明。** 按论文的 BLS 良基关系归纳：先比较最后基数 $\Theta$，同端点时用有界 application 关系比较最后嵌入 $J$。本证书类只需 application 右因子也在同一个 $\operatorname{Iter}(j)$ 中的关系；全部自然操作满足此限制。Steel 定理保证该关系良基。

cut 严格降低 $\Theta$。$M_\star$ 不改末基数，末 owner 是 $J(j_{e-1})$；完整扫描保留它。$E(m)$ 不改末基数，末 owner 经两次 application 获得，两个中间临界点都低于共同末基数。因此这些自然操作严格下降。

零项由论文的两行 linedness 引理给 $m2^m$。不可复制项先向 cut 应用归纳，再用临界点搬运嵌入把最后一段的末点延长到 $P.\Theta$。limit 和 transient 直接使用自然 E／M 的闭包及下降。

对 successor，令 $q=\operatorname{cut}p$、$g(x)=f_\star(q,x)$。设 $q_i=p.E(i)$，于是 $q_0=q$，$q_{i+1}=D(q_i)$。证明强化断言：

> 对任意 $Q\in\mathcal C$，若 $Q<P$、$Q\models q_i$，则其首两点与末点为 $g^{2^i}(Q.m)$-lined。

$i=0$ 是外层良基归纳。由 $i$ 到 $i+1$，先限制到旧块，末点为 $\nu<Q.\Theta$。归纳给 $M=g^{2^i}(Q.m)$ 的同端点见证。用抽取引理得到实现 $q_i$ 的新块 $R$，参数为 $M$，最后基数和嵌入与 $Q$ 相同，所以 $R<P$。再次应用同一强化断言，得到

$$
g^{2^i}(M)=g^{2^{i+1}}(Q.m)
$$

的 linedness。所有涉及的函数调用同时由归纳证明有定义，不预设 $g$ 在所有整数上的全定义或单调性。

最后向自然实现 $P.E(m)<P$ 应用 $i=m$ 的断言，即为 successor 分支的 $2^m$ 次迭代。各分支完成，得到 (10)。证毕。

## 原 Laver 表的明确推论

标准标记根为

```text
012:1  0123:1  01234:2  012345:2  23456:2
```

第 4 行唯一 mark 是 3，其 trace 是 $(3,1)$。其余 marks 为空。

Qi 论文对普通 $P_{\rm start}$ 的具体实现取 owners

$$
j,\quad j,\quad h,\quad h,\quad h(h),
\qquad h=j_{(11)}.
$$

因此第 4 行的 mark 由 owner 与第 3 行 owner 全局相等实现，其自然语义自动成立。输入 Sat，唯一 mark 源为 1；首三元组 $\kappa_0,\kappa_1,\kappa_2$ 为 1-lined。最后基数是

$$
\Theta=\kappa_3^{10}<\kappa_4.
$$

定量定理和 linedness 计数引理于是给

$$
\Theta\ge\gamma_{2^{f_\star(P_{\rm start},1)}}.
$$

用 $q(5)=F(4)+1$ 及 $\kappa_4=\gamma_{F(4)}$，得到

$$
\boxed{q(5)>2^{f_\star(P_{\rm start},1)}.}\tag{11}
$$

这是一个已明确规则、固定小周期指数的下界接口。它不含“取足够大的 N”，也不调用所有参数的共同无限 linedness。这里的新增结论是 **完整自然截断标记规则的 $f_\star$ 可以用于原 Laver 表的定量下界**，不能因此就把它叫作 BMS 下界。

要完成当前目标，还需证明例如

$$
2^{f_\star(P_{\rm start},1)}
\ge F^{\rm BMS}_{\mathrm{BMS}[10]}(10),
$$

或者找到另一个同样受小 $N$ 控制、且可严格比较的模式。

## 有界语法核验

marked_quantitative_probe.py（历史参考：`marked_quantitative_probe.py`） 使用旧诊断引擎的正确 PDF copy guard，但不运行其写文件的主程序，也不修改任何外部文件。核验只涉及短复制 E／M，不混入原 IBLP 全尾规则。

最新运行检查了 570 个队列状态、1,610 次转移，连同一个专项回归例，完成 537 次双块抽取，精确恢复 2,035 枚 marks。专项例包含真正的非邻接多因子 trace，用来检查抽取没有暗用内部邻接；不声称它从标准根可达。资源界为 20 秒、150 行、每状态 15,000 条目、1,500 个不同状态和深度 25；44 个资源停止不计为完成。

这些测试只核对语法下标、Sat、PosSource、准确 trace 及 marks 的恢复，不验证无限域上的嵌入语义，也不替代以上证明。
