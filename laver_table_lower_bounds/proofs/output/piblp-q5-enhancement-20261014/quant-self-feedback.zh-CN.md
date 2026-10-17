# pIBLP 定量函数的自反馈与周期三十二下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。假设 ZFC + I3，全部实际嵌入取自同一个
$\operatorname{Iter}(j)$。采用当前 pIBLP 的规则：首次完整复制地址域检查
失败就删去末行，不改为最长合法前缀复制。记九行实际种子为 $S$，并置

$$
G(m)=f_{\rm PP}(S,m).
\tag{1}
$$

这里的 $f_{\rm PP}$ 是[父包有限参数定量桥](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.zh-CN.md>)
式 (3) 的递归计算，不是 pIBLP 的 FGH，也不是固定 `[2]` 总次数。
已有定量桥可以自反馈，得到

$$
\boxed{q(5)>2^{G^{\circ3}(1)}.}
\tag{2}
$$

沿已有 BMS 反馈长链，还可得到

$$
\boxed{q(5)>2^{G^{\circ(N+1)}(1)},\qquad
N=D(T(h)),\quad 3\le h\le C_{\rm line}+2.}
\tag{3}
$$

$D,T,C_{\rm line}$ 使用[沿长链逐段反馈](<../iblp-030-laver-20261014/lined-feedback-corridor.zh-CN.md>)
的原定义，特别是 $T(h)=D(h)+2$。第 4 节用同代数的逐相邻临界点 owner
构造补齐逐段端点延长，避免将 Qi 引理 2.11 超出同一 BLS 的范围使用。
本篇证明的是 pIBLP 新增的数值接口；
没有证明 $G$ 支配 BMS 反馈函数 $T$，因而不把 (2) 或 (3) 宣称为
超过现有最佳显式 BMS–FGH 下界。

## 1. 有限参数定量桥的准确输入

实际种子 $S$ 的首三点为
$(\kappa_0,\kappa_1,\kappa_2)$，cap 为 $\theta_6<\kappa_4$。
它有一份初始 1-linedness 见证，满足 ordinary 行型、ActiveSat、proper
marks、准确 traces、正标记源及自然 membership 截断。其完整证书见
[九行种子的 Sat 证明](<../iblp-030-laver-20261014/same-owner-L3-sat-closure.zh-CN.md>)。

定量桥的形式是：对同一语法图案的任意合格实际实现，只要当前首三元组有
一份有限 $m$-linedness 见证，就同时得到该次 $G(m)$ 调用的定义性及

$$
(\text{首点},\text{次点},\text{cap})
\quad\text{的}\quad G(m)\text{-linedness}.
\tag{4}
$$

这允许依次改变实现和当前有限参数。它不要求原来的固定三元组
$(\kappa_0,\kappa_1,\kappa_2)$ 同时具有任意大的 linedness。

## 2. 同一语法图案的取像实现

设 $Q\in\operatorname{Iter}(j)$ 固定 $\kappa_0,\kappa_1$。将 $S$
的所有命名点、行 owners、marks 的实际因子词和截断界同时取 $Q$-像，
记所得实现为 $Q(S)$。其整数地址、步长和 mask 完全不变，所以仍然是
语法图案 $S$。它的首三点及 cap 分别为

$$
(\kappa_0,\kappa_1,Q(\kappa_2)),\qquad Q(\theta_6).
\tag{5}
$$

所有 owners $Q(J_r)$ 仍属于原来的 $\operatorname{Iter}(j)$，不另换
生成元的临界点枚举。ordinary 行边与临界点由 application 点像恒等式保持；
ActiveSat、proper、正源和准确 trace 都是保持整数地址后的同一条件。

若一枚 mark 原来的非终点词为
$W=J_{v_0}\circ\cdots\circ J_t$，自然截断界是

$$
\Delta(W)=(J_{v_0}\circ\cdots\circ J_{v_{d-2}})(\xi_{t+1}),
$$

则取像后的词为对应 $Q(J_v)$ 的复合，其自然界恰是 $Q(\Delta(W))$。
membership 截断等价随 $Q$ 搬运。因此 marks 保持其实际自然截断证书，
并非仅仅保留了符号 `*`。

首三点的 linedness 见证可重新指定；上述行边、marks 及其证书不依赖这份
见证的身份。这正是定量桥允许替换有限参数的条件。

## 3. 三次自复合的具体小窗口

沿用[第一轮降根反馈](<../iblp-030-laver-20261014/root-lowered-bms-feedback.zh-CN.md>)
的记号

$$
b=K(j),\quad W=L_3(b),\quad
a=L_3(\mu),\quad \tau=L_3(\theta_5).
$$

已有实际点像及严格顺序为

$$
\operatorname{crit}(W)=\kappa_2,\qquad
W(\kappa_2)=\theta_6,\quad W(\theta_6)=a,\quad W(a)=\tau,
\tag{6}
$$

$$
\kappa_2<\theta_6<a<\tau<\theta_7<\kappa_4.
\tag{7}
$$

因此 $W$ 和普通复合 $W\circ W$ 均固定首两点。三次定量调用如下；
$W^2(S)$ 表示将全部数据依次取两次 $W$-像，而非 application 项
$W(W)$ 对 $S$ 的作用。

| 实际实现 | 首三点 | cap | 本次参数 | 得到的首两点至 cap 的 linedness |
|---|---|---|---|---|
| $S$ | $(\kappa_0,\kappa_1,\kappa_2)$ | $\theta_6$ | $1$ | $G(1)$ |
| $W(S)$ | $(\kappa_0,\kappa_1,\theta_6)$ | $a$ | $G(1)$ | $G(G(1))$ |
| $W^2(S)$ | $(\kappa_0,\kappa_1,a)$ | $\tau$ | $G(G(1))$ | $G^{\circ3}(1)$ |

每一行的输入见证正是前一行的输出，因此调用定义性也逐次建立。
没有先假定 $G$ 在所有整数上都有定义。

写 $\tau=\gamma_r$，其中 $\gamma_i$ 枚举同一个全局代数的临界点。
同代数 linedness 计数引理给

$$
2^{G^{\circ3}(1)}\le r.
$$

因为 $\tau<\kappa_4=\gamma_{q(5)-1}$，有 $r<q(5)-1$，从而得到 (2)。

### 为什么不能无限重复同一个 W

这里有确定的第四步逃逸，不能只省略端点核对。由
$\theta_5=K(\kappa_3)$ 及 application 点像恒等式，

$$
b(\theta_5)=K(j)(K(\kappa_3))=K(j(\kappa_3))
=K(\kappa_4)\ge\kappa_4.
$$

因此

$$
W(\tau)=L_3(b)(L_3(\theta_5))
=L_3(b(\theta_5))\ge\kappa_4.
\tag{8}
$$

第四个 $W$-像实现的 cap 就是 $W(\tau)$，已经不能用于当前 $q(5)$
窗口。长链版本下面为每一段另取一个实际 $Q_i$，不用这个失效的无限重复。

## 4. 同代数任意两临界点的实际连接

Qi 引理 2.11 在同一合格 BLS 的两列点之间供应所需 owner。它不能被改写成
“同一 $\operatorname{Iter}(j)$ 的任意两个临界点之间都有指定临界点及
指定像的 owner”。既有定量证明 cut 分支使用的正是同一 BLS 中的两列，见
[原 marked 定量证明](<../../natural-mark-lemmas/marked_blp_proof.md>)。

本篇改用一个更直接的外部事实，再给出全部有限归纳。
[Dougherty 第二篇第 3 节开头，PDF 第 10 页](https://arxiv.org/pdf/math/9503204#page=10)
记载：令 $e_n=j_{(2^n)}$，则

$$
\operatorname{crit}(e_n)=\gamma_n,\qquad
e_n(\gamma_n)=\gamma_{n+1}.
\tag{9}
$$

这里 $j_{(k)}$ 是 k 个 j 左结合的 application 项，不是普通复合幂。
所有 $e_n$ 均属于同一个 $\operatorname{Iter}(j)$。

对任意有限整数 $a<b$，定义实际 application 项

$$
L_{a,a+1}=e_a,\qquad
L_{a,b+1}=e_b(L_{a,b}).
\tag{10}
$$

对 $b-a$ 作有限归纳，证明

$$
\operatorname{crit}(L_{a,b})=\gamma_a,\qquad
L_{a,b}(\gamma_a)=\gamma_b.
\tag{11}
$$

基础步就是 (9)。归纳步中 $a<b$，故 $e_b$ 固定 $\gamma_a$。
application 的临界点公式给

$$
\operatorname{crit}(e_b(L_{a,b}))
=e_b(\operatorname{crit}(L_{a,b}))=e_b(\gamma_a)=\gamma_a.
$$

在相同的固定点上读取点像恒等式，有

$$
e_b(L_{a,b})(\gamma_a)
=e_b(L_{a,b})(e_b(\gamma_a))
=e_b(L_{a,b}(\gamma_a))
=e_b(\gamma_b)=\gamma_{b+1}.
$$

这完成 (11)，并显式构造了每个所需连接，不增加共同 BLS 假设。
Laver–Steel 定理已经把当前代数的全部临界点列为有限下标的 $\gamma_n$。
因此对任意当前临界点 $z=\gamma_a<u=\gamma_b$，可取
$B=L_{a,b}$，得到 $\operatorname{crit}(B)=z$、$B(z)=u$。

具体说，若一份 $m$-linedness 的最后一段为

$$
\operatorname{crit}(A)=\kappa_0,\quad
A(\kappa_0)=x,\quad A(x)=z,
\qquad \kappa_0<x<z,
$$

则 $B$ 固定 $\kappa_0,x$。把最后一个 owner 换成 $B(A)$，就有

$$
B(A)(\kappa_0)=x,\qquad B(A)(x)=u.
$$

前面各段保持不变，段数仍为 $m$。若 $z=u$，无需替换。
因此，$(\kappa_0,\kappa_1,z)$ 的 $m$-linedness
可以在不减少段数的前提下延到任意较大同代数临界点 $u$。这里改变的是另行携带的 linedness
见证，不改变 $S$ 的行 owners 或 marks。

## 5. 沿有限长链复合 G

设给定一份实际有限链

$$
\theta_6\le u_0<u_1<\cdots<u_N<\kappa_4,
\tag{12}
$$

$$
\operatorname{crit}(Q_i)=\kappa_2,\quad
Q_i(\kappa_2)=u_i,\quad Q_i(u_i)=u_{i+1}
\qquad(0\le i<N).
\tag{13}
$$

若当前已有 $M_i$-linedness 的
$(\kappa_0,\kappa_1,z_i)$，且 $z_i\le u_i$，先由上一节的显式
连接延长至 $u_i$。这就是实现 $Q_i(S)$ 的首三点所需见证。定量桥给

$$
M_{i+1}=G(M_i),\qquad z_{i+1}=Q_i(\theta_6).
\tag{14}
$$

因为 $\kappa_2<\theta_6\le u_i$，严格单调性给

$$
u_i=Q_i(\kappa_2)<z_{i+1}
=Q_i(\theta_6)\le Q_i(u_i)=u_{i+1}.
\tag{15}
$$

所以输出满足下一段的输入条件。首两点始终不变，marks 的自然证书由第 2 节
保持。对有限 $i$ 归纳，同时证明各次 $G$ 调用的定义性及 (14)。
最后得到 $G^{\circ N}(M_0)$-linedness，末端不超过 $u_N<\kappa_4$，故

$$
q(5)>2^{G^{\circ N}(M_0)}.
\tag{16}
$$

特别地，先用原 $S$ 得 $M_0=G(1),z_0=\theta_6$，便得到 (3) 所需的
$N+1$ 次复合。

[已有 corridor 证明第 4 节](<../iblp-030-laver-20261014/lined-feedback-corridor.zh-CN.md>)
对每个 $3\le h\le C_{\rm line}+2$，提供 (12)—(13) 的实际链，其长度为
$N=D(T(h))$，起点为原文 promoter 的 $S_{\rm prom}(a)>\theta_7>\theta_6$，
末端严格低于 $S_{\rm prom}(\theta_7)<\kappa_4$。该处的 promoter 与本篇
九行语法种子 $S$ 不是同一个对象。

每一对 $z_i<u_i$ 都是当前全局代数的临界点，因此第 4 节已经逐对给出
实际 $B_i$。其项长可能极大，但这是对已确定有限整数所作的有限构造，
没有把该构造加入 pIBLP 一步展开，也没有要求计算它的完整文本。
由此 (3) 的全部连接条件都已供应。

## 6. 严格增长与尚未接通的比较

在定量桥使用的自然数势上归纳，可以同时证明每个已实现调用满足

$$
f_{\rm PP}(P,m)\ge g_0(m)=m2^m.
\tag{17}
$$

零项为等号；cut、transient 和 E-limit 分支向较小势作同参数调用，继承该
下界。E-successor 分支迭代 $x\mapsto f_{\rm PP}(\operatorname{cut}P,x)$
共 $2^m$ 次。每次递归调用的归纳下界至少为当前输入，第一次已至少为
$g_0(m)$，故整个迭代也满足 (17)。所有被使用调用的定义性来自同一个
有限势归纳，不需要预设全域单调性。

对本篇实际出现的参数，因而有 $G(m)\ge m2^m>m$。所以 (2) 确实严格
加强原来的 pIBLP 接口 $q(5)>2^{G(1)}$，而 (3) 可以执行由 BMS 计算
确定次数的自反馈。

但是 (17) 只有初等增长的通用底线，没有建立 $G$ 支配 BMS 的 $D$、
$T$ 或 $F_\Lambda$。因此本篇没有完成 pIBLP 数值接口与最佳显式
BMS–FGH 界之间的比较。父包增加、记号的序型比较，以及两条分别低于
$q(5)$ 的不等式，都不能代替这个仍需证明的数值支配。

本篇是纸面有限构造，没有计算 $G(1)$ 的十进制值，没有运行巨型固定指标
下降，也没有修改 pIBLP 展开器。
