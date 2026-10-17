# pIBLP 给出的 q5 增强下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。假设 ZFC + I3，固定同一个生成元及其代数
$\operatorname{Iter}(j)$。本篇将 pIBLP 的有限参数递归实际接回 BMS
行数反馈，得到比此前明确记录的 FGH 下界严格更大的数值下界。

令 $\Lambda=\lim(\mathrm{BMS})$、$g=F_\Lambda$，令
$C=C_{\rm line}$ 为此前文献长链常数。则

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(g(g(2^C))\bigr).}
\tag{A}
$$

采用 $(\Lambda+\omega)[x]=\Lambda+(x+1)$。这里
$q(5)$ 是普通二元 Laver 表首行周期首次达到 $32$ 的阶参数，
不是表的元素数 $2^{q(5)}$。结论为纸面推导，尚未 Lean 形式化。

另有直接保留 pIBLP 计算的界。设 $S$ 为当前九行种子，
$G(m)=f_{\rm PP}(S,m)$，置

$$
X=g(g(2^C)),\qquad e_0=1,\quad e_{r+1}=2^{e_r}.
$$

则以下指定调用均有定义，并且

$$
\boxed{q(5)>2^{G^{\circ(e_X+1)}(1)}.}
\tag{B}
$$

$G$ 是父包有限参数增长递归，不是固定 `[2]` 的总步数，也不是按定义
等于 pIBLP 的 FGH。本篇未比较 (A) 与 (B) 两个右端的大小。

## 1 公理条件和实际实现

使用 I3 嵌入 $j:V_\lambda\to V_\lambda$，所有 row owners、链段及
取像后的拥有者均留在同一个 $\operatorname{Iter}(j)$。application
$a(b)$ 与普通复合 $a\circ b$ 始终区分。

全局临界点枚举为 $\gamma_0<\gamma_1<\cdots$，沿用
$\kappa_4=\gamma_{q(5)-1}$。一份 $M$-lined 的
$(\kappa_0;\kappa_1,\ldots,z)$ 见证若满足 $z<\kappa_4$，
同代数计数给 $\gamma_{2^M}\le z$，因而

$$
q(5)>2^M.
\tag{1}
$$

九行种子 $S$ 的实际首三点是
$(\kappa_0,\kappa_1,\kappa_2)$，cap 为 $\theta_6<\kappa_4$，
初始 linedness 参数为 1。其 ordinary 行、Sat、proper marks、正源及
自然 membership 截断证书见
[种子完整证书](<../iblp-030-laver-20261014/same-owner-L3-sat-closure.zh-CN.md>)。

[父包定量定理](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.zh-CN.md>)
对当前实现及当前有限参数同时证明计算定义性和 linedness 输出。
因此 $L=G(1)$ 有定义，并给出实际
$(\kappa_0;\kappa_1,\ldots,\theta_6)$ 的 $L$-段链。
不预设 $G(m)$ 对所有整数全定义。

## 2 pIBLP 提供严格更长的初始化

设 $P_i$ 是 $S$ 的前 $i$ 行，记
$H(m)=f_{\rm PP}(P_4,m)$。已有小图案归约严格给出
$H(1)=C$，其中 $C$ 可不用嵌入术语而定义为

$$
\begin{aligned}
g_0(x)&=x2^x,& u_0(x)&=g_0(x),\\
u_{r+1}(x)&=u_r^{\circ2^x}(x),& v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),& C&=w(w(1)).
\end{aligned}
\tag{2}
$$

关键的一次有限辅助复制是

```text
P4 = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2
P5 = P4(5,3,2,1,0)3
E_P5(1) = P4(5,2,1,0)2(6,*5,2,1,0)2
R = P4(5,2,1,0)2
```

$P_5$ 是 E-limit；$R$ 是 $E_{P_5}(1)$ 的字面前缀，且为
E-successor，满足 $\operatorname{cut}R=P_4$。两处完整复制 guard
都通过。辅助 E 复制不扫描 native 或 marks。

在同一个实际实现内，定量函数对字面前缀不减；该性质由有限表势归纳得到，
不使用其对数值参数的单调性。故

$$
\begin{aligned}
L&\ge f_{\rm PP}(P_5,1)
=f_{\rm PP}(E_{P_5}(1),1)\\
&\ge f_{\rm PP}(R,1)
=H^{\circ2}(1)=H(C).
\end{aligned}
$$

每个有实际定义证书的调用均满足
$f_{\rm PP}(P,m)\ge m2^m$，由有限求值树归纳可证。因此

$$
\boxed{L\ge H(C)\ge C2^C>C.}
\tag{3}
$$

这里 $H(C)$ 的定义性来自 E-successor 双块构造，不是先假定同一首三元组
能支持任意参数。完整推导及有限数组证书见
[严格初始化增量](<audit-piblp-strict-Cline.zh-CN.md>)。

## 3 将新增链长送回 BMS 行数

沿用实际 application 项 $E=L_3(K)$，其已证点像为

$$
E(\kappa_0)=\kappa_2=k,\quad E(\kappa_1)=\theta_6=a,\quad
E(\theta_6)=\tau=b<\theta_7=c<\kappa_4.
\tag{4}
$$

将第 1 节的 $L$-段链全部取 $E$-像，得到
$(k;a,\ldots,b)$ 的 $L$-段链。
[统一前端插入引理](<../iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md>)
于是供应高度

$$
h_*=L+2
\tag{5}
$$

的闭合相容 fan，封口严格小于 $b$。输入链的末端恰为 $b$ 没有问题：
插入引理的输出封口严格低于该末端。

设

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil.
$$

由 $C\ge3$ 及 (3)，

$$
\rho(2^C)=2^C+C+4\le C2^C+2\le h_*.
\tag{6}
$$

因此新的合法入口不只是原来的 $C+2$ 行，而是已经足以支付输入 $2^C$
及其全部行数开销。

## 4 已有递归反馈的准确接口

记 $B_r=(0^r)(1^r)$、$R_h=(0^h)(1^h)(1^h)$，令
$D(h)$ 为 $R_h$ 反复取原 BM4 `[1]` 到空的步数，
$T(h)=D(h)+2$。原 BM4 `[1]` 等于新父表展示指标的 `[2]`。

使用以下两个既有接口。

第一，[强森林计数缓冲](<../iblp-030-laver-20261014/nested-bms-FGH-bound.zh-CN.md>)
给出

$$
h\ge\rho(x),\quad x\ge2
\ \Longrightarrow\ 
D(h)\ge e_{g(x)},\qquad T(h)\ge\rho(g(x)).
\tag{7}
$$

第二，定义有限层自然模板

$$
U_0=T,\qquad
U_{i+1}(h)=U_i^{\circ(D(U_i(h))+1)}(h),\qquad
m(h)=\lfloor\log_2D(T(h))\rfloor.
$$

对任何**已经实际初始化**的高度 $h\ge3$、封口低于 $b$ 的入口 fan，
[递归模板及短搬运端点定理](<../iblp-030-laver-20261014/small-period-endpoint-Sf.zh-CN.md>)
第 4.1 节给出

$$
q(5)>D(U_{m(h)+1}(h)).
\tag{8}
$$

旧文常写 $h\le C+2$，只是当时已供应的初始化范围；模板证明本身只读取
实际入口 fan。第 3 节已经为 $h=h_*$ 重新供应这一证书，所以这里没有把
一个仅限旧高度的数值不等式擅自外推。

端点构造先由一次独立的 $T(h)$ 生成有限整数 $m(h)$，再构造对应长度
的高共同根链，最后执行模板。它不让链长依赖最终输出，也不要求在一个固定
端点下同时存在任意长的链。模板的整背景自然性允许任意全局输入 fan，
而非仅允许旧 fan 的取像。

## 5 从反馈层数得到极限加 omega 的 FGH 界

令 $J_i(x)=F_{\Lambda+i}(x)$，即
$J_0=g$、$J_{i+1}(x)=J_i^{\circ(x+1)}(x)$。
有限层归纳由 (7) 给出

$$
h\ge\rho(x),\ x\ge2
\ \Longrightarrow\ U_i(h)\ge\rho(J_i(x)).
\tag{9}
$$

归纳步骤中令 $N=D(U_i(h))+1$，同时跟踪
$U_i^{\circ j}(h)\ge\rho(J_i^{\circ j}(x))$。由 (7) 有
$N\ge x+1$；额外迭代沿同一严格增值轨道处理，不需要假定
$U_i$ 的输入单调性。

对任意合法入口 $h\ge\rho(x)$，置 $x_2=g(g(x))$。两次使用 (7) 得

$$
D(T(h))\ge e_{x_2},\qquad m(h)\ge e_{x_2-1}\ge x_2+1.
\tag{10}
$$

这里 $x\ge2$，故 $x_2\ge4$。展开最外层
$U_{m+1}(h)=U_m^{\circ N}(h)$。第一轮由 (9) 已将高度提高到
至少 $\rho(x_2)$；后面至少还有一轮，并可对固定输入 $x_2$
再次使用 (9)。于是 (7)、(8) 给出

$$
q(5)>D(U_{m+1}(h))>J_m(x_2)
\ge J_{x_2+1}(x_2)=F_{\Lambda+\omega}(x_2).
\tag{11}
$$

详尽的额外迭代及端点审计见
[递归反馈的 FGH 转换](<audit-recursive-corridor-FGH.zh-CN.md>)。
将 $h=h_*$、$x=2^C$ 代入 (11)，由 (6) 得到 (A)。

## 6 与此前明确 FGH 界的严格比较

设 $t=F_3(256)$。此前已证 $C>4t$，其中
$F_2(x)=(x+1)2^{x+1}-1$、$F_3(256)=F_2^{\circ257}(256)$。
本次得到的严格比较是

$$
\begin{aligned}
F_{\Lambda+\omega}(g(g(2^C)))
&>F_{\Lambda+\omega}(g(g(t)))\\
&>F_{\Lambda+1}(g(g(t))).
\end{aligned}
\tag{12}
$$

第二步在同一输入上逐有限后继层比较即可。第一步需要专门的输入比较，
不是从 $2^C>t$ 直接假定任意 FGH 都单调。

标准 BMS 的基本列保留删尾前缀，且 $P[x]$ 是 $P[y]$ 的字面前缀
（$x\le y$）。同时良基归纳证明：$F_P(x)\ge x+1$、FGH 对字面
前缀不减，以及 $F_P(y)\ge F_P(x)+(y-x)$。此外
$B_s[n]=(0^{s-1})(1^{s-1})\cdots(n^{s-1})$（去掉全零最高行，$n\ge1$），
其前两列为 $B_{s-1}$。由此专门得到 $g$ 输入严格递增，再得到各
$J_i$ 和 $x\mapsto J_{x+1}(x)$ 输入严格递增，证明 (12)。
完整归纳见 [BMS 对角输入比较](<audit-BMS-diagonal-input-monotonicity.zh-CN.md>)。

若希望不在公式里保留文献常数 $C$，可保守放松为

$$
\boxed{q(5)>
F_{\Lambda+\omega}\!\left(
F_\Lambda\!\left(F_\Lambda\!\left(2^{F_3(256)}\right)\right)\right).}
\tag{13}
$$

这些比较针对已写明的 FGH 右端。没有宣称 (A) 已经超过此前一切未展开的
隐式递归下界，例如所有 $D(U_{m(h)+1}(h))$ 的旧参数值。

## 7 可重复的 pIBLP 数值反馈

从高度 $T(h_*)$、封口低于 $c$ 的实际 fan 出发，
[沿长链反馈构造](<../iblp-030-laver-20261014/lined-feedback-corridor.zh-CN.md>)
供应长度 $N=D(T(h_*))$ 的实际链

$$
\operatorname{crit}(Q_i)=k,\quad Q_i(k)=u_i,\quad Q_i(u_i)=u_{i+1},
\qquad \theta_6<u_0<\cdots<u_N<\kappa_4.
\tag{14}
$$

每个 $Q_i$ 固定 $\kappa_0,\kappa_1$。$Q_i(S)$ 是同一语法种子
的实际实现，首三点为 $(\kappa_0,\kappa_1,u_i)$，cap 为
$Q_i(\theta_6)<u_{i+1}$。所有 marks 及自然截断证书一同取像。

先用 $S$ 得到 $G(1)$-lined 的低根链。将其末端延至 $u_0$，再用
$Q_0(S)$ 得到参数 $G(G(1))$；依次重复，有限归纳得到

$$
q(5)>2^{G^{\circ(N+1)}(1)}.
\tag{15}
$$

每次调用的定义性都由该次实际证书给出。端点延长只替换另行携带的 linedness
见证的最后一段，不改动种子的 owners 或 marks。

这里所需的任意全局临界点间连接来自
[Dougherty 第二篇第 3 节开头](https://arxiv.org/pdf/math/9503204#page=10)
所记的标准事实：$e_n=j_{(2^n)}$ 满足
$\operatorname{crit}(e_n)=\gamma_n$、$e_n(\gamma_n)=\gamma_{n+1}$。
有限归纳令 $L_{a,a+1}=e_a$、$L_{a,b+1}=e_b(L_{a,b})$，便有
$\operatorname{crit}(L_{a,b})=\gamma_a$、$L_{a,b}(\gamma_a)=\gamma_b$。
这补足所需连接；不能仅引用适用范围为同一 BLS 列点的 Qi 引理 2.11。
完整反馈证明见 [pIBLP 自反馈](<quant-self-feedback.zh-CN.md>)。

由 (6)、(7)，$N\ge e_{g(g(2^C))}=e_X$。在 (14) 中只取前 $e_X$
段，便得到 (B)。因此已有的 pIBLP 接口不再只使用一次 $G(1)$，而是能
使用塔高为两层 BMS 对角计算结果的有限次数自复合。

## 8 结论范围与核验

(3) 是真正的 pIBLP 初始化增量；(A)、(12) 是新增的明确 FGH 下界与严格比较；
(B) 保留了更多 pIBLP 自反馈结构。它们仍未把整个 $S$ 的序型转换为 FGH，
也未证明原 IBLP $I[0][2]$ 或 $I[0][3][0]$ 的 FGH 受 $q(5)$ 控制。
全指标 pIBLP 的良序性不作为本篇前提。

有限核验包括一次 P5 辅助复制及 marks、短搬运端点、BMS 两列展开公式和
相邻基本项前缀。它们只是有限接口检查；全称结论来自以上归纳与所列纸面定理。
没有运行巨型固定指标下降或实际求值任何 FGH 大数。
