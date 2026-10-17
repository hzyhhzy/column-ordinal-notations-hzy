# 普通 L3 种子的完整 Sat 证书及后续短操作闭包

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本文审计的是
[八行 L3 初始化及第一次扫描](<ordinary-l3-native-mark-seed.zh-CN.md>)
所得的九行模式 $S$。结论不是仅仅“若干点像相符”：$S$ 满足已有普通
自然截断 Sat 闭包定理的全部输入条件。因此之后每次**合法**短复制加完整扫描、
cut，以及有限参数允许的 $E(1)$，都有真实实现。

这里的“合法”没有被省略：Sat 不保证部分复制映射处处有定义；不可复制项按规则
选择 cut。本文也不把这套短操作树的高度当作原 IBLP 或 BMS 的序型。

## 1. 固定实际实现与九行数据

假设 ZFC + I3，所有拥有者都取自固定的同一个 $\operatorname{Iter}(j)$。
沿用初始化文稿的真实项 $K,f,H,D_\beta$，而不是给它们另设抽象点像。
命名点按地址排列为

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,
\beta,\alpha,\zeta,\eta,\theta_6),\qquad 0,1,\ldots,10.
\tag{1}
$$

它们严格递增，且 $\theta_6<\kappa_4$。下表的完整行还要在 core 后补上
隐含端点 $r+1$。第 4 行的 mark 3 可取可不取；两种版本均满足本文结论。

| 行 $r$ | core | $L_r$ | marks | owner |
|---:|---|---:|---|---|
| 1 | $(0,1)$ | 1 | 空 | $j$ |
| 2 | $(0,1,2)$ | 1 | 空 | $j$ |
| 3 | $(0,1,2,3)$ | 2 | 空 | $K$ |
| 4 | $(0,1,2,3,4)$ | 2 | 空或 $\{3\}$ | $K$ |
| 5 | $(0,1,2,3,5)$ | 3 | 空 | $f$ |
| 6 | $(0,6)$ | 1 | 空 | $D_\beta$ |
| 7 | $(0,1,2,6,7)$ | 3 | 空 | $H$ |
| 8 | $(0,1,2,3,6,7,8)$ | 4 | $\{7\}$ | $H$ |
| 9 | $(0,1,2,3,6,7,8,9)$ | 4 | $\{7,8\}$ | $H$ |

全部 owners 的临界点都是 $\kappa_0$，与各行最小地址 0 一致。
初始首三点 $(\kappa_0,\kappa_1,\kappa_2)$ 的 1-linedness 由实际 $j$
实现；这不是全部有限参数的共同 linedness。

## 2. 普通行型及全部行边

采用 [Qi 的 Definition 2.6](https://arxiv.org/html/2501.06733v5)：行长应按
**加回隐含端点后的完整长度**计算。九行的完整长度依次为

$$
3,4,5,6,6,3,6,8,9.
$$

相应步长为 $1,1,2,2,3,1,3,4,4$，全是允许的普通行型。特别是第 4 行
完整长度 6、步长 2，是允许的长行；不能套用完整长度 4 必须步长 1 的限制排除它。

第 1、2 行是 $j$ 的前三、四个临界序列点。第 3、4 行使用

$$
K:\kappa_0\mapsto\kappa_2,\quad
\kappa_1\mapsto\kappa_3,\quad
\kappa_2\mapsto\mu,\quad
\kappa_3\mapsto\theta_5.
$$

第 5 行的全部边为

$$
f:\kappa_0\mapsto\kappa_3,\quad
\kappa_1\mapsto\theta_5,\quad \kappa_2\mapsto\beta.
$$

第 6 行使用 $D_\beta:\kappa_0\mapsto\beta\mapsto\alpha$。第 7、8、9 行
分别使用以下列表的前 3、前 4、全部 5 条边：

$$
H:\kappa_0\mapsto\beta,\quad\kappa_1\mapsto\alpha,\quad
\kappa_2\mapsto\zeta,\quad\kappa_3\mapsto\eta,\quad
\beta\mapsto\theta_6.
\tag{2}
$$

这同时核对了每一行的隐含端点，不只是可见 core 内部的边。

## 3. Sat、proper traces、正源及自然截断

为避免两个父函数混名，记

$$
\delta(r)=A_r[-2],\quad p(r)=A_r[-L_r-1],\quad e(r)=A_r[-L_r].
$$

只有 core 长度不超过 $2L_r$ 的中、短行执行 native；第 2、4 行不在此列。
其余行逐项满足：

| $r$ | $p(r)$ | $e(r)$ | $\delta(e(r))$ |
|---:|---:|---:|---:|
| 1 | 0 | 1 | 0 |
| 3 | 1 | 2 | 1 |
| 5 | 1 | 2 | 1 |
| 6 | 0 | 6 | 0 |
| 7 | 1 | 2 | 1 |
| 8 | 2 | 3 | 2 |
| 9 | 3 | 6 | 0 |

所以全部满足 $\delta(e(r))\le p(r)$，即 Sat。

全部非空 marks 的实际 traces 只有

$$
\begin{array}{c|c|c|c}
\text{owner 行}&\text{mark}&\text{完整 trace}&\text{owner 与非终点因子}\\\hline
4&3&(3,1)&K=K\quad(\text{可选})\\
8&7&(7,1)&H=H\\
9&7&(7,1)&H=H\\
9&8&(8,2)&H=H.
\end{array}
\tag{3}
$$

各 mark 都严格小于所在行，准确命中步长配对源；源地址为 1 或 2，严格大于行最小
地址 0。因此 proper、准确 trace、PosSource，甚至 NC 都成立。

自然截断规定：若非终点词为 $W=J_{v_0}\circ\cdots\circ J_t$，则

$$
\Delta(W)=(J_{v_0}\circ\cdots\circ J_{v_{d-2}})(\xi_{t+1}),
\qquad J_r\equiv_{\Delta(W)}W,
\tag{4}
$$

其中 $\xi_i$ 是 (1) 的地址 $i$ 对应点，$\equiv$ 为 Laver membership
截断。在 (3) 中词只有一个因子，且与 owner **全局相等**，故 (4) 自动成立。
这也覆盖了 direct mark 所需的完整紧后点界，不存在仅有较低截断的缺口。

## 4. 能直接调用的闭包，以及不能省的定义域条件

使用以下已有纸面引理的准确范围：

1. [自然截断语义](<../../natural-mark-lemmas/natural_trace_cutoff_semantics.md>)
   §§2—3 给合法 copy 的 full/low/high mark 闭包；
2. [Sat 入口完整包定理](<../../natural-mark-lemmas/sat_endpoint_packet_theorem.md>)
   §6 从 **Sat 父项的一次合法短 copy** 得到全部实际读非空记录的旧词的 Sat_rec；
   §§2—5 完成逐事件的整包、旧边、新边及自然截断证明；
3. [普通完整 marked BLP 合成](<../../natural-mark-lemmas/full_marked_blp_natural_cutoff_wellorder.md>)
   引理 3.1 将它们合成为短复制加左到右完整扫描的闭包；
4. [有限参数定量桥](<../iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md>)
   的证书类 $\mathcal C$ 表明这些局部引理只需当前实际证书，不要求某条标准生成历史。

本篇 §1—3 已给出 $S\in\mathcal C$，参数 $m=1$。于是：

- cut 到至少两行的前缀，保持同一类证书；
- 若原部分短复制映射在所需条目上有定义，一次短复制及其完整扫描有限完成，输出仍在
  $\mathcal C$，cap 不变，末 owner 由 $J$ 变成 $J(K')$；
- 复制采用正确的一基 `paper` mark guard，不能换成本地 `legacy` 少一位筛选；
- 若复制无定义，原本允许的操作是 cut。尤其原 `ap` 的 $p>0$ 条件也属于定义域；
  Sat 没有证明、也不需要证明每个对象都可复制；
- 对互斥类型判定中的 successor/limit 项，可用 $E(1)$。它只有一次辅助三点行复制，
  辅助复制的阈值映射总定义；1-linedness 足以构造其真实拥有者，首三点及其见证保留。

本种子的第一次短复制本身确实有定义，而非立即落入 cut：末行给
$p=3,e=6,n=9$，源行是 3、4、5；低地址 0、1、2 都出现于末行，复制映射为

$$
\varphi(0)=6,\quad\varphi(1)=7,\quad\varphi(2)=8,\quad
\varphi(x)=x+6\ (x\ge3).
$$

这覆盖三条源行的全部所需引用。此处只核对第一次，不把它外推为任意多轮都可复制。

最后一项不授权从这份证书任取全部 $E(k)$。固定首三元组的 1-linedness 与
“对所有有限 $k$ 同时有同端点见证”是不同条件；后者是原 I2 全参数良序文稿中
专门供应的数据。有限参数定量递归在需要增加 $m$ 时另由归纳构造、抽取和替换见证，
也不是直接把当前 $m=1$ 当成任意参数。

旧前缀因 Sat 且入口 record 为空而逐行静止；每条当时旧行只处理冻结的旧 marks，
native 新块跳过。因此一个 $M_\star$ 只执行一次复制、一次有限扫描，没有在其中
隐藏“反复 M 直到某种型”的归约循环。扫描的几何合法性由上述整包引理给出，
不靠测试枚举后追加过滤。

## 5. 固定 E1／M／cut 计算的终止及两个不同计数

现在固定一个实际算法：两行为终点；其余项先处理原不可复制分支为 cut，
successor/limit 取 $E(1)$，其余可复制项取 $M_\star$。也可允许在每个非终点
主动选择 cut；以下界对每条这样选择的路径都成立。

所有点和拥有者一直留在同一个 $\operatorname{Iter}(j)$。令
$\gamma_0<\gamma_1<\cdots$ 枚举其临界点，写当前 cap 为 $\gamma_r$。
沿用周期阈值约定

$$
q(5)=\min\{m:\pi(m)\ge 2^5\},\qquad
\kappa_4=j(\gamma_4)=\gamma_{q(5)-1}.
\tag{5}
$$

初始 cap 为 $\theta_6=\gamma_{r_0}<\kappa_4$，故

$$
r_0\le q(5)-2.
\tag{6}
$$

cut 严格降低 cap，其他上述步骤保持 cap。设路径含 $C$ 次 cut、全部操作数为 $L$，
终端 cap 为 $\gamma_{r_{\rm end}}$。则

$$
C\le r_0-r_{\rm end}\le r_0<q(5).
\tag{7}
$$

全部操作不能用这个线性界。若非终端末 owner 在大小 $2^r$ 的 Laver 商中余类为 $a$，
真实行的临界点低于 cap 给 $1\le a<2^r$。定义

$$
\Phi=2^{r+1}-a.
\tag{8}
$$

有限 Laver 表对 $a<2^r$ 满足 $a*_r b>a$。所以一次 $M_\star$ 严格降低
$\Phi$；一次 $E(1)$ 的语义是两次 application，且中间、最终临界点都低于
cap，故也严格降低。cut 把 $r$ 降为 $r'<r$，而

$$
\Phi'\le2^{r'+1}-1\le2^r-1<2^r+1\le\Phi.
$$

将两行终点的势设为 0，每条边仍至少降 1。由此同时得到终止和

$$
\boxed{L\le\Phi(S)<2^{r_0+1}\le 2^{q(5)-1}<2^{q(5)}.}
\tag{9}
$$

有限表增值性和商—application 对应的完整计数论证见
[直接步数桥](<../iblp-laver-bms-20261013/direct-step-bridge.zh-CN.md>)。每次完整扫描内部的
单个补全事件不另算作 (9) 的一个严格减势步骤；计的是 $E(1),M_\star,\mathrm{cut}$。

若确需数到空式，可在固定首两行处追加四个明确无标记步骤：

$$
(01)(012)\to(01)(12)\to(01)(02)\to(01)\to\varnothing.
\tag{10}
$$

前两步的末 owner 依次为 $j(j)$、$(j(j))(j)$，cap 仍为 $\kappa_3$；
随后两次 cut 降低 cap。这四步逐项点像已在
[短尾计数第 6 节](<short-tail-cofinality.zh-CN.md#6-六行根的固定指标计数与周期界>)
证明。给真正空式赋势 0，同样的 (7)、(9) 可用于到空的计数；没有把保护首两行的
Sat 定理越界应用到这段尾部。

## 6. 这尚未给出的强度结论

以上建立了一个真正发生 native 与 mark 传播、其后仍可长期自然计算的小 cap 种子。
它不像旧无主零端口方案那样在首次复制就失去 owner，也不像 $L=2$ 的短控制行那样
超出普通 BLP 行型。

但是，固定 $E(1)/M_\star/\mathrm{cut}$ 的每个节点只有有限个孩子，而 (9) 给定点
的有限深度。因此不能把它的操作树 rank 自动解释为 BMS 或 IBLP 的极限序型。
同样，(7) 只给 cut 计数上界，不能无证明地将全部 $M_\star$ 次数当成 cut 次数。
若要取得结构性超 BMS 数值下界，还要给一个明确的全指标基本列系统，以及其固定指标
计算到本自然计算的计数保持模拟；或者直接证明 $E$ 层的所需强度。

可以调用既有有限参数定量定理得到另一条严格但尚未比较的结论：

$$
q(5)>2^{f_\star(S,1)}.
\tag{11}
$$

理由是 $S\in\mathcal C$ 给 $(\kappa_0,\kappa_1,\theta_6)$ 为
$f_\star(S,1)$-lined，再用该定理的 linedness 计数引理和 $\theta_6<\kappa_4$。
这里 $f_\star$ 是已明确定义的递归计算，不是把未知次数的连续 M 打包成新的“一步基本列”。
没有另证增长下界前，(11) 本身也不等于完成“超过 BMS”的任务。

**独立审计。** t3_audit 完整阅读所用普通 Sat、自然截断和辅助 E 依赖后，
独立重算全部行边、Sat 三元组和 mark traces，并核对了合法短复制的条件、
固定 $E(1)$ 对 1-linedness 的使用、单步有限性及 (7)—(9) 的势函数计数。
其审计与本文一致；没有用有限程序样例代替这些全称闭包引理。
