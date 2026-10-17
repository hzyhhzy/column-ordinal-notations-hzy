# 第三组：原版 IBLP 大初值的带标记 modify 次数界

本篇使用 ZFC + I3。初值由固定原版 IBLP 的完整基本列构造；后续次数属于 **paper-guard 短 $M_\star$ 加完整冻结扫描及 cut**。入口保留全部 marks，允许后续出现有效多因子标记补全。

## 1. 原证明直接给出的自然初值

令 $R=I[0][3][0]$，其六行是

    01:1; 012:1; 0123:2; 234:1; 2345:2; 456:1.

根没有 marks。令 $L=C_{\rm line}$，即[第二组](02-bms-feedback.zh-CN.md)式 (1) 的实际 Qi 长链长度。定义

$$
N_0=2^L,\qquad L_1=2^L-1,\qquad N_1=2^{L_1},
$$
$$
S_*=R[N_0][N_1].
\tag{1}
$$

这里两个基本列步骤都是**原版完整展开及 legacy guard**。原入口证明逐指标成立，故可以直接花完第一条当前链的 $L$ 段，再花第一步返回的 $L_1$ 段，得到这个自然初值。无须选定一个十进制大数。

一般地，对

$$
2\le k\le2^L,\qquad 2\le n\le2^{\,2^L-1},
\tag{2}
$$

指定的原版 $R[k][n]$ 都有下述自然语义入口。若希望两个指标相同，也可取 $S_{\rm diag}=R[N_0][N_0]$，因为 $L\le2^L-1$。

设从一个这样的初值 $P$ 出发，直到空式的完整短 $M_\star$ 次数为 $\mu(P)$，cut 次数为 $\delta(P)$，两者之和为 $\tau(P)$。一轮扫描中的内部插点不另计一步。则

$$
\boxed{\delta(P)<q(5),\qquad
\mu(P)\le\tau(P)<2^{q(5)}.}
\tag{3}
$$

尤其 (3) 适用于 $P=S_*$。这保留了原证明给出的自然入口和准确计数方向。它还没有把 $\mu$ 或 $\tau$ 与整个 $R$ 的 Hardy／FGH 作比较。

## 2. 规则的准确范围

非空项若是真后继，或者首次完整复制的全部地址检查失败，则 cut。否则对末行作一次普通短复制，源区间为 $[p,e)$，使用 paper guard；再执行原来规定的完整冻结扫描：旧行先处理冻结 marks，再 native，新 family 跳过。扫描允许多因子词和有效标记补全。

定义域失败包含 $p=0$：不存在源第 0 行，不能把 Python 负下标当作合法来源。扫描只遍历本轮入口的有限旧行及有限下降祖先链，所以单步有限。

paper guard 与原版 legacy guard 的一般等价性未证明。本组只在两个初始化宏里逐项证明两者一致；后续轨道的定理使用 paper guard。

## 3. 同一代数、精确端点的完整包供给

取 application 项

$$
K=j_{(11)},\quad b=K(j),\quad c=K(b),\quad
d=c(K),\quad A_*=c(d),\quad Q=A_*(K).
$$

标准有限点表给

$$
A_*(\kappa_0)=\kappa_2,\quad A_*(\kappa_1)=\kappa_3,\quad
A_*(\kappa_2)=\theta_6,\quad A_*(\kappa_3)=\theta_7,
$$

并有严格上界

$$
A_*(<\theta_6)<\theta_8<\kappa_4.
\tag{4}
$$

把原来的实际 $L$-line $(\kappa_0,\kappa_1,\theta_5)$ 先取 $K$ 像，再取 $Q$ 像，得到准确匹配根末完整包的

$$
L(\theta_6,\theta_7,A_*(\theta_5);L),\qquad
A_*(\theta_5)<\kappa_4.
\tag{5}
$$

根 $R$ 的六个 owners 为 $j,j,K,b,K(K),c$。最后的完整包是单行，起点 $\theta_6$、cap $\theta_7$，包括其隐含端点。恰好使用 (5)，逐段 E 倍增产生 $2^L$ 份完整包；保留前 $k$ 份、执行明确的 $k-1$ 次 raw 短复制，删控制行，再扫描和抽取，得到准确原版 $R[k]$。

这里是指定次数的有限构造；没有运行未知次数的 modify 来寻找下一个特殊形状。

## 4. 第二次展开的当前链来自哪里

令 $V=d(K)$、$B=V(K)$。实际点像提供

$$
L(\theta_5,\theta_6,\chi;L),\qquad \theta_6<\chi<\theta_7.
$$

根的最后 owner $c$ 另给一段 $L(\mu,\theta_5,\theta_6;1)$。使用保留原前缀的指数链乘法，得到 $2^L$ 段；删除原来第一段，留下

$$
L(\mu,\theta_6,\chi;2^L-1).
\tag{6}
$$

这正是根倒数第二行所需的 shadow，而非任意更换首点的数值预算。

在第一次 raw 森林中，这条 shadow 的端点及见证随完整相邻源块一起被同一 owner 输送。每轮的内部 shadow 端点低于该包 cap，包 cap 不高于本轮活动第一像，故取像后仍低于旧总 cap。最终控制行被删去，暴露的末行正好是被输送的倒数第二行。

首次 native-only 扫描保留该末行的中央边界和隐含 cap：若插入宽度为 $t$，core 长度与步长分别从 $(h,s)$ 变成 $(h+2t,s+t)$，原中央坐标的新位置仍为
$(h+2t)-(s+t)$。提取还保留末行和 cap，不会修补这个末 owner。

因此每个 $R[k]$ 得到位于其**准确新包端点**的 $2^L-1$ 段当前链。它可以供给第二次最多 $2^{\,2^L-1}$ 份包，证明 (2) 的数值范围。第二次初始化之后不需要再生第三条 shadow，故本结论不预设无限预算闭包。

完整证据为[实际入口](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-initializer.txt)第 1–6、15 节、[装饰 shadow 森林](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-shadow-forest.txt)和[前缀保留的链代数](proofs/scratch/iblp-I-to-I0-20261016/local-budget-algebra.txt)第三节。

## 5. 为什么可以保留自然 mark 语义

proper mark $y$ 的准确非终点词为 $W=F_{v_0}\circ\cdots\circ F_t$。自然 membership 截断要求

$$
F_r\equiv_{\Delta(W)}W,\qquad
\Delta(W)=(F_{v_0}\circ\cdots\circ F_{\rm prev})(\theta_{t+1}),
$$

其中 $\theta_y<\Delta(W)\le\theta_{y+1}$。它不是普通函数逐值限制。

**修补引理。** 若 $\operatorname{crit}(G)=c$，则 $G(F)\equiv_c F$。对 $x,z\in V_c$，$G$ 固定二者，而 application 协变及初等性给

$$
x\in G(F)(z)\iff x\in G(F(z))\iff x\in F(z).
$$

不要求 $F(z)\in V_c$。

**因子后继闭合抽取。** 所选行集若保留所有 core/mark/trace 引用、末行及 cap，并对每个 mark 因子 $v$ 也保留物理后继 $v+1$，则原自然证书在端点修补后保持。

证明：每个因子的 owner、下一物理点和整个 $\Delta(W)$ 不变。若 carrier $r$ 的旧 cap $c$ 被延长为 $c'>c$，用实际 $\operatorname{crit}(G)=c,\ G(c)=c'$ 的 transporter 替换为 $G(F_r)$。proper 性给 $\Delta(W)\le\theta_r<c$，于是上面的引理保留所需 membership 等价。末行及 cap 被保留，所以末 owner 不修补。[完整证明及 transporter 构造](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-extraction.txt)

第一次森林无继承 marks；完整 native family 一起选择。出生 direct mark 的因子和其物理后继同在该 family，满足闭合条件。

第二次森林的 live 完整包由最后两个完整 native family 组成。其 mark 只有一个非终点因子，而且配对源均不低于活动最小值。每轮 short copy 的新 pivot 正好位于新复制段开头，因此下一源段仍是这个性质的整体像。所有复制 marks 只走 all-high 分支，legacy 与 paper guard 在本次宏中一致。所选完整包、其删控制行前缀及所选 source 的像保持因子后继闭合；第二次冻结扫描 quiet。

据此，所有 (2) 中的原版 $R[k][n]$ 都取得自然 membership 证书、普通实际行、Sat、proper 准确 marks 和正 mark 源，cap 严格低于 $\kappa_4$。[独立入口归纳](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-initializer.txt)及[原版森林／quiet 证明](proofs/scratch/iblp030-8h-20261015/original-audit-root-forest-interface.txt)

## 6. 后续短 M 闭包

对于上述证书，合法 paper 短复制及完整扫描保持自然 membership、Sat、准确 traces、ordinary 行边、同一生成元及全局 cap。末 owner 从 $J$ 变成 $J(K')$，扫描不再改变它。合法 cut 也保持证书。

这里确实调用了带标记局部定理，具体复制词、自然界、Sat 内部包传送和扫描证明全部随附于[自然标记引理索引](common/natural-marks.zh-CN.md)。所用局部引理不需要某个固定三元组同时有全部有限 linedness，也不调用全局 I2 标准域良序定理。

## 7. 有限表势函数给出准确次数

当前 cap 写为 $\gamma_r$。末 owner 临界点严格低于 cap，其有限 Laver 商代表为 $1\le a<2^r$。置

$$
\Phi=2^{r+1}-a.
\tag{7}
$$

有限 Laver 表有 $a*_r b>a$（$a<2^r$）。证明对 $a$ 由大到小归纳，再对列号归纳：首列为 $a+1$；前值若为顶元则下一值回到 $a+1$，否则由更高行归纳得到严格大于前值。

成功 $M_\star$ 保持 cap，末 owner 商变成 $a*_r b$，故 $\Phi$ 至少减 1。cut 使 $r'<r$，不需要比较新旧 owners，因为

$$
\Phi_{\rm new}\le2^{r'+1}-1\le2^r-1
<2^r+1\le\Phi_{\rm old}.
\tag{8}
$$

最后两行以下单独按

$$
(01)(012)\to(01)(12)\to(01)(02)\to(01)\to0
$$

实现；前两步仍是末 owner application，后两步 cut，空式势为 0。因此单步可定义性加整数势严格下降，证明整个运行有限，并有

$$
\tau(P)\le\Phi(P)<2^{r_0+1}<2^{q(5)}.
$$

cap 的初始下标满足 $r_0<q(5)-1$。每次 cut 都进一步降低该下标，最后删空可按一个终止等级计入，故
$\delta(P)\le r_0+1<q(5)$。由此得到 (3)。

这个势也给原五行初式 $I$ 及六行 $R$ 的相同 paper 短 $M_\star$/cut 次数界：它们已有同一代数、cap 小于 $\kappa_4$ 的自然实际实现。五行初式唯一 mark 的 carrier 与因子 owner 都是 $j_{(11)}$。[五行初始化](proofs/output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md)

## 8. 可以和不可以读出的下界

可以写 $q(5)>\delta(S_*)$，以及 $\tau(S_*)<2^{q(5)}$。若 $\tau(S_*)>0$，后者也给 $q(5)>\log_2\tau(S_*)$。本证明没有删除这层指数。

这是一条原版巨大初值与可定义 modify/cut 过程的定量联系。把这些次数进一步压到某个原版 $R$ 的 Hardy／FGH 以下仍需完整变指标模拟；仅有入口很高、前两次指标很大或序型相同都不够。第一组的有限类型 FGH 证明不以这个尚缺比较为前提。
