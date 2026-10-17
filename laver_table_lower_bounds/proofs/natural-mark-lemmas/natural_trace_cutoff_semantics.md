# 末因子后继输送界：无内部邻接的自然 mark 语义

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-09-07。本文只讨论普通带标记补全 BLP。它采用一条由实际 transfer 自然
确定的截断界，证明全部合法复制分支的语义闭包，并证明一旦实际整包输送
成立，补全的全部读值和新 mark 截断自动得到保证。不修改原操作，不删除
marks，不将界取为 0，也不把尚待验证的包输送作为已经完成的结论。

这一自然界比 `marked_variable_cutoff_semantics.md` 中任意 Γ>目标的语义更强。
特别地，direct mark 仍使用原 note 的完整 θ_(y+1) 界，因此该稿的 direct
低界局部反例不满足本稿输入。

## 1. 自然界的定义及准确范围

设 owner F=j_r 的 proper mark y 的准确实际 trace 为
$$
(v_0=y,v_1,\ldots,v_{k-1}=t,\delta),\qquad
W=j_{v_0}\circ\cdots\circ j_{v_{k-1}}.
$$
令 S_0=id，S_i=j_(v_0)∘⋯∘j_(v_(i−1))。定义
$$
\boxed{\Delta(W)=S_{k-1}(\theta_{t+1}).} \tag{1}
$$
其中 θ_(t+1) 指当前 BLS 的下一列，未必是末因子行中 p(t) 后的 source。
自然 mark 语义为
$$
\boxed{F\equiv_{\Delta(W)}W.} \tag{N}
$$
所有截断仍为 Laver membership 截断，括号 E(K) 表示 application，圆圈表示
普通复合。

**引理 1.1。** 不要求内部 +1，已有
$$
\theta_y<\Delta(W)\le\theta_{y+1},
\qquad
\Delta(W)=\min_{0\le i<k}S_i(\theta_{v_i+1}). \tag{2}
$$
并且 Δ(W)=θ_(y+1) 当且仅当该 trace 的全部内部边具有 +1 邻接。

**证明。** 若 p(v_i)=v_(i+1)，令 e(v_i) 是其后下一 source。严格递增整数
core 给 e(v_i)≥v_(i+1)+1，而行边给
$$
j_{v_i}(\theta_{e(v_i)})=\theta_{v_i+1}.
$$
所以 j_(v_i)(θ_(v_(i+1)+1))≤θ_(v_i+1)，且等号恰在 e(v_i)=v_(i+1)+1
时成立。左复合严格递增的 S_i，得到式 (2) 中各项沿 i 递减。准确 p 链给
S_i(θ_(v_i))=θ_y，每一项因此都严格高于 θ_y。有限递减链首末相等，当且
仅当每一步都相等，这恰是内部 +1。direct 情形链无内部边，所有结论均成立。
证毕。

因此 (N) 是原 note 语义在非邻接 trace 上的明确扩展，并在内部邻接成立时
与原语义完全一致。这个界由实际列和 factor owners 确定，不需要另猜一个界。

若 W=P∘K，且 K 是以某一非终点开始的非空尾词，则直接由定义有
$$
\Delta(W)=P(\Delta(K)). \tag{3}
$$

## 2. 合法 full 与 low 复制

活动嵌入记为 E，临界点 c=θ_C，复制根 a；假设普通行和 canonical 基数复制
合法，marks 按原 PDF 的规则保留。实际新词使用
`copy_trace_word_identification.md`。每枚输入 mark 要求 (N)，不要求内部 A。

**全因子复制。** 所有非终点因子都在复制区，故末因子 t 与其后继列同步复制：
$$
\Delta(E(W))=E(\Delta(W)). \tag{4}
$$
原 F≡_(Δ(W))W 经 application 就给新语义。终点 δ 不必在复制区。

**low。** 写 W=P∘K，K 首因子 u<C 是首次低于 a 的非终点，H=E(P)。
新词为 H∘K。K 的全部因子及末因子下一列均在未变旧前缀，因此
$$
\Delta(H\circ K)=H(\Delta(K)). \tag{5}
$$
引理 1.1 给 Δ(K)≤θ_(u+1)≤c。应用原 mark 后的有效界是
E(Δ(W))=H(E(Δ(K)))。又 E(K)≡_cK，普通左复合 H 将这个替换输送到 H(c)。
因为 E 对序数不减，式 (5) 同时不超过 H(EΔ(K)) 与 H(c)，遂得到新语义。
P 为空时同样成立，包括 u=C−1、Δ(K)=c 的边界。

这一步不需要 Δ(K) 被 E 固定；当 Δ(K)=c 时一般并不固定。

## 3. high 复制：三份界都自动覆盖新的自然界

写 W=P∘K，K 的首因子为 C≤u<a，H=E(P)，z=φ(u)<n。活动行被引用的
mark z 的实际词为 Q，其终点是 u，输入自然证书为
$$
E\equiv_{\Delta(Q)}Q. \tag{6}
$$
新词为 H∘Q∘K。Q、K 全部因子及最后下一列均留在旧前缀，所以新自然界是
$$
D:=\Delta(H\circ Q\circ K)=H(Q(\Delta(K))). \tag{7}
$$
一般传递法保证的三个界为
$$
E(\Delta(W)),\qquad H(E(K)(c)),\qquad H(\Delta(Q)). \tag{8}
$$
下面逐一证明 D 不超过这些界，不使用复制输出内部邻接。

令 s 为 Q 的末因子，故 p(s)=u。由行边及 e(s)≥u+1，
$$
Q(\theta_{u+1})\le\Delta(Q).
$$
再由 Δ(K)≤θ_(u+1)，得到
$$
Q(\Delta(K))\le\Delta(Q). \tag{9}
$$
因此 D≤H(Δ(Q))。

输入 Δ(K)≤θ_(u+1)≤θ_z<Δ(Q)，确在 (6) 的界内。若 (9) 严格，则弱截断
读值给 E(Δ(K))=Q(Δ(K))；若等于界，则 membership 至少给
E(Δ(K))≥Δ(Q)=Q(Δ(K))。两种情形统一为
$$
E(\Delta(K))\ge Q(\Delta(K)). \tag{10}
$$
所以 D≤H(EΔ(K))=E(PΔ(K))=E(Δ(W))，覆盖第一个界。

最后处理 Second 替换界，避免默认它自动足够。设旧 source owner 中 mark
的步长源为 δ，紧后的 source 条目为 d。正确 PDF high guard 给 δ<d<C。
该条旧行边的目标严格在 y 之后，因此
$$
F(\theta_d)\ge\theta_{y+1}\ge\Delta(W).
$$
由于 θ_d<θ_y<Δ(W)，旧自然弱语义给 W(θ_d)≥Δ(W)。这里仅用了 membership
下界，没有把界上方的像当作相等。由 W=P∘K、Δ(W)=PΔ(K) 和 P 严格递增，
得到 K(θ_d)≥Δ(K)。E 固定 θ_d，故
$$
E(K)(\theta_d)\ge E(\Delta(K))\ge Q(\Delta(K)).
$$
又 θ_d<c，严格单调性给
$$
\boxed{E(K)(c)>Q(\Delta(K)).} \tag{11}
$$
所以 D<H(E(K)(c))，覆盖剩下的界。

原 source 证书应用 E、Dougherty Second 的
E(K)≡_(E(K)(c))E∘K，以及 (6) 的普通复合输送，分别使用 (8) 的三个界。
式 (9)—(11) 证明它们均覆盖 (7)，故 high 新 mark 满足 (N)。空 P 时 H=id，
全部论证仍成立。没有固定原 source 的 θ_(y+1) 截断，也没有调用最终 A。

**定理 3.1（自然语义的完整 copy 闭包）。** 合法连续 copy 保持全部原规则
所保留 marks 的自然语义 (N)，不要求父或子内部 +1、Sat、RowAncestor，
也不要求复制后靠扫描降低某个固定需求界。满区、low、high 已全部覆盖。

## 4. cut、native、正确 compTo 的旧标记继承

cut 不改变任何保留 mark 的词和末因子下一列，故保持 (N)。普通 native 的
已证公式保留旧基行 p 与 owner；继承到拆分行的旧 marks 保留其原词。
某个旧因子行之后插入新点时，其旧头基数本身保持，当前下一列只可能下降。
因此每个继承旧 mark 的新自然界不大于保存的旧界，(N) 仍成立。

这句话不意味着应丢弃旧证书：在一次扫描内保存入口的更高历史界，后面的
实际 compTo 会使用它。当前较低 Δ 与历史较高证书可以同时存在。

native 新 direct marks 的因子 owner 与本行 owner 全局相同，故满足其
自然界 θ_(y+1)。正确成对 compTo 保留旧 p、owners 与旧列值，因而也保留
旧证书；对新 marks 的证明见下一节。

## 5. 一旦整包已证，全部补全读值和新自然界自动成立

固定扫描入口某个旧 mark 的准确词 W=P_t∘j_t，末因子为 t。保存历史证书
$$
F\equiv_{\Delta_0}W,\qquad
\Delta_0=P_t(\Theta),\qquad
\Theta=\text{该入口中旧 }\theta_{t+1}. \tag{12}
$$
后续已验证操作保留旧 factor owners、旧 p 链和旧列本身。设底层实际 native
源为 U=(u_1<⋯<u_q)，q>0。普通 native 给
$$
j_t(\theta_{u_h})=\theta_{T_t+h}<\Theta.
$$
现在明确假设一个独立的实际包传播引理已经建立所有层的平行 owners、
p 链，以及
$$
W(\theta_{u_h})=\theta_{Y+h}\quad(1\le h\le q),
$$
且 targets 在原 mark 的历史间隙内。则
$$
\boxed{\theta_{Y+h}
=P_t(j_t(\theta_{u_h}))<P_t(\Theta)=\Delta_0.} \tag{13}
$$
故 (12) 可读取全部实际新行边 F(θ_(u_h))=θ_(Y+h)。不需要另证明 Γ>包顶
这类历史不等式；它由自然界的定义直接给出。

新平行 mark 的末因子为 T_t+h，前面因子 owners 仍组成 P_t，因此其自然界是
$$
\Delta_h=P_t(\theta_{T_t+h+1})\le P_t(\Theta)=\Delta_0. \tag{14}
$$
h<q 时下一列是下一个 native 包点；h=q 时恰为旧下一列 Θ。因而边界 h=q
也被覆盖。新词与 W 全局相同，式 (12)、(14) 证明所有新 marks 满足 (N)。

普通行的 source/target 成对间隙、临界点及几何 (G) 可由 (13)、历史目标间隙
与已有普通 interval lemma 推出。因此自然界不给实际 compTo 增加一个
独立读值接口：一旦整包和历史间隙从原算法得到，全部语义随之成立。

**非循环性。** 整包不可由本节的结论反推后当作前提。所保存的是扫描入口
的 Δ_0，不是底层 native 后已经下降到第一个包点像的当前 Δ。前段正确
compTo 可以用于事件归纳；当前待验证 compTo 不包含在前段正确性中。

## 6. 与完整普通 BLP 证明的接口

本稿证明了自然 mark 语义的合法复制闭包、旧 marks 的 cut/native 继承，
以及实际整包一旦成立后的全部 compTo 语义。与固定 θ_(y+1) 语义相比，
它不再要求为每个复制接缝恢复全局内部 +1，且无须为 read 单独追踪任意界。

剩余的算法论证是从原始当前 guard 与标准扫描入口结构推出整包、历史间隙
和普通行合法性；这须另行证明。现有仅使用入口 A_rec 的包定理当然仍可
使用，但本稿自身不把 A_rec 作为必需条件，也不宣称它已经被删除。

主代理正在单独研究以 eligible 内部上因子的入口 Sat 条件
B(e(v))≤p(v) 取代入口邻接的包二分。本稿第 5 节可直接与任何正确的该类
独立包定理合并。完整语法操作的合法性、标准初始实现、定理 2.25 及从展开
终止到所指定顺序的良序桥接，仍应在最终合成稿逐一核验，不能仅由本稿标题
或局部复制闭包宣告完成。

**本轮完成后的补记。** 上段保留本局部稿形成时的依赖说明。所需的独立
Sat_rec 整包定理现已在 `sat_endpoint_packet_theorem.md` 中证明并终审；
全部普通操作合法性与 I2 良序合成见
`full_marked_blp_natural_cutoff_wellorder.md`，也已完成独立终审。
den2_wellorder_route 对本稿的独立终审核对了 min 公式、high 三界、
low 等号边界、全部 native 继承标记和 h=q 历史界，未发现缺口。
定理 2.25 的精确数值结论和 DEN2 不属于这次合成的结论。
