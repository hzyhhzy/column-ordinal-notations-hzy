# 内部上因子的入口饱和足以保证完整标记包传送

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-09-07。本文替换 `current_guard_full_packet_theorem.md` 的 A_rec 前提。
新的条件只使用源间隙右端点所在行的 B 值，允许 e(v)>p(v)+1。
主代理提出后，full_marked_proof 与 den2_wellorder_route 分别核查了下面的
关键归纳。本文针对普通 BLP 与正确 PDF 当前 +1 guard；不推广到无 guard
的 DEN2。

## 1. 扫描入口和 Sat_rec

固定合法普通 BLP 扫描入口 P。每条 mark 的实际 trace 精确命中其步长源。
普通扫描先 compTo 后 native，native 新块跳过。令

$$
p_v=A_v[-L_v-1],\quad e_v=A_v[-L_v],\quad B(v)=A_v[-2].
$$

旧行 v 的当前基行记 T_v=ρ(v)，其实际 native 宽度为 q_v。
旧下一行 D_v=ρ(v+1)=T_v+q_v+1。普通 native 块内有

$$
B(T_v+h)=T_v+h-1,\qquad 1\le h\le q_v.
\tag{1}
$$

此前已经验证的 compTo 保持旧步长边、p、e、min，sources/targets 各在
相应旧间隙，targets 全在 mark 的历史相邻列之间。native 保持块首 B。
这些只是假设当前事件以前的结论，当前 compTo 不包括在内。

对会读取非空 Rec 的每条入口旧词，要求每条内部边 v→w 满足：

$$
\boxed{\text{若 v eligible，则 }p_v=w,\quad B_P(e_v)\le w.}
\tag{Sat_rec}
$$

eligible 指普通中/短行；长行不作 native。没有要求 e_v=w+1，也没有
要求末因子本身 Sat，更没有要求整个复制后入口 Sat。

## 2. 先证明宽度单调，不使用完整连接

**引理 2.1。** 对已处理的内部上因子 v→w，若满足 Sat_rec，则

$$
q_v\le q_w.
\tag{2}
$$

当 q_v>0，其实际 native 源必为 w 新块的一个初段
`T_w+1,...,T_w+q_v`。

**证明。** 长行的 q_v=0。对 eligible v 记 s=e_v。
若 s=v，则下一源为 core 最大项，故 L_v=1；普通 eligible 行只能是
两点 core，native 首次查询 B(v)=p_v，包为空。合法前置 compTo 不能
改变这一退化行的结论。

以下 s<v，故旧行 s 先于 v 处理。入口 B_P(s)≤w 说明 s 的全部旧
proper marks 至多为 w。mark y<w 的此前正确补全，其新 targets 严格
低于历史 y+1 列，因而低于或先于 T_w；sources 更低。只有旧 mark w
可能使 s 的基行 B 超过 T_w。若该 mark 实际插入 k 个 targets，前段
几何给

$$
T_w+k<D_w=T_w+q_w+1,\quad\text{所以 }k\le q_w.
\tag{3}
$$

有此 mark 时入口 B_P(s)=w，它执行后 B(ρ(s))=T_w+k。没有此操作时
B(ρ(s))≤T_w。s 自己的 native 保持基行 B；以后更高行的操作也不再
修改它。

当前 v 的 native 仍在历史端点 (T_w,ρ(s)) 之间取 B 链。若 B(ρ(s))≤T_w，
第一次 B 查询已经到达终止阈值，包为空；若 B(ρ(s))=T_w+k，则由 (1)
得包恰为 `T_w+1,...,T_w+k`，于是 q_v=k≤q_w。证毕。

这里允许 s 离 w 很远。限制 B_P(s)≤w，而非 s=w+1，已足以排除
独立旧 sources 混入该包。

## 3. 实际连接只能为空或完整

**引理 3.1。** 在引理 2.1 的情形，处理 s 后只有

$$
B(\rho(s))\le T_w\quad\text{或}\quad
B(\rho(s))=T_w+q_w.
\tag{4}
$$

**证明。** 只需处理 s 的旧 mark w 确实补全 k>0 的情况。其底层
旧因子记 t，故 k=q_t。该 mark 读取非空记录，Sat_rec 适用于其每条
内部边。全部因子均严格低于 owner s，已经处理；沿它的词逐次用
引理 2.1 得 q_w≤q_t=k。前段几何已经给 k≤q_w，所以相等。
这只使用当前 v 以前的 native 和已验证 compTo，没有循环验证当前事件。
证毕。

更明确地，在验证某个外 owner R 的当前 compTo 时，引理 2.1 用到的每个
端点 owner s<v<R 都严格更早；引理 3.1 中 carrier 词的所有因子又都<s。
引理 2.1 本身没有使用引理 3.1，只使用更早 compTo 的几何。因此先使用
宽度单调，再证明二分，不会回借当前外 compTo 的正确性。

## 4. 当前 +1 guard 强迫完整平行包

固定当前外 mark，其旧非终点因子由下至上记 b₀<...<b_d=y。
假定底层实际 native 包 U=(u₁,...,u_q) 非空，q=q_(b₀)，当前 PDF
检查每条内部边时都发现

$$
T_{b_{i-1}}+1\in A_{T_{b_i}}\qquad(1\le i\le d).
\tag{5}
$$

**定理 4.1。** 在 Sat_rec 及已验证前段下，每层 native 宽度都等于 q，
上层 i 的实际源恰为下层的整包 `T_(b_(i−1))+1,...,+q`。
因此所有 h=1,...,q 满足

$$
p(T_{b_0}+h)=u_h,\qquad
p(T_{b_i}+h)=T_{b_{i-1}}+h,
\tag{6}
$$
$$
j_{T_{b_i}+h}=j_{b_i},\qquad
\theta_{T_y+h}=(j_{b_d}\circ\cdots\circ j_{b_0})(\theta_{u_h}).
\tag{7}
$$

**证明。** 从底层向上归纳，假定下层 q>0。新整数 T_w+1 原来不在
扫描入口任何行中，位于上层的历史源间隙 (T_w,ρ(e_v)) 内。此前正确
compTo 的 sources 严格低于 p_v，targets 在 e_v 及以上，不会向这个
源间隙添点。这里的 target 位置使用此前事件已经验证的普通 interval
lemma，不仅是 proper mark 的裸语法：非空底层 native 给
crit(W)<θ_δ，历史弱证书给 crit(owner)<θ_δ，故 source 不可能是
最小条目。特别在长行中，这排除了位于 e_v 以下的最早 proper mark
实际作非空补全。因此 (5) 只能由上层自己的非空 native 实现。
引理 3.1 随即迫使其选中下层整个包，而非真初段。退化 e_v=v 的行和
长行均不能通过这一检查。普通 native 逐行公式给 (6)、(7)。证毕。

这一步只验证包对应关系；当前外 owner 的真实新增行边，还要用下一节
的标记证书验证，不能把组合对应当作语义。

## 5. 末因子后继输送界恰好覆盖所有实际 targets

令扫描入口 mark 的词为 W=P∘j_t，其中 t=b₀，P 为除末因子外的前缀。
保存入口基数定义的历史界

$$
\Delta_0=P(\theta^{\rm entry}_{t+1}),\qquad F\equiv_{\Delta_0}W.
\tag{8}
$$

普通 native 把底层新点严格插在其旧目标间隙中，所以

$$
j_t(\theta_{u_h})<\theta^{\rm entry}_{t+1}.
$$

定理 4.1 遂给

$$
\boxed{\theta_{T_y+h}=W(\theta_{u_h})<\Delta_0.}
\tag{9}
$$

因此 membership 弱等价确实读出 F 的全部新行边，不能仅凭
Δ₀>θ_(T_y) 省略 (9)。此外 Δ₀≤入口 θ_(y+1)，故 targets 位于旧
mark 的历史间隙；未处理 owner 的该间隙此前不被其他 mark 占用。
`marked_completion_interval_lemma.md` §4 给普通配对几何及旧边保持。

新 mark 的平行因子 owners 全局相同；其自然新界为

$$
\Delta_h=P(\theta_{T_t+h+1})\le
P(\theta^{\rm entry}_{t+1})=\Delta_0.
\tag{10}
$$

h=q 时右边为等号，较小 h 为不等式。故全部新 marks 满足自然界语义；
旧基行因子词不变，其当前紧后列只降低，所以其自然界也不增加。
这完成逐事件语义归纳。具体自然界的复制闭包见
`natural_trace_cutoff_semantics.md`。

这里的新词识别也确由算法得到：成对几何使新 mark T_y+h 的步长源为 u_h，
式 (6) 使实际 p 链逐级经过各 T_(b_i)+h，并准确停在 u_h。不同层的 native
块互不相交，故不会提前命中终点。无需另外假定新词内部 +1；当入口
e_v>w+1 时，包末项 h=q 的那条邻接未必成立，本节也没有使用它。

式 (8) 必须作为历史证书保留。底层 native 后，当前自然界可以已经降为
P(θ_(T_t+1))；不能将这个较低的当前界替入 (8) 再试图读取整个包。

## 6. 单次 Sat 父项短复制自动提供 Sat_rec

**定理 6.1。** 父模式为真实普通 BLS、Sat，所有 marks 的 trace 精确；
用自然界语义，不要求内部邻接。执行一次合法短复制，并从左到右完整
扫描，则所有实际读取非空 Rec 的旧 marks 都满足入口 Sat_rec。

**证明。** Sat 与空 Rec 使原前 n−1 行静止。已证实际 copy 词识别和
`scan_dependency_localization.md` 定理 3.1 因而仍适用：任何读取非空
记录的 mark 必须全部非终点因子被复制。跨界 low/high 的末因子在静止
前缀，本轮不建立记录。

对这样的旧词内部边 v→w，复制根为 a，有 w≥a，且
w<e_v≤v。owner 是 proper 的，故 v 与 e_v 所在行均在同一连续复制
源区间内。若 v eligible，父 Sat 给 B(e_v)≤w；统一严格映射 φ 给

$$
B_{\rm entry}(\varphi(e_v))=
\varphi(B_{\rm parent}(e_v))\le\varphi(w).
\tag{11}
$$

复制保持行内位置与行型，所以这是所需入口 Sat。没有对底层非终点
因子施加该条件，它可以产生本轮第一个 native 包。证毕。

式 (11) 即使 B_parent(e_v)<a 仍成立：它是源行 e_v 的 core 条目，合法
copy 因而在该点定义 φ，且 φ 在整个所用域严格递增。此论证适用于每个
实际借非空 Rec 的旧 mark，特别包括第 3 节可能读到的 carrier mark；
carrier 若跨复制边界，其末因子在静止前缀，根本不会触发非空调用。

结合自然界的 copy 保持定理、第 4—5 节，以及普通 native 保持，可得
一次 M_star 的完整自然界 marked BLS 闭包，无须先证明输出旧 A。
标准 Sat 的纯组合归纳随后可直接应用，因为每次实际操作的合法性已经
在上述逐事件归纳中验证。

## 7. 范围与审核提醒

核心 Sat 替换已由两个代理分别核查，完整成稿已终审；整体 E/M 合成见
`full_marked_blp_natural_cutoff_wellorder.md` 的独立终审记录。
无入口 Sat_rec 的一般扫描不适用：其 endpoint 行可以原来就有
B(e_v)>p_v，产生额外旧源，进而使后继 mark 只连接一个真初段。
这解释了 `marked_cutoff_demand_analysis.md` 的局部反例为何没有推翻本文。

**独立终审记录（full_marked_proof，2026-09-07）。** 全文局部定理审核通过。
已逐项核对第 2—3 节只使用更早事件、第 4 节 +1 新点不能来自 compTo、
第 5 节保存入口历史 Δ、以及第 6 节对所有非空 carrier 的 Sat 搬运。
修正第 2 节“前一种/后一种”文字指代颠倒，并补明低于复制根的 B 像、
新词识别及无需新词内部 A 的边界。没有增加新的算法过滤或未证语义前提。
本记录负责局部整包定理；整体 E/M、终止与良序合成的审核另记于全局稿。
