# 直接 mark 的下一源对齐：一个完成态历史不变量

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-09-07。本文给出不依赖固定因子下界的标记出生约束。它已由另一代理
独立核查。应用范围是普通 P_start 主 E/M_star 的已验证结构历史：复制
严格合法且采用正确 PDF 筛选，native 使用普通公式，compTo 有正确成对
间隙、旧边保持及实际平行词。真实 BLS、Sat、内部 A 的父项作一次合法
短复制后，`current_guard_full_packet_theorem.md` 推论 6.1 已提供后者。

这不是把任意 raw 扫描宣布为正确，也不假定扫描输出所有旧 marks 的 A
已经闭合。以下等式断言在复制后的扫描入口及完整扫描结束时成立；不能
误用于“底层刚 native、后方 owner 还没处理”的临时快照。

## 1. 定义与结论

对行 t 记

$$
p(t)=A_t[-L_t-1],\qquad e(t)=A_t[-L_t].
$$

proper mark y 位于 owner 行 R 的一基位置 k，令

$$
\delta=A_R[k-L_R],\qquad d=A_R[k+1-L_R].
$$

d 是它的源 δ 后紧随的 core 条目。称 mark 为 direct，若实际 trace 恰为
(y,δ)，故 p(y)=δ。定义

$$
\boxed{\mathsf D:\quad d=e(y)\quad\text{对每枚 direct mark 成立}.}
                                                               \tag{D}
$$

**定理 1.1。** P_start 满足 D；合法 PDF 复制、辅助 E、cut 保持 D；在
上述正确补全接口下，完整扫描把满足 D 的入口送到仍满足 D 的输出。

这是额外的历史信息。一般弱 marked BLS 只给 d≥e(y)，并不自动给等号：
因子在 θ_(e(y)) 达到弱界，而 owner 在 θ_d 达到或超过该界。不能从弱截断
把这些较高像误读成全局相等。

## 2. 初始、复制及删尾

初始唯一 mark3 的源为 1、下一源为 2，因子行 3 的 e(3)=2。

实际 copy 词识别表明：全复制、low 保留 direct 词长度；high 实际结果
至少包含活动词及 source 尾词的两个非终点。因此 high 不产生 direct，
非 direct 旧词也不会因复制变成 direct。

全复制 direct 的因子行及 owner 的对应条目使用同一 φ，故
d'=φ(d)=φ(e(y))=e'(φ(y))。low direct 的因子 y<C，而 e(y)≤y<C，源后
条目与因子行都固定，等式同样保持。这里不需要 φ 保持整数间距。
辅助 E 是同一复制的全／低分支特例；cut 不改变保留行。

## 3. 扫描中的精确局部论证

先固定一枚入口 direct mark y。用 T=ρ(y) 表示其已处理后的基因子行。
在处理 owner 前，保存的是历史等式

$$
d_{\rm owner}=\rho(e_{\rm entry}(y)).                 \tag{1}
$$

此前其他行只重编号这个条目。当前 owner 上其他 marks 的源间隙与它不同，
不能向其 (δ,d) 插点；正确 (G) 还把所有 targets 放在 owner 的 e 之后，
不会混进任何 proper mark 的源间隙。所以按多 mark 顺序处理时仍可使用 (1)。

若因子 y 的 native 为空，其 e 只是旧 e 的重编号，本枚 mark 不读取非空
Rec，D 原样成立。若它有非空包 U=(u₁<…<u_q)，则基行的新 e(T)=u₁。
direct 词的内部 +1 检查为空，owner 确实处理这份非空 Rec。正确 compTo
往旧源 δ 后的同一个真间隙插入 U，于是继承的 mark T 有 d_new=u₁，
恢复 D。

同次 compTo 的新 mark T+h（1≤h≤q）仍是 direct。h<q 时，它的 source
u_h 后紧接 u_(h+1)，而真实 native 因子行也有 e(T+h)=u_(h+1)。h=q 时，
owner 在 u_q 后的下一 source 是历史旧 d；native 块末的 e(T+q) 恰为
历史旧 e(y)，由 (1) 两者相等。这特别核对了最末新 mark 的边界。

若当前 native 自己新建 mark T+k，任何承载它的块行 T+h 都满足
0≤k<h≤q。因而 k<q，因子行的下一源是 u_(k+1)（令 u₀=原 p），承载行
中对应 source 后的下一项也是 u_(k+1)。所以 native 真正新建的 direct
marks 同样满足 D。

最后，owner 自己的 native 不破坏任何已经验证的 proper mark。因为
k≤m−1 给

$$
k+1-L\le m-L,
$$

所以该 mark 的下一 source d≤owner 的 p；native 只在 (p,e) 添 sources，
短行只删 e，并在末端添 targets。这些都不会改变 d。每个继承副本仍用
同一 direct 因子及下一源。后方扫描也不会再改这些已处理行。

逐 owner／逐 mark 归纳给出定理。这里允许任意多 marks、任意合法非空
包宽；没有另加 direct carrier 存在或 Flow 条件。

## 4. 对 H 标记的立即后果

H 行满足 min=0、p=1。在 NC 与 trace 精确性下，任何以 H 行 y 为首因子
的 mark 都只能是 direct (y,1)：其第一次 p 已到 1，而阈值必须≥1。
于是标准完成态每枚这种 mark 的 source/下一 source 精确为

$$
(1,e(y)).                                             \tag{2}
$$

它可以位于任意高 owner，不能只核对紧随 y 的一行。式 (2) 是 H 接缝
分析可以使用的整族约束，后续应用及尚未排除的复制压缩见
`h_anchor_history_barriers.md`。
