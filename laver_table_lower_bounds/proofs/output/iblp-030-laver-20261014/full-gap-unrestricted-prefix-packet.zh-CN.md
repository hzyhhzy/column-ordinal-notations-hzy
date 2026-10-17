# 全间隙扫描的前缀包定理：语义闭包不再需要 Sat

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本文加强
[GapSat 父项的局部闭包](<full-gap-native-local-closure.zh-CN.md>)：
对豁免 $L=1$ 的全间隙 native，完整扫描的**语义合法性**其实不需要
GapSat、旧 Sat 或 Sat_rec。

原因不是“补得更多所以更强”，而是一个确定的前缀关系：上层全间隙包可以比
下层包长，但它的前面一段必恰好是下层整个新 family；传送底层记录只需这段。
下面不讨论序型增强。GapSat 仍用于旧前缀静止和基本列的前缀性质。

## 1. 输入和结论

输入是任意一个有限的真实普通 marked BLS：

- 每个 core 加回隐含端点后满足普通行型；所有行边与最小项临界点真实；
- 所有 marks proper，其实际 p 链准确命中步长配对源；
- 每枚 mark 满足其当前实际词的自然 membership 截断。

不要求输入来自标准根，也不要求任何饱和条件。
使用一次从左到右扫描：每条当时的旧行先按当前 $+1$ guard 处理冻结的旧 marks，
然后作 native；native 新 family 跳过，不在本轮重扫。
仅普通中、短行且步长 $L\ge2$ 执行 native，源包为当前全部整数间隙 $(p,e)$。

**定理。** 此扫描的每个实际补全都合法，全部新旧行边、proper 准确 traces
及自然截断保持；扫描有限完成，输出 GapSat。全局最后命名点与末 owner 都不变。

这是扫描本身的定理；若此前执行复制，仍须另外保证原部分复制映射有定义，
并调用合法 copy 的自然截断语义。定理不宣称所有复制都可做。

## 2. 旧因子基行和不受污染的源间隙

把扫描入口的旧行记为 $v,w,\ldots$。其当前基行位置记 $T_v,T_w,\ldots$，
它本轮 native 的插入数为 $q_v,q_w,\ldots$。此前插入只对以后旧行作重编号，
不会重新扫描新 family。

沿旧行与冻结旧 marks 的处理顺序作事件归纳。在一个待验证事件之前，可使用
此前已经验证的事实：

1. native 保留其旧基行的 p 与 owner，阶梯新行也使用同一个 owner；
2. 正确 compTo 保留旧 p/e、旧行边及 owner；
3. compTo 新 sources 严格低于该 owner 的 p，新 targets 在其 e 或以上，
   不向开区间 $(p,e)$ 添加 core 条目；
4. 旧 mark 的实际因子基行与旧词随重编号保留。

第 3 项不是对任意 raw 字段的断言。普通长行最早的 critical-image mark
可能违背其字面位置范围；必须用 §5 的临界点论证证明这枚 mark 不会执行非空补全。
只有已经验证的此前 compTo 才能用这四项，当前事件不包含在归纳前提里。

## 3. 内部 active 因子的包包含整个下层 family 作为前缀

设某条入口旧词有内部边 $v\to w$，即入口 $p(v)=w$。
当然 $e(v)>w$，但不要求 $e(v)=w+1$ 或旧 $\delta(e(v))\le w$。
设下层已经产生非空 native family，宽度 $q_w>0$。

由于按旧行次序扫描，旧第 $w$ 行和其紧后旧行之间的全部新增全局点正是
第 $w$ 行自己的 native family。因此这些点的当前地址为

$$
T_w+1,\ldots,T_w+q_w.
\tag{1}
$$

原来的下一旧行在 $T_w+q_w+1$；更晚旧行的 native 插点全部在此位置以后，
不会重新往 (1) 中间插点。compTo 不新增全局点。

扫描到 $v$ 时，其 p 仍为 $T_w$，其 e 对应某个严格晚于 $w$ 的旧点，
故至少为 $T_w+q_w+1$。若 $v$ active，它取整个当前源间隙，所以

$$
q_v\ge q_w,\qquad
u_h^{(v)}=T_w+h\quad(1\le h\le q_w).
\tag{2}
$$

这里包按升序排列。普通 native 阶梯的统一 p 公式遂给

$$
p(T_v+h)=T_w+h\quad(1\le h\le q_w),
\qquad J_{T_v+h}=J_v.
\tag{3}
$$

上层间隙在这些点以后还可包含任意多旧点及其他先前 family；它们只增加 $q_v$，
不改变首 $q_w$ 项。因此既不需要旧 Sat，也不需要复制因子局限在同一连续区。

## 4. 当前 guard 强迫实际经过的内部因子 active

固定当前 mark。其旧非终点因子按从底向上排列为
$b_0<\cdots<b_d=y$，底层记录宽 $q=q_{b_0}>0$。
当前 $+1$ guard 要求各内部边的上层 core 含下层基行后的第一个点
$T_{b_{i-1}}+1$。

此点不是扫描入口旧点，而是下层 native 的第一个新点。
若上层为长行，它不作 native；在其 mark 处理阶段，已验证 compTo 的
sources 在 p 以下、targets 在 e 或以上，不能把它添进 $(p,e)$。
所以长行不通过该 guard。

若上层为豁免 native 的一步长两点 core $(p,v)$，它没有 proper marks，
也只含基点 $T_w$ 与不早于 $T_w+q_w+1$ 的行地址，不能含
$T_w+1$。一步长长行已属于前一种情形。

因而一个实际通过 guard 的非空 mark，全部内部因子必须 active。
沿 (2) 归纳得到

$$
q_{b_0}\le q_{b_1}\le\cdots\le q_{b_d}.
\tag{4}
$$

只取各层的前 $q=q_{b_0}$ 条新行，由 (3) 有

$$
p(T_{b_i}+h)=T_{b_{i-1}}+h
\qquad(1\le h\le q,\ 1\le i\le d).
\tag{5}
$$

最底层则满足 $p(T_{b_0}+h)=u_h$，其中 $u_h$ 是原记录的第 $h$ 个源点。
所以当前 compTo 实际输送的 $q$ 项具有准确的平行 p 链及 factor owners。
**不需要**任何上层的全部包宽等于 $q$；式 (4) 已足够。

## 5. 历史自然界、临界点和完整配对几何

设当前 mark 的 owner 为 $F$，其入口旧词为

$$
W=P\circ K,\qquad K=J_{b_0}.
$$

底层入口紧后点记 $\Theta$。扫描入口保存历史自然证书

$$
F\equiv_{\Delta_0}W,\qquad \Delta_0=P(\Theta).
\tag{6}
$$

此前操作保留实际旧词、旧 owner 和旧命名点。底层 native 插入的所有像均低于
它的旧紧后点，故

$$
K(\xi_{u_h})<\Theta.
$$

由 §4 的前缀传送，顶层前 $q$ 个目标实际为

$$
\xi_{T_y+h}=W(\xi_{u_h})
           =P(K(\xi_{u_h}))<P(\Theta)=\Delta_0.
\tag{7}
$$

所以历史 membership 截断读取每一条新增 $F$-边，不需要将上层超出 $q$ 的
其余 targets 也放入当前 compTo。

底层非空 native 来自普通 $L\ge2$ active 行。普通行型排除步长 2 短行，
因此底层 $p$ 严格大于其最小项，给
$\operatorname{crit}(K)<\xi_\delta$，其中 $\delta$ 是该 mark 的源。
复合不提高最早被移动点，故

$$
\operatorname{crit}(W)\le\operatorname{crit}(K)<\xi_\delta.
$$

又 $W(\xi_\delta)=\xi_y<\Delta_0$，历史弱等价给 $F$ 同一个低临界点。
所以 $\delta$ 不能是 $F$ 的最小项。这正是排除长行最早 critical-image mark
执行非空补全所需的论证。

式 (7) 还使 targets 严格位于该 mark 的历史紧后间隙内。由真实旧边、严格单调性
及普通成对区间引理，源包位于其对应的 source 间隙，所有旧边与新边均成立，
且旧 p/e、owner 保留。因此 §2 的位置性质此刻对当前 compTo 也得到验证。

新增第 $h$ 枚平行 mark 的实际词仍由相同 owners 组成，准确性由 (5) 给出，
其自然界是

$$
\Delta_h=P(\xi_{T_{b_0}+h+1})\le P(\Theta)=\Delta_0.
\tag{8}
$$

等号发生于底层 $h=q$；上层是否还有更多新行与此无关。
故全部新自然证书保持。旧证书的当前紧后点只可能下降，也仍成立。

## 6. 完成事件归纳与用途边界

当前 compTo 至此全部验证，再执行 native。后者对任意升序整数间隙的点像
和阶梯行边已经直接验证，不依赖祖先链。它给普通行型、同 owner、
准确 direct marks 及 GapSat family。
所有新 targets 严格早于其 mark owner，所以 proper 条件同时保持。

旧行与每条旧行的冻结 marks 都有限；每个间隙包含有限多个当前地址；
新 family 跳过。因此上述事件归纳给有限完成和全部局部合法性。
每个处理完的前缀都 GapSat，后续操作不改此前行，故最终输出 GapSat。
补全不改变旧末 owner 及全局末点，完成定理证明。

该结论可在任意有限串**合法**复制之后使用：先用原自然 copy 语义逐次取得真实输入，
再调用本篇扫描定理，不再额外证明 Sat_rec。
但全尾复制可能提高 cap，故这句话不自动给一个固定小端点的良基下降或步数界。
也不能据此把任意多个全尾复制算成一次 application 下降。

若需要展开保留父 cut 前缀，仍应让父项 GapSat：这样扫描入口旧前缀才静止。
语义闭包、前缀结构、序位严格下降和定量强度比较是四个不同接口，本定理只免掉了
第一个接口里的 Sat／Sat_rec 前提。

**独立审计。** t3_audit 独立核对了前缀包而非等宽包的下标、长行和 $L=1$
的排除、历史自然界及包末 $h=q_{\rm bottom}$ 的边界；确认上述逐事件次序没有
预用当前 compTo 的合法性。该审计不把本定理扩展为强度比较或全指标固定 cap 良基性。
