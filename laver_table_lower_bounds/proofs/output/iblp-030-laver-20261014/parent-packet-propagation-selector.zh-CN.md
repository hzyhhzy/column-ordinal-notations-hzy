# 父包传播：保留祖先带的温和 native 选择器

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本文定义并验证一个局部改造：保留原祖先链包，只把本轮直接父行
已经产生的 native family 补进来。它不填整个整数间隙，也不把未知次数的 M
归约藏入一步。以下证明其有限扫描语义、输出饱和和原平衡 BMS 带保持；
不宣称该改造已经比 BMS 或原 IBLP 更强。

## 1. 数据、扫描次序及定义

采用普通 marked BLP 行型。第 $r$ 行的 core 为 $A_r$，末项 $r$，步长
$L_r\ge1$，隐含最后命名点为 $r+1$。定义

$$
\delta(r)=A_r[-2],\qquad
p(r)=A_r[-L_r-1],\qquad e(r)=A_r[-L_r].
$$

称行 active，若 $L_r\ge2$ 且 $|A_r|\le2L_r$。
长行和 $L=1$ 行不作 native。
执行左到右单次扫描：每条当时的旧行先处理其冻结旧 marks，再执行 native；
native 新生 family 跳过，不在当前扫描重新遍历。

字典 record 初始为空。每次某个旧基行 $t$ 实际插入了 $q_t>0$ 个新点，
就在键 $t$ 下记录其**最终所选源包**，长度为 $q_t$。键随必要的递增重编号
同步解释为该旧行的当前基行；新 family 内部行不另登记记录。

处理 active 行 $r$ 时，从其当前 core 读取 $p=p(r),e=e(r)$：

1. 按原规则沿 $\delta$ 链，从 $e$ 的第一跳起，收集仍严格大于 $p$ 的点，
   将所得包升序写为 $U$。
2. 若 record 中没有键 $p$，令 $V=\varnothing$；否则令
   $q=|\operatorname{record}[p]|$，取
$$
   V=\{p+1,\ldots,p+q\}.
$$
3. native 的实际源包取
$$
   \boxed{S=U\cup V.}
   \tag{1}
$$
   按升序去重，沿用普通 native 的中/短阶梯公式和同 owner 语义。

这里 record[p] 的原源地址不被直接加入；加入的是这次记录所对应的
**当前目标 family 地址** $p+1,\ldots,p+q$。两者不可混淆。
定理会证明所有 $V$ 点严格小于当前 $e$；实现应检验这一不变量，
不能在失败时悄悄把越界点截去。

## 2. 为什么 record[p] 恰好指向正确的父 family

固定扫描入口的旧行编号。设旧行 $v$ 的入口 p 为旧行 $w$，当前基行位置为
$T_v,T_w$。沿已验证的此前事件：

- native 保留旧基行 p 与 owner；
- 正确 compTo 保留当前 owner 的旧 p/e 和 owner；
- 后续插点只重编号，旧实际点及行身份不变。

因此在处理 $v$ 的 native 时，

$$
p(T_v)=T_w.
\tag{2}
$$

它不会意外变成父 family 的某条内部新行。若 $w$ 本轮 native 了 $q_w$ 个点，
record 的键就是 $T_w$，其 family 为

$$
T_w+1,\ldots,T_w+q_w.
\tag{3}
$$

旧 $w$ 的下一旧点在 $T_w+q_w+1$。入口 $e(v)>w$，而本行此前 compTo
保留旧 e，所以当前

$$
T_w+q_w<\rho(e(v))=e(T_v).
\tag{4}
$$

这证明定义 (1) 的父包始终落在当前 $(p,e)$ 内。
若该 p 行没有 native，record[p] 不存在，规则自然退回原祖先包。
论证不要求 $v\to w$ 真被某个 mark 使用；普通 p 边本身已经足够。

## 3. 联合包保证输出 ActiveSat

定义

$$
\operatorname{ActiveSat}(P):
\quad \delta(e(r))\le p(r)\quad\text{对所有 active 行 }r.
\tag{5}
$$

对普通 $L=1$ 行，若 core 仅有 $(a,r)$，则
$p=a,e=r,\delta(e)=a$，旧 Sat 是恒等式；其余普通 $L=1$ 行是 long，
不受旧 Sat 检查。因此在普通行型域，ActiveSat 与原来对全部 eligible 行的
Sat 等价。这一等价只在说明了行型以后使用。

设 $S=\{s_1<\cdots<s_m\}$，并置 $s_0=p,s_{m+1}=e$。
称 $S$ 覆盖源间隙的 $\delta$-前驱，若

$$
\delta(s_{i+1})\le s_i\qquad(0\le i\le m).
\tag{6}
$$

空包情形就是 $\delta(e)\le p$。
原祖先包 $U$ 满足 (6)：中间各点是连续祖先迭代，最后一步越过阈值；
没有包时第一跳已不超过阈值。

父 family 的每个新点满足

$$
\delta(T_w+h)=T_w+h-1\qquad(1\le h\le q_w).
\tag{7}
$$

此式来自普通阶梯 core 中连续新目标的位置，与其源包是否祖先链无关。

**并包引理。** $S=U\cup V$ 仍满足 (6)。

证明：若待检查点来自 $U$ 或是终点 $e$，它原来被前一个 $U$ 点或 $p$
控制；取并集只会增大它的紧前源阈值。若它来自 $V$，(7) 的前驱要么是 $p$，
要么是 $V$ 中的紧前点，已在并集中。因此各点都满足 (6)。

对任何这样的升序源包，普通 native 阶梯在第 $r+i$ 行满足

$$
p'(r+i)=s_i,\qquad e'(r+i)=s_{i+1}\qquad(0\le i\le m).
\tag{8}
$$

active 普通行有 $e<r$，所以插在 $r$ 后面的新 targets 不修改 (6) 查询的
源地址和 $\delta$ 值。于是 (6)—(8) 证明每条新行满足 ActiveSat。
处理完的前缀以后不再被更高行修改，故一次合法扫描的最终输出满足 ActiveSat，
不要求输入原来饱和。

## 4. 每个相关上层包包含下层整个 family 作为初段

考虑当前 mark 的旧因子链中的内部边 $v\to w$，即旧 $p(v)=w$。
若下层有包 $q_w>0$，§2 保证 record[p(v)] 正是这份记录。
若上层 active，选择器 (1) 必把下层全部 family (3) 放进当前源包。

它们是 p 之后最早的连续整数点，没有其他点能夹在它们前面。因此

$$
q_v\ge q_w,\qquad
u_h^{(v)}=T_w+h\quad(1\le h\le q_w).
\tag{9}
$$

原祖先包可以在这段之后再添点，但不能破坏这个初段。
由 (8)，对应新行具有

$$
p(T_v+h)=T_w+h,\qquad J_{T_v+h}=J_v
\quad(1\le h\le q_w).
\tag{10}
$$

这是完整标记输送所需的前缀包条件，不要求各层总宽度相同。

## 5. 任意真实普通输入的有限语义闭包

**定理。** 设输入有真实普通行实现、proper 准确 mark traces 和自然 membership
截断语义。按 §1 作父包传播扫描，则所有局部操作合法，有限完成，输出仍满足
这些条件及 ActiveSat。全局 cap 与末 owner 不变。
不要求输入 Sat、Sat_rec，或来自标准根。

证明按旧 owner 行号和冻结 marks 的顺序作事件归纳。
当前事件只使用已经验证的此前 compTo 的保边、p/e 和区间几何。

active 普通行的 p 严格大于其最小项：中行的 p 是第 $L\ge2$ 项；
短行的 p 是第 $L-1\ge2$ 项，因为普通行型排除步长 2 短行。
故每次非空 native 的底层 owner $K$ 满足
$\operatorname{crit}(K)<\xi_p$。
沿旧词 $W=P\circ K$，其临界点也低于 mark 配对源。
历史自然截断继承该低临界点，排除普通 long 行最早 critical-image mark
执行非空补全；已验证 compTo 的新 sources 在 p 以下、targets 在 e 或以上。

因此当下层包非空时，long 因子不能通过当前 $+1$ guard：
它没有 native，也不能从此前 compTo 向 $(p,e)$ 添加父后的第一个新点。
豁免的 $L=1$ 两点 core 没有 proper marks，且只含父基点和晚于整包的行地址，
同样不能通过该 guard。

所以实际执行的非空 mark，其内部因子都 active。
由 (9)—(10) 沿各层取底层宽 $q$ 的共同初段，就得到完整准确的平行 p 链、
相同 factor owners 及全部实际 word 像。设底层旧紧后点是 $\Theta$，
入口保存的历史证书为

$$
F\equiv_{\Delta_0}P\circ K,\qquad \Delta_0=P(\Theta).
$$

底层各新像 $K(\xi_{u_h})<\Theta$，因此顶层对应目标满足

$$
(P\circ K)(\xi_{u_h})<P(\Theta)=\Delta_0.
\tag{11}
$$

历史 membership 截断读取全部新增 F 边。普通成对区间引理再给所有旧边保持、
正确 source/target 间隙及当前 p/e 保持。至此当前 compTo 才完成验证，
可以供后来事件使用；没有预用当前合法性。

新平行 mark 的自然界为
$P(\xi_{T_{\rm bottom}+h+1})\le P(\Theta)$，包括底层包末 $h=q$，
故自然语义保持。这个界不要求上层 family 也在此结束。

随后 native 选出的 $S\subset(p,e)$ 是有限严格升序包；每个新目标是当前 owner
对相应源点的实际像，严格位于旧末行点与其隐含 cap 之间。
普通阶梯公式保持行型、全部边、owner 和准确 direct marks。
§3 给该 family 的 ActiveSat。

每条入口旧行、每份冻结 marks 都有限。祖先链严格下降，父记录有限；
每个 native family 跳过，因此整个扫描有限完成。所有插入保留旧 cap 和末 owner。
这证明定理。

本节的前缀包—历史截断推导与
[无 Sat 的全间隙前缀包证明](<full-gap-unrestricted-prefix-packet.zh-CN.md>)相同，
但其 (9) 在这里由父包选择器保证，而不是靠填满整个间隙。

## 6. 父前缀与原平衡 BMS 带保持

若父项 ActiveSat，一次合法短复制保留其 cut 前缀。扫描入口 record 为空。
逐行扫描这个前缀时，原祖先包因 ActiveSat 为空；此前没有 native 记录，
父包也为空；mark 没有记录可用。因此整个旧前缀不动。
该论证给父 cut 前缀保持，没有要求更强的 $e=p+1$。

对[旧平衡 BMS 端口带](<../iblp-laver-bms-20261013/balanced-ribbon-bridge.zh-CN.md>)，
其全部 marks 为空，且每个原祖先包都为空。原 BMS 宏复制后也仍是同类带。
扫描归纳于是给 record 始终为空、选择器 (1) 始终为空。
所以原固定指标平衡带单步恒等式**逐字保持**；原来的 all-index 带恒等式若采用
相同合法复制及 guard，也不因这个扫描替换而改变。

这不是说所有无 marks 输入都保持原 native：一般无 marks 输入可以先发生 native，
稍后另一行读到它的父 family，进而补进原祖先链没有的点。
本节明确使用的是平衡带“整次扫描都不产生原生包”的不变量。

## 7. 准确范围

这个选择器保留了旧 BMS 带，而不会像全间隙强饱和那样强迫所有 active 复制区间
只剩一行。它还为实际标记传送提供所需前缀包，不再依赖入口 Sat_rec。

但这仍不是完整增强结论。仍需分别检查新基本列的比较、全部参数的合法复制域、
强度嵌入以及固定指标计数。特别地，多次 full copy 可能提高 cap，
不能仅凭最后扫描保 cap 就称整个基本列保持小周期窗口。
也不能把添了更多父包直接解释为序型变大。

**独立审计。** t3_audit 独立核对了旧基行身份与 record 的匹配、父包严格落于
源间隙、$\delta$-前驱覆盖的并集证明、前缀包传送及历史截断边界。
确认该扫描定理不需 Sat_rec，且没有将复制定义域或全尾复制的端点预算作为已证。
