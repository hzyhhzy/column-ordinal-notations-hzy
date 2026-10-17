# 带标记补全的 BLP：一个已证明的保守版本与完整版本的缺口

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

> 历史范围说明：本文保留早期保守版本的独立证明。用户随后已把持续目标扩为
> 完整标记 BLP 良序和 IBLP / DEN2 良序；当前范围、后续一般长词引理和未决
> 接口以 `wellorder_goal_state.md` 为准。下文“本次请求的目标”只指本文写作
> 时的较早请求，不能用来缩小现行目标。

核对日期：2026-09-07。材料为本目录的 iblp.md、IBLP 定义 PDF、旧稿 blp with mark completion.md，以及 [arXiv:2501.06733v5](https://arxiv.org/html/2501.06733v5) 第 2 节。NE 按本次取得的 [DEN2.ts](https://github.com/SmileLee-lyx/ne-rewritten/blob/master/src/notations/DEN/DEN2.ts) 核对，本地快照在 source_review/DEN2.ts。

**任务对象。** 用户要求的是：依据 IBLP / DEN2 的标记规则，将无限展开改回 BLP 的短复制，设计完整的带标记补全 BLP，并证明定理 2.25 仍成立。IBLP / DEN2 是其改为无限展开的对应版本；这里无限展开允许按有限参数继续全尾复制，每个有限参数的输出仍是有限模式。证明 IBLP / DEN2 本身良序或把定理推广到无限展开版本，不是本次请求的目标。

**结果的范围。** 下文构造一个会自动产生标记、使用标记增加行条目和步长的 BLP 系统，并完整证明定理 2.25 的对应结论。它是 note 的一个保守片段：只允许两顶点转移链，标记语义加强为行嵌入全局相等，补全增加有限可计算的边检查。**用户要求的完整带标记补全 BLP 尚未证明完；不能将剩余工作说成“只剩 DEN2”。** 即使使用 BLP 短复制，完整标记规则的截断高度、整块输送及后继块恢复仍需证明。

## 1. 旧 note / 证明中需要先修正的问题

### 1.1 完整行、core 与短复制终点

全文采用论文的完整行
$$
s_i=(s_{i,1}<\cdots<s_{i,-2}=i<s_{i,-1}=i+1),
\quad A_i=s_i\setminus\{i+1\},
\quad d(i)=A_i[-(\ell_i+1)].
$$
正索引从 1 开始。设末行编号为 n，令
$$
L=\ell_n,\qquad a=A_n[-L-1],\qquad e=A_n[-L],\qquad c=A_n[1].
$$
论文定义 2.12 复制的源行恰为
$$
\boxed{a,a+1,\ldots,e-1.}
$$
因此，在 **core 约定下**，note 所写的终点 $A_n[-L]$ 应减 1。IBLP 的全尾复制 $a,\ldots,n$ 不能直接代替这个操作。

### 1.2 旧稿使用了错误的截断等价语义

这里所需的 Laver 截断等价是
$$
f\equiv_\alpha g
\iff
\forall x,y\in V_\alpha\;(x\in f(y)\iff x\in g(y)).
\tag{1}
$$
它比较 $f(y)\cap V_\alpha$ 与 $g(y)\cap V_\alpha$，不同于旧稿 S.3 的普通函数限制
$f\restriction V_\alpha=g\restriction V_\alpha$。

旧稿 S.8 在其自身的强语义下有一个完整反例。取 I3 嵌入 j，临界序列为 $\kappa_0<\kappa_1<\cdots$，令
$$
\theta_i=\kappa_i\ (0\le i\le4),\qquad j_1=j_2=j,\qquad j_3=e:=j(j(j)).
$$
完整行为
$$
s_1=(0,1,2),\quad s_2=(0,1,2,3),\quad s_3=(2,3,4),
\quad \ell_1=\ell_2=\ell_3=1.
$$
仅 $M_2=\{1\}$ 非空。由于 $\operatorname{tr}_2(1)=(1,0)$、$j_2=j_1$，这是旧稿定义下的有效 marked BLS，可取 $m=1$。

复制末行时 $a=c=2$，只复制源行 2。旧规则保留 $y=1<c$ 的标记，新末行为 $(0,1,3,4)$，新末嵌入为 $e(j)$。但 $e(j)\circ e=e\circ j$，e 固定 $\kappa_1$，故
$$
e(j)(\kappa_1)=e(\kappa_2)=\kappa_3
\ne\kappa_2=j(\kappa_1),\qquad \kappa_1\in V_{\kappa_2}.
$$
输出不满足旧稿的强标记语义。**此反例针对旧稿的语义，不是正确弱截断版本的反例。**

### 1.3 跨复制边界的因子位置

设源转移链为 $(i_1,\ldots,i_{l'})$，$i_l$ 是首个小于 a 的顶点。若
$$
i_l=A_n[k],\quad z=A_n[k+L],\quad
\operatorname{tr}_n(z)=(m_1,\ldots,m_s),\quad m_s=i_l,
$$
则合法拼接所对应的因子链应为
$$
\varphi(i_1),\ldots,\varphi(i_{l-1}),
m_1,\ldots,m_{s-1},i_l,\ldots,i_{l'-1}.
\tag{2}
$$
已复制前缀只到 $l-1$，未复制尾部从 $i_l$ 开始。note 与旧稿把 $j_n(j_{i_l})$ 留在左边、让尾部从 $i_{l+1}$ 开始，不是这条 transfer 的因子链。修正此处之后，仍须逐次证明截断高度足够。

## 2. 直接标记模式及其实现

称 $\widehat p=(s,\ell,M)$ 为本文的**直接标记 BLP**，若底层 $(s,\ell)$ 是论文定义 2.6 的 BLP，每个 $y\in M_i$ 满足
$$
2\le y<i,\qquad y=A_i[k],\qquad k>\ell_i,\qquad
A_i[k-\ell_i]=d(y).
\tag{3}
$$
即
$$
\operatorname{tr}_i(y)=(y,d(y)).
$$
一个**直接标记 BLS**是底层模式的普通 BLS，外加
$$
\boxed{y\in M_i\Longrightarrow j_i=j_y.}
\tag{4}
$$
(4) 是全局函数相等，因而蕴含 note 对这种转移链的局部要求。这是在定义一个较小但可证明封闭的系统，不是在把所有 DEN2 标记解释成全局相等。

排除 0、1 是为了保证后继型复制时所有标记都能恢复，排除 i 则让标记只引用较早行。第一、二行无标记。删尾直接删除末行及其标记。

## 3. 复制保持引理

底层可复制性和复制使用论文定义 2.12。对实际需要的条目，
$$
\varphi(x)=
\begin{cases}
x,&x<c,\\
A_n[k+L],&x=A_n[k]<a,\\
n+x-a,&x\ge a.
\end{cases}
$$
只在论文的可复制条件全部满足时执行。对源行 $\sigma\in\{a,\ldots,e-1\}$ 和目标行 $\tau=n+\sigma-a$，定义
$$
M'_\tau=\{\varphi(y):y\in M_\sigma,\ y\ge a\}.
\tag{5}
$$
前 $n-1$ 行的标记保持。此处没有采用 PDF 定义 10(b) 的跨边界规则。

**引理。** 该复制保持直接标记实现、m、首两个和最后基数；末嵌入是 $j_n(j_{e-1})$。

**证明。** 采用普通 copied BLS。若 y 被保留，则 $a\le y<\sigma\le e-1$，所以被引用行 y 也已经复制，
$$
j'_\tau=j_n(j_\sigma)=j_n(j_y)=j'_{\varphi(y)}.
$$
严格递增的复制映射保持行位置与步长，并给出
$d'(\varphi(y))=\varphi(d(y))$。由 (3) 得新的直接转移条件。其他性质由普通 copied BLS 构造成立。证毕。

## 4. 普通补全产生完成包和新标记

只对论文的 suitable 行执行普通补全；本模型不自动加入 PDF 的所有短行补全。设当前第 r 行完整行长为 $2L+1$，$L\ge2$，令
$$
p=s_r[L]=d(r),\quad a=s_r[L+1],\quad
T=(u_1<\cdots<u_q),\quad p<u_1<\cdots<u_q<a.
$$
通常使用论文 fullcomp 选出的 T：从 a 开始反复取对应完整行的倒数第三个条目，直到不大于 p，取内部顶点并升序排列。T 为空就不操作。

普通补全把原第 r 行替换为以下完整行：
$$
\begin{aligned}
s'_{r+h}
 &=\operatorname{sort}\bigl(A_r\cup\{u_1,\ldots,u_{h+1}\}
       \cup\{r+1,\ldots,r+h+1\}\bigr),&
\ell'_{r+h}&=L+h+1\quad(0\le h<q),\\
s'_{r+q}
 &=\operatorname{sort}\bigl(A_r\cup T\cup\{r+1,\ldots,r+q+1\}\bigr),&
\ell'_{r+q}&=L+q.
\end{aligned}
\tag{6}
$$
旧行号与旧列按
$$
\rho(x)=x\ (x\le r),\qquad \rho(x)=x+q\ (x>r)
$$
重编号：原第 r 行之前保持，原第 r 行之后的行及其条目按此变换。

被拆行的旧标记在各新行中保留；第 $r+h$ 行新增标记
$$
r,r+1,\ldots,r+h-1\qquad(0\le h\le q).
\tag{7}
$$
其他旧标记按 $\rho$ 重编号。保存 $\operatorname{Rec}(r)=T$，其由构造保证的**完成包性质**为
$$
\theta_{r+h}=K(\theta_{u_h})\ (1\le h\le q),\qquad
j'_r=j'_{r+1}=\cdots=j'_{r+q}=K,
\tag{8}
$$
其中 K 是原第 r 行嵌入。记录只允许由此构造产生，不能任意输入一个序列当作有效包。

**引理。** 普通补全保持全部旧标记，产生的全部新标记满足 (3)–(4)。

**证明。** 普通 BLS 补全插入 $K(\theta_{u_h})$，并在所有替换行中使用 K，故底层实现及 (8) 成立。

令 $u_0=p$。从 (6) 直接读出
$$
d'(r+h)=u_h\qquad(0\le h\le q).
$$
第 $r+k$ 行内，条目 $r+h$（h<k）的步长前驱是 $u_h$，所以新标记转移为 $(r+h,u_h)$；相应行嵌入都是 K。

对被拆行的旧标记 $y=A_r[k]$，由 $k>L$、y<r，它在新增源条目之后，其旧步长前驱在第 L 项或更前。中间行中标记位置与步长都增加 h+1；最终行中两者都增加 q，故旧前驱不变，被引用的 y 行也不变。对后方旧行，若引用行 r，则新包首行仍有 $d'(r)=d(r)$、嵌入 K；其他引用只是一致重编号。所有旧标记保持。证毕。

## 5. 使用完成包的标记补全

设当前行 i 有标记 y，且已有非空记录
$$
\operatorname{Rec}(y)=(u_1<\cdots<u_q),\qquad y+q<i.
$$
此时 $\operatorname{tr}_i(y)[-2]=y$，正是 PDF 定义 13 的直接转移情形。令
$$
U=\{u_1,\ldots,u_q\},\quad V=\{y+1,\ldots,y+q\},\quad
s_i^+=\operatorname{sort}(s_i\cup U\cup V),\quad \ell_i^+=\ell_i+q.
\tag{9}
$$
定义
$$
\operatorname{Edges}(s,L)=\{(s[k],s[k+L]):1\le k\le |s|-L\}.
$$
仅当下列**有限语法检查**全部通过时执行 (9)：

1. $|U\cup V|=2q$，且 $(U\cup V)\cap s_i=\varnothing$。
2. 最小条目不变，末两项仍为 i,i+1，新完整行与新步长满足 BLP 行条件。
3. 每条旧步长边、每对新增 $u_h\mapsto y+h$ 都是新步长边。可直接检查
$$
\operatorname{Edges}(s_i^+,\ell_i+q)
=
\operatorname{Edges}(s_i,\ell_i)\cup\{(u_h,y+h):1\le h\le q\}.
\tag{10}
$$

失败就跳过。成功后在 $M_i\cup V$ 中只保留满足新 (3) 的元素；新增源 U 不标记。其他行不改。

这一步**不插入全局行或列**：U、V 都是此前普通补全已命名的列。它只给当前行加入已证实的对应关系，并非把 y+h 凭空当作新基数。

**引理。** 此规则保持直接标记 BLS 实现、全部基数及行嵌入。

**证明。** 由标记及完成包，
$$
j_i=j_y=K,\qquad
j_i(\theta_{u_h})=\theta_{y+h},\qquad j_{y+h}=j_i.
$$
所以 (10) 右侧每条边都由同一个 $j_i$ 实现；最小条目不变保证其临界点正确。

也可只逐边检查位置差：旧边数为 $|s_i|-\ell_i$，新边数为
$$
(|s_i|+2q)-(\ell_i+q)=(|s_i|-\ell_i)+q.
$$
新增源不在旧行，故旧边与 q 条新边互异，数量正好覆盖全部新边。

保留旧标记原有的全局等式，新标记用 $j_{y+h}=j_i$，再由 (3) 的筛选保证有效。还要检查其他行：旧边 $(d(i),i)$ 在 (10) 中保留，i 仍是倒数第二条目，所以新 d(i) 等于旧 d(i)。其他行引用 i 的直接转移也不变。证毕。

## 6. 有限扫描、M 与 E

定义有限扫描 C：开始时令 Rec 为空，从左到右只访问进入扫描时存在的各行。每到一行，冻结其现有标记集合，按升序各尝试一次第 5 节补全；随后若当前行 suitable，执行第 4 节 fullcomp 并保存记录。新插入的行跳过，新标记不在同一步重新处理。扫描结束后丢弃 Rec，它不是输出模式的一部分。

扫描必定有限：旧行数有限，每次冻结的标记数有限，选源链严格下降。更后方的插入不改变已保存包及其源列。由前两条引理，扫描保持直接标记实现、m、首两个和最后基数、最后嵌入。

定义
$$
\widehat p.M=C(\widehat p.\mathrm{Copied}).
\tag{11}
$$
这个补全次序与原论文 M 不同，但它保留归纳所需的端点和末嵌入性质；这里没有声称新旧函数数值相同。

对 successor / limit 类型，E 按论文定义 2.16 递归：$E(0)=del$，之后添加原定义规定的无标记三点行，再进行第 3 节复制。**E 内不增加扫描 C。** 对应的 BLS E 用原定义 2.18 的 linedness 见证建立辅助末行，再由复制引理验证标记。

因此 M、E 均保留 m、$\theta_0,\theta_1,\theta_{-1}$。M 的末嵌入是 $J(P)(h)$；E 的末嵌入可写成
$(J(P)(h_0))(h_1)$，中间嵌入临界点小于原末基数，如原论文引理 2.19。

## 7. 定理 2.25 的对应结论及完整证明

定义部分可计算函数（按从上到下的优先次序）
$$
F(\widehat p,m)=
\begin{cases}
m2^m,&p\text{ 为零模式},\\
F(\widehat p.del,m),&p\text{ 不可复制},\\
g^{2^m}(m),\quad g(x)=F(\widehat p.del,x),&p\text{ 为后继型},\\
F(\widehat p.E(m),m),&p\text{ 为极限型},\\
F(\widehat p.M,m),&\text{其余情形}.
\end{cases}
\tag{12}
$$
底层类型完全按原论文定义 2.15 判断。

**定理。** 在原论文的 I3 与 $\operatorname{Iter}(j)$ 框架下，若 P 是直接标记 BLP $\widehat p$ 的直接标记 BLS 实现，m=P.m，则 $F(\widehat p,m)$ 有定义，且
$$
\boxed{(P.\theta_0,P.\theta_1,P.\theta_{-1})
\text{ 是 }F(\widehat p,m)\text{-lined}.}
$$

### 7.1 外层良基归纳

记 $\Theta(P)$ 为末基数、J(P) 为末嵌入。取原论文定义 2.28 的良基关系：末基数严格降低，或末基数相等而末嵌入变成原末嵌入应用于另一个 $\operatorname{Iter}(j)$ 中的嵌入，再取传递闭包。其良基性来自论文引理 2.27。附加标记不改变该下降参数。这里不假设 DEN2 的序关系良基。

删尾严格降低末基数。M 由一次复制及末嵌入不变的有限扫描构成，故 P.M<P。E 的两次应用关系及中间临界点界给 P.E<P。它们的直接标记实现已在前文证明。

零模式使用原论文的基本 linedness 放大引理。不可复制分支先对 P.del 用归纳，再用临界点为删尾末基数、把它映至原末基数的嵌入，应用于最后一个 linedness 见证，将终点延长且保持见证数量；所需嵌入由引理 2.11 存在。极限分支和 M 分支直接使用严格下降及首尾基数保留。

后继分支需要下面的额外检验。

### 7.2 后继展开恢复全部标记

设 p 后继型，$\widehat q=\widehat p.E(t)$，$N=\widehat q.n$。辅助三点行的首列为 2；源行为 2,...,N，复制映射为
$$
\psi(x)=x\quad(x<2),\qquad \psi(x)=x+N-1\quad(x\ge2).
\tag{13}
$$
旧块为前 N 行，新块为行 N+1,...,2N-1。由于每个标记 y≥2，(5) 在此次复制中**没有丢失任何标记**。

取任意 $Q\models\widehat p.E(t+1)$，不要求 Q 来自某个指定实现的复制。旧块 $R^{old}=Q|N$ 实现 $\widehat q$，其末基数
$$
\nu=Q.\theta_{N+1}<Q.\Theta.
$$
抽取新块，定义
$$
\begin{aligned}
R^{new}.\theta_0&=Q.\theta_0,&R^{new}.\theta_1&=Q.\theta_1,\\
R^{new}.\theta_s&=Q.\theta_{s+N-1}&&(2\le s\le N+1),\\
R^{new}.j_s&=Q.j_{s+N-1}&&(2\le s\le N).
\end{aligned}
$$
补第 1 行可以直接取 $R^{new}.j_1=R^{new}.j_2$：复制块第二行实现
$(0,1,\psi(2),\psi(3))$、步长 1，所以其前三项正好实现新第一行。也可用原论文的基数搬移引理补造这一行。

(13) 的逆重编号恢复全部行与步长。对任意 $y\in M_s$，Q 的标记语义已给
$$
Q.j_{s+N-1}=Q.j_{y+N-1},
$$
所以 $R^{new}.j_s=R^{new}.j_y$。y≥2 保证不涉及补造的第 1 行；转移位置也完全恢复。故 $R^{new}$ 实现的是整个 $\widehat q$，不仅是去标记模式。

如果 $(Q.\theta_0,Q.\theta_1,\nu)$ 已有 M-lined 见证，可将它们用作 $R^{new}$ 的初始见证，设置 $R^{new}.m=M$。这些数据不改变行嵌入与标记。同时
$$
\Theta(R^{new})=\Theta(Q),\qquad J(R^{new})=J(Q).
\tag{14}
$$

### 7.3 后继分支的双重归纳

固定后继型 P，令 $g(x)=F(\widehat p.del,x)$。对 t 证明
$$
H(t):\quad Q<P,\quad Q\models\widehat p.E(t)
\Longrightarrow
g^{2^t}(Q.m)\text{ 有定义且是 Q 的 linedness 下界}.
$$
H(t) 同时量化所有正整数 Q.m。H(0) 直接使用外层归纳于实现 $\widehat p.del$ 的 Q。

若 H(t) 已证，取 $Q<P$ 实现 E(t+1)。旧块末基数严格较小，故 $R^{old}<Q<P$。由 H(t)，
$$
M=g^{2^t}(Q.m)
$$
有定义，并得到到 $\nu$ 的 M 个见证。用它们建立第 7.2 节的新块并设置参数 M。由 (14)，新块与 Q 具有相同下降参数，所以 $R^{new}<P$。再用 H(t)，得到有定义的
$$
g^{2^t}(M)=g^{2^{t+1}}(Q.m)
$$
及所需见证。这也同时证明每次迭代求值的有定义性。

最后令 t=m=P.m，代入 Q=P.E(m)<P，利用首两个和末基数保留，即得 (12) 的后继分支。全部分支完成，定理得证。

**量词限制。** 未证明任意指定标记集合的语法模式都有实现，因此不能照搬原论文 Remark 2.26，断言 F 在所有带标记语法输入上全定义。这里的定理是“对每个直接标记 BLS 实现”。

## 8. 一个实际触发标记补全的可实现例子

取完整行：

| 行号 | 完整行 | 步长 | 标记 |
|---|---|---:|---|
| 1 | (0,1,2) | 1 | 无 |
| 2 | (0,1,2,3) | 1 | 无 |
| 3 | (0,1,2,3,4) | 2 | 无 |
| 4 | (0,1,2,4,5) | 2 | 无 |
| 5 | (0,1,3,5,6) | 2 | 无 |
| 6 | (0,1,3,5,6,7) | 2 | 5 |

此模式有直接标记实现：先取底层 BLP 的任一普通实现（原论文 Remark 2.26），再令 $j_5=j_6$。第 5 行的要求是第 6 行要求的子集，所以替换有效；其他行没有标记。d(5)=1，第 6 行条目 5 的两步前驱也是 1。

第 5 行的 fullcomp 选 T={2}：源间隙为 (1,3)，第 3 行倒数第三项为 2，然后链到 1 停止。普通补全后的后面三行为
$$
\begin{array}{c|c|c|c}
i&s_i&\ell_i&M_i\\\hline
5&(0,1,2,3,5,6)&3&\varnothing\\
6&(0,1,2,3,5,6,7)&3&\{5\}\\
7&(0,1,3,5,7,8)&2&\{5\}.
\end{array}
$$
记录 Rec(5)={2}。处理第 7 行的标记 5，借用完成包的对应 $2\mapsto6$，得到
$$
\boxed{s_7^+=(0,1,2,3,5,6,7,8),\quad \ell_7^+=3,\quad M_7^+=\{5,6\}.}
$$
旧边 $0\mapsto3,1\mapsto5,3\mapsto7,5\mapsto8$ 与新边 $2\mapsto6$ 在新行内位置差全为 3。它确实增加映射信息和步长。

check_guarded_mark_completion.py 已核验此例、拒绝重复插入及错误的新边，并对三次 a=2 的 E 复制验证全部行与标记的块恢复，行数为 13、25、49。输出为 guarded_mark_completion_checks.json。程序只检验有限语法与边证书；嵌入和终止性依靠上述数学证明，不由有限测试代替。

## 9. 距离完整带标记补全 BLP 的目标还差什么

**后续研究更新。** full_marked_copy_work.md 已进一步给出真正可实现的输入，反驳“任意裸 marked BLS 上，原短复制过滤保持正确弱截断语义”。它不是标准初始项生成域的反例，也未证明输出不存在其他实现。用户后续已把良序目标明确限定为标准生成域；因此完整路线必须保留并证明生成过程的额外不变量，不能再以任意裸 marked BLS 的普遍保持引理作为未经核验的前提。

1. **完整复制的弱截断演算。** 使用 (1)，修正 (2)，证明每次左复合与尾部替换后的截断至少为目标 $\theta_{x+1}$。
2. **保存历史上界的整包输送。** y 后插入 q 个基数时，旧 $\theta_{y+1}$ 成为新 $\theta_{y+q+1}$。当前裸标记只要求到新 $\theta_{y+1}$ 的等价，不能仅由它推出到 $\theta_{y+h+1}$ 的新标记等价。扫描的证明状态应保存旧截断的重编号、每层 transfer 的包宽度和嵌入副本关系，再证明 PDF 邻接条件足够，或者增加可计算的整包检查。只说“新标记是旧等价的限制”不足。
3. **后继块恢复或替代递归。** 将长链标记或额外补全加入 E 后，必须重新证明全部标记的块抽取。仅有实现闭包、首尾保持及末嵌入下降，不足以支持原后继分支 $2^m$ 次迭代的公式。

独立核查还找到一个使裸 PDF 补全出现重复条目的纯语法例子；但其原标记条件与行映射矛盾，不能有 marked BLS 实现。因此它只否定“对任意语法状态都自动有整包”的无条件说法，**不能反驳用户要证明的条件性定理**。可重放分析见 den2_definition_work.md 与 den2_packet_probe.py。

另有版本区别：本次 DEN2 的 compTo 没有 PDF 定义 13(3) 的逐层邻接检查，也没有其去重步骤；seqFrom 的阈值处理亦不同。不能把当前源码与 PDF 逐字等同。完整目标下一步必须固定所证明的版本。

本稿完成的是第 2–8 节的保守定理。采用 BLP 短复制、允许一般转移链及 note 截断标记语义的完整版本仍未证明。IBLP / DEN2 无限展开版本及其序数良序性是另一个层次的问题，本次没有将其作为待完成目标。

## 10. 配套核查文件

- audit_draft_work.md：旧稿审计，含其 S.8 的完整强语义反例。
- theorem_transfer_work.md：原定理接口及后继块抽取的独立核对。
- den2_definition_work.md：PDF / 源码差异、包输送问题和不可实现的纯语法反例。
- check_guarded_mark_completion.py、guarded_mark_completion_checks.json：本文保守规则的有限检查。
- source_review/DEN2.ts：本次核对的源码快照。

原 note、PDF 和旧证明文件均保留。
