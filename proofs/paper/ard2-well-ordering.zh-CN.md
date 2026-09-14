# ARD2：全上下文行锚图的良序证明 · [English](ard2-well-ordering.md)

2026-09-14。[PDF](ard2-well-ordering.zh-CN.pdf) · [定义](../../notations/ARD2/definition.zh-CN.md) · [Python](../../notations/ARD2/ard2.py) · [NER](../../notations/ARD2/ARD2.ne-rewritten.js) · [普通 Lean](../../lean/src/ARD2Final.lean)。

ARD2 是 ARD 的全上下文版本：行锚和根都可引用本列，父仍严格向前。本文证明实际有限展开规则，不证明 ARD2 强于 ARD 或不弱于 IPD。软件资源保护不是数学规则。弱体系内的纸面推导与普通 Lean 内核验证是两项不同交付。

## 1. 公理、语法与定理

使用经典集合论

$$
S=KP_\omega+\text{“存在不可数序数”}.
$$

KP 包含外延、空集、配对、并集、无穷、$\Delta_0$ 分离、$\Delta_0$ 收集和完整集合归纳。不可数指大于 $\omega$ 且不存在从 $\omega$ 到它的集合满射。不增加幂集、完全分离或收集、选择、宇宙反射或大基数公理。

有限图 $G=(C_0,\ldots,C_{m-1})$ 的第 $j$ 列包含压缩组

$$
(k,p,q),\qquad k\le j,\quad q\le j,\quad p<j.
\tag{1}
$$

所有坐标为自然数。它表示全部根原子 $(k,t,p,j)$，其中 $t\le q$。同一 $(k,p)$ 只留最大根，忽略重复关系但保留空列。列内按 $(p,k,q)$ 递减排列，列内及列间均取字典序，真前缀较小。列序也等于完整根原子按 $(p,k,t)$ 递减排列后的比较。

种子 $A_n$ 有 $n$ 列，$C_0=\varnothing$，其余 $C_j=\{(j,j-1,j)\}$。以 $D(H)$ 表示 $H$ 及有限次展开后代，路径忽略 $0\to0$ 自环。标准域和顶端为

$$
U=\bigcup_{n<\omega}D(A_n),\qquad \mathsf{Top}[n]=A_n.
\tag{2}
$$

**定理。** $S$ 证明：所有结构合法有限图存在一个实际的序数值集合函数 $\mu$，每个非空图的每项展开（包括指标零）都严格降低 $\mu$；标准域 $U$ 按上述列序良序；加入最大外顶端后仍良序。

“良序”包括每个非空集合子集有最小元，不只排除可计算降链。全部合法图的列序并不良序，例如

$$
[\varnothing]^{r+1}[(0,0,0)]>
[\varnothing]^{r+2}[(0,0,0)]>\cdots.
$$

这不是展开链。构造器只验证式 (1)，不能把任意合法输入自动当成标准式。

## 2. 实际展开与有限结构引理

$0[n]=0$。非空图在指标零或空末列时删末列。否则令 $x=m-1$，按 $(k,q,p)$ 选末列最大组 $(k,c,r)$，置

$$
\ell=x-c>0,\qquad N_b=x+b\ell,\qquad c_b=c+b\ell,
\qquad
\phi_b(i)=\begin{cases}i&i<c,\\ i+b\ell&i\ge c.\end{cases}
\tag{3}
$$

对 $n>0$，输出有 $x+n\ell$ 列。取以下并集，作根闭包并规范化：

1. 对 $b=0,\ldots,n$ 复制 $G\restriction x$，行、最大根、父、子四坐标全部按 $\phi_b$ 搬运。
2. 对 $b<n$，在第 $N_b$ 列放接缝。原末列组 $(h,p,q)$ 在 $h<k$ 时保留搬运后的根；在 $h=k$ 时将最大根改为 $\min(\phi_b(q),\phi_b(r)-1)$，负根不加入；高行不加入。
3. 接缝再加入所有 $(h,c_b,N_b)$，其中 $h<\phi_b(k)$。

切点前各份复制重合；新来源块首列与接缝合并。第三项的最大根是当前接缝自身，不是控制父。此定义不调用新输出的展开。

**引理 2.1。** 展开保持合法性，旧末列之前不变，且 $G[n]$ 是 $G[n+1]$ 的完整列前缀。

$\phi_b$ 严格递增，故保留式 (1)；SELF 随所在子列一起移动。新生行严格低于接缝，最大根等于接缝，父严格低于接缝。切点前各列的引用不超过自身，所以全部固定。增加指标时，新接缝及来源块从旧输出的末端之后开始，既有列不再被改写。删列和零情形直接成立。

**引理 2.2。** $G\ne0$ 时，$G[n]<G$。

只需看原末位置 $x$。父大于 $c$ 的旧组不变：若同行，控制最大性迫使其最大根小于 $r$。父 $c$、行 $k$ 的最大根 $r$ 则降低或消失。新包的行较低；来源切点列的父全部低于 $c$。即使来源列同时有 SELF 行和 SELF 根，在这里重绑到 $x$，其父仍低于 $c$，不能填回首次差异。因此父优先的列序严格降低。

这些结构性质本身还不证明良序。以下独立构造展开下降秩。

## 3. 弱集合论中的准备

暂在 $S+V=L$ 中工作，令 $\kappa$ 为最小不可数序数。使用 [ARD 论文第 3、5.1、8 节](ard-well-ordering.zh-CN.md) 的集合构造，其内容在这里明确列出：

- 对每个 $0<\alpha<\kappa$，从一个收集到的见证集合中按可构造良序取首个满射，得到统一集合函数 $e(\alpha,\cdot):\omega\twoheadrightarrow\alpha$。函数在其他输入取零而总化。
- 每个实际集合函数 $v:\omega\to\kappa$ 的值都有严格小于 $\kappa$ 的共同上界。否则用 $e$ 及自然数对编码得到 $\omega\twoheadrightarrow\kappa$。
- 对任意以 $\kappa$ 为论域、使用固定有限或可数语言的集合结构，满足关系及取最小序数见证的有限元 Skolem 运算构成集合。将 $\omega\cup\{\omega,\gamma\}$ 对这些运算及 $e$ 闭合，所得可数集合是一个序数 $\delta$，满足 $\max(\omega,\gamma)<\delta<\kappa$，并给出该结构的初等初段。

最后一项只反射一个集合结构，不反射集合论宇宙。可数性来自有限闭项的实际自然数枚举，不是可数选择。普通 KP 可用的 $\Sigma_1$ 收集、$\Delta_1$ 分离及序数递归足以构造这些集合。有限图、模板、有限路径和坐标运算先制成自然数解码表；下文的有界公式查询已有表，不把未经处理的任意算术公式称为纯集合语言的 $\Delta_0$。

## 4. 带两个 SELF 坐标的有限需求关系

取有限标签元组集合 $B=(\kappa+1)^{<\omega}$。宽度为 $m$ 的图表示为严格递增元组 $f$，所有标签大于 $\omega$ 且小于 $\kappa$，并满足

$$
\operatorname{Rep}(G,f)\iff
\operatorname{Inc}(f)\land
\bigwedge_{(h,t,p,j)\in G}R(f(h),f(t),f(p),f(j)).
\tag{4}
$$

内部第 $j$ 列的 SELF 是普通下标 $j$，读取 $f(j)$。它与下面的虚拟端点标志不同。

宽 $m$ 的端点模板 $N$ 是有限组 $(h,t,p)$，满足 $h,t\le m$、$p<m$。下标 $m$ 是模板 SELF。若 $f$ 全部小于端点 $b$，定义

$$
\widehat f_b(i)=\begin{cases}f(i)&i<m,\\ b&i=m,\end{cases}
\qquad
\operatorname{End}_b(N,f)=
\bigwedge_N R(\widehat f_b(h),\widehat f_b(t),f(p),b).
\tag{5}
$$

允许性仅用行、根两坐标，不含父阶段，也不含旧 ARD 的“根在切点前”限制：

$$
\operatorname{Adm}^{b}_{K,\theta}(N,f)\iff
\bigwedge_N(\widehat f_b(h),\widehat f_b(t))<_{\rm lex}(K,\theta).
\tag{6}
$$

$FR_{K,\theta}(a,b)$ 断言：对每个有限合法图 $G$、模板 $N$、切点 $c<m$ 和元组 $f\in B$，若 $\operatorname{Rep}(G,f)$、$f[m]\subset b$、$f(c)=a$、式 (6) 及 $\operatorname{End}_b(N,f)$ 成立，则存在 $g\in B$，使

$$
\operatorname{Rep}(G,g),\quad g[m]\subset a,\quad
g\restriction c=f\restriction c,\quad \operatorname{End}_a(N,g).
\tag{7}
$$

输出不必再次满足旧允许性。普通行和根读新标签 $g$；模板 SELF 则重绑成 $a$。不能因输入某个普通地址恰好取值 $a$，就把它误当成 SELF。

定义

$$
R(K,\theta,a,b)\iff
K\le b\le\kappa\ \land\ \theta\le b\ \land\ \omega<a<b
\ \land\ FR_{K,\theta}(a,b).
\tag{8}
$$

### 4.1 因果递归及集合存在性

按 $(b,K,\theta)$ 字典序递归。输入图内部关系的右端点小于 $b$；输出图及输出模板的右端点不超过 $a<b$；输入端点模板则由式 (6) 只读更早的 $(K,\theta)$。先拒绝无效守卫和不允许输入，再查询端点关系，故没有同阶段读取。

例如令 $M=\kappa+1$，用 $M^2b+MK+\theta<M^3$ 编码阶段。阶段编码和投影先构成集合表。给定历史，在 $\kappa+1$ 上以有界分离取得本阶段的全部父参数 $a$；其他量词在 $\omega$、$B$ 或既有有限解码表中有界。历史的有效性有界可验且由归纳唯一；极限时收集已存在的短历史并取并，不收集所有可能历史的幂集。因此式 (8) 给出一个集合关系。

### 4.2 两个弱化性质

由允许需求的包含性直接得到：

$$
\eta\le\theta,\ R(K,\theta,a,b)\Longrightarrow R(K,\eta,a,b),
\tag{9}
$$

$$
H<K,\ \eta\le b,\ R(K,\theta,a,b)\Longrightarrow R(H,\eta,a,b).
\tag{10}
$$

式 (10) 的根可重置到整个端点 $b$，而不只到父 $a$。其理由是任何低行控制允许的需求，其行不超过 $H<K$；无论其根多大，都已被原控制允许。这里没有跨父单调性断言。

## 5. 四种顶端切片、一致性与初始表示

先完成 $R$ 的递归，再定义四个集合谓词：

$$
P_{00}(K,T,a)=R(K,T,a,\kappa),\qquad
P_{10}(T,a)=R(\kappa,T,a,\kappa),
$$

$$
P_{01}(K,a)=R(K,\kappa,a,\kappa),\qquad
P_{11}(a)=R(\kappa,\kappa,a,\kappa).
\tag{11}
$$

未标 SELF 的参数均小于 $\kappa$。取固定结构

$$
\mathcal A=(\kappa;<,R\restriction\kappa,P_{00},P_{10},P_{01},P_{11},e,\omega).
$$

这不是给结构加入域外常量 $\kappa$；四个 $P$ 是不同元数的实际关系。第 3 节给出任意高的 $\delta<\kappa$，使 $\mathcal A\restriction\delta\prec\mathcal A$。

### 5.1 Pointed 端点一致性

令 $\iota_\delta:\delta+1\to\kappa+1$ 固定所有 $u<\delta$ 并将 $\delta$ 送到 $\kappa$。对 $u,v\le\delta$、$a<\delta$，证明

$$
R(\iota_\delta(u),\iota_\delta(v),a,\kappa)
\quad\Longleftrightarrow\quad R(u,v,a,\delta).
\tag{12}
$$

对真实良序 $(\delta+1)^2$ 的字典序归纳，同时处理所有 $a$。$a\le\omega$ 时两边皆假。不能先整体处理普通坐标，再一次处理所有 SELF：较高普通行的允许需求可能已含较低行的 SELF 根。

正向，取 $\delta$ 下的允许输入。各端点需求的 pointed 行根对严格小于 $(u,v)$；用归纳假设将其端点从 $\delta$ 换成 $\kappa$。映射 $\iota_\delta$ 严格保序，普通标签低于 $\delta$，所以允许性被保持。应用左边的 $FR$ 得到式 (7)；输出全部在 $a$ 以下，读的是同一个 $R$，就是右边需要的输出。

反向，若右边成立而左边失败，固定一个有限坏请求的图形、模板与切点。将标签元组展开为有限个变量；根据模板的两个 SELF 标志，用式 (11) 的相应谓词写输入端点关系。控制坐标也是普通参数或 SELF 标志，允许性可拆成普通序数比较、恒真或恒假，不需要域外参数 $\kappa$。“不存在输出”的候选标签全部小于 $a$，只读取右端点不超过 $a$ 的共同 $R$。

坏输入标签元组作为存在变量，而不是固定参数。这个有限坏请求公式的普通参数均低于 $\delta$，故初等性给出全在 $\delta$ 内的坏输入。其允许端点对仍严格较小；用归纳假设换成指向 $\delta$ 的关系，违反右边的 $FR$。这证明式 (12) 的全部四种 SELF 情形。

### 5.2 强端点供应

对同一 $\delta$，有

$$
R(K,\theta,\delta,\kappa)\qquad(K,\theta\le\kappa).
\tag{13}
$$

取任意允许输入 $G,N,c,f$，其中 $f(c)=\delta$。只固定前缀 $f\restriction c$，反射“存在严格递增标签 $z$，表示内部图 $G$、固定此前缀，并满足指向 $\kappa$ 的全部端点模板”的有限存在公式。端点关系用四个 $P$ 表达。旧 $f$ 见证其真。

公式不固定控制 $K,\theta$，不固定 $z_c=\delta$，也不要求输出满足旧允许性。初等性得到全部小于 $\delta$ 的 $z$；对每份模板用式 (12)，普通坐标取新 $z$，SELF 取 $\delta$，于是得到 $\operatorname{End}_\delta(N,z)$。这正是所需输出。式 (13) 包含普通控制参数大于父高度的情形。

### 5.3 任意合法图的表示

取递增初等高度 $\delta_0<\cdots<\delta_{m-1}$，令 $f(j)=\delta_j$。对原子 $(h,t,p,j)$，按 $h=j$ 与 $t=j$ 的两个标志选择式 (11) 中的切片。在父高度 $\delta_p$ 用强供应，再在子高度 $\delta_j$ 用式 (12)，得到

$$
R(\delta_h,\delta_t,\delta_p,\delta_j).
\tag{14}
$$

例如双 SELF 原子先用 $P_{11}(\delta_p)$，再得到 $R(\delta_j,\delta_j,\delta_p,\delta_j)$；不能把普通坐标一致性偷用于等号边界。根在父之后不构成障碍，因为式 (13) 没有限制 $\theta\le\delta_p$。故所有合法有限图都有表示；空图用空元组。

## 6. 两种 SELF 的逐块拼接

**引理。** 若非空图 $G$ 有末标签 $\beta$ 的表示，则每个 $G[n]$ 都有全部标签严格小于 $\beta$ 的表示。

删列直接限制表示。其余沿用式 (3)。令 $D_0=G\restriction x$；从 $D_b$ 到 $D_{b+1}$ 追加一份长度 $\ell$ 的来源块，并在首列合并接缝 $b$，则 $D_n=G[n]$。

归纳保有宽 $N_b$ 的标签 $f$：表示 $D_b$ 且全部小于 $\beta$；对每个原来源最大根组，保有四坐标的来源关系；对每个原末列最大根组，保有指向固定虚拟端点 $\beta$ 的关系。定义

$$
v_b(i)=\begin{cases}f(\phi_b(i))&i<x,\\ \beta&i=x.\end{cases}
$$

虚拟末列关系为 $R(v_b(h),v_b(q),v_b(p),\beta)$。特别是原末列的两个 SELF 都读取 $\beta$，不访问尚不存在的数组元素 $f(N_b)$。置 $K=v_b(k)$、$\theta=v_b(r)$、$a=f(c_b)$。控制关系给出 $R(K,\theta,a,\beta)$。

### 6.1 实际接缝是允许需求

把接缝的所有根原子做成宽 $N_b$ 的端点模板，其中下标 $N_b$ 表示 SELF：

- 低行保留组由虚拟关系及根弱化得到，其行严格低于 $K$，根可以是 SELF。
- 同控制行的根被截到 $\phi_b(r)$ 以下，所以标签严格低于 $\theta$。控制根若为 SELF，所有截断根都是普通地址；若不是 SELF，截断仍给严格不等式。不再要求根位于切点以前。
- 新生包有 $h<\phi_b(k)$、最大根 $N_b$。由式 (10)，其最大根虚拟关系为 $R(f(h),\beta,a,\beta)$；再根弱化得到全部较小根。所有这些需求因行降低而允许。

父始终是普通地址。对整个 $D_b$ 应用控制的 $FR$，得到 $g$，满足

$$
\operatorname{Rep}(D_b,g),\quad g[N_b]\subset a,\quad
g\restriction c_b=f\restriction c_b,\quad \operatorname{End}_a(N,g).
\tag{15}
$$

### 6.2 接回来源块

定义标签串

$$
h=g\mathbin{\frown}f[c_b,N_b).
\tag{16}
$$

它严格递增、全在 $\beta$ 以下，且 $h(N_b)=a$。对每个 $i<x$，有关键恒等式

$$
h(\phi_{b+1}(i))=f(\phi_b(i)).
\tag{17}
$$

$i<c$ 时使用固定前缀；$i\ge c$ 时使用拼接尾段。等式同时适用于行、根、父及来源子列，而不仅是普通父指针。

现在穷尽输出关系：旧图的全部坐标不超过其子列，故取自 $g$，由式 (15) 成立；新来源最大根组由式 (17) 运输；搬运跳过的新中间根由式 (9) 补足；实际接缝由 $\operatorname{End}_a$ 得到，其中两个模板 SELF 都读 $a=h(N_b)$。

来源切点 $C_c$ 也可能同时有两个 SELF。它们通过下一份来源复制成为新首列自身，标签同样是 $a=f(c_b)$；来源父仍在固定前缀内，所以来源关系与接缝合并完全兼容。不能错误地把来源 SELF 保留成旧切点下标。

虚拟原末列的 SELF 则继续读固定 $\beta$。其普通坐标由式 (17) 保持，故下一阶段的所有虚拟关系和来源关系也保留。这与实际接缝重绑到 $a$ 是两个不同用途，不矛盾。归纳到 $b=n$，拼接引理成立。

## 7. 实际下降秩与标准域良序

设 $Q\subseteq\omega$ 是唯一规范的合法有限图码集合。固定解码表、$R$ 与 $B$ 后，表示存在性在既定集合中有界。定义

$$
\mu(0)=0,\qquad
\mu(G)=\min\{\beta<\kappa:\exists f\in B\,
 [\operatorname{Rep}(G,f)\land f(|G|-1)=\beta]\}\quad(G\ne0).
\tag{18}
$$

初始表示保证候选非空；在 $Q\times\kappa$ 上一次有界分离得到整个函数图。不存在为每个图另作无界选择的步骤。非空表示标签大于 $\omega$；对实现最小末标签的表示应用第 6 节，得

$$
G\ne0\Longrightarrow\mu(G[n])<\mu(G).
\tag{19}
$$

随后才把秩与列序联系。对 $\mu(H)$ 归纳，证明 $D(H)$ 中任意两图按有限可达性可比：若两条路径的首步是 $H[i]$、$H[j]$，它们都是 $H[\max(i,j)]$ 的前缀，因而可由第零项删列取得。两图同属这个更小秩的后代锥，应用归纳假设。

每一步又由引理 2.2 严格降低列序，故同锥内

$$
V<W\Longrightarrow V\in D(W)\setminus\{W\}
\Longrightarrow\mu(V)<\mu(W).
\tag{20}
$$

种子满足 $A_{n+1}[0]=A_n$，因此任意两个标准图有共同种子祖先。$\mu\restriction U$ 严格保序。任意非空集合子集 $X\subseteq U$ 的秩像可有界分离取得，取最小像值及其原像就得到 $X$ 的最小元。将外顶端映到 $\kappa$，仍严格保序。

这里没有把可及性或表示存在性放进标准域定义，也没有使用“任意良序的递增并都是良序”这个错误的无条件命题。

## 8. 移除 V=L 与形式验证范围

普通 KP 的可构造内类 $L$ 满足相同的 KP，并具有相同的序数和自然数。具体层构造及收集账本见 [ARD 论文第 8 节](ard-well-ordering.zh-CN.md)。环境中的不可数序数在 $L$ 内仍不可数，因为 $L$ 中的满射也会是环境中的满射。因此在 $L$ 内得到某个序数 $\chi$ 和实际集合函数 $\mu:Q\to\chi$。

有限语法、规范化、展开及有限路径在环境与 $L$ 间逐码一致；序数比较绝对，故同一个实际函数在环境中仍满足式 (19)。在环境中重做第 7 节，就对包括不属于 $L$ 的标准域子集在内的所有集合子集得到最小元。转移的是实际秩，而不仅是“$L$ 认为良序”的陈述。不要求 $\chi$ 在环境中仍不可数。

普通 Lean 对实际有限规则构造了无条件初始表示、逐块下降和标准列序良序。语义后端使用 mathlib 的 $\omega_1$、经典选择，以及实际的最小坏请求／最小延拓见证闭包；并未把 $S$ 的语法、证明系统或整段 $S$-推导编码进 Lean。尤其，上述 KP 满足关系和构造性宇宙部分仍是纸面论证，不是对象理论 Lean 模块。最终定理及可复现的验证状态见 [Lean 说明](../../lean/README.zh-CN.md) 和 [验收记录](../../VALIDATION.zh-CN.md)。

有限程序测试不能替代本证明；普通 Lean 也不是 Python/JavaScript 虚拟机的逐行验证。本文没有证明 ARD 是 ARD2 的前段、ARD2 可嵌入 IPD、任何相对序型不等式，或公理上界最优。
