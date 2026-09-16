# ARD-legacy：弱集合论中的良序证明 · [English](ard-legacy-well-ordering.md)

旧版数学证明完整保留；本文 ARD 指 ARD-legacy，低行包规则不是新版规则。新版见 [ARD skyline](ard-well-ordering.zh-CN.md).


2026-09-13。ARD = Anchored Row Diagrams（行锚图）。

[PDF](ard-legacy-well-ordering.zh-CN.pdf) · [定义](../../notations/ARD-legacy/definition.zh-CN.md) · [NER 弧线图展开器](../../notations/ARD-legacy/ARD-arcs.ne-rewritten.js) · [Python](../../notations/ARD-legacy/ard.py) · [普通 Lean 入口](../../lean/ARD-legacy/src/ARDFinal.lean)

本文证明链接定义及两个展开器采用的有限规则。实现中的时间、内存及绘图保护不是数学规则的一部分。本文给出弱公理体系中的纸面论证；普通 Lean 代码是另一项交付，不是该弱理论形式系统中推导的编码。本文不证明 ARD 比 Y、RPD、LRD 或 Ω-LRD3 强。

## 1. 定理及定义域

采用经典集合论

$$
S=KP_\omega+\text{“存在不可数序数”}.
$$

这里 KP 使用外延、空集、配对、并集、无穷、$\Delta_0$ 分离、
$\Delta_0$ 收集和完整集合归纳；“不可数”指大于 $\omega$ 且不存在从
$\omega$ 到该序数的集合满射。不假设幂集、完整分离、完整收集或选择公理。

**定理。** 在 $S$ 中：

1. 存在一个定义于所有结构合法的有限 ARD 图的序数值集合函数 $\mu$，使
   $G\ne0\Longrightarrow\mu(G[n])<\mu(G)$。因此不存在无限非零展开链，
   即使每一步任意改变基本列指标。
2. 从标准种子有限展开可达的图，按实现规定的列字典序构成良序。
3. 加入最大外顶端，其基本列为标准种子，仍是良序。

本文的良序指严格线性序且每个非空**集合子集**有最小元，不仅仅是排除某类可计算降链。

第二项的“标准”限制不可删除。所有结构合法图的列字典序本身不是良序：

$$
[\varnothing]^{m+1}[(0,0,0)]
>
[\varnothing]^{m+2}[(0,0,0)]
>\cdots.
$$

这个反例与第一项不矛盾：字典序下降不一定是展开可达。
NER 输入验证只检查结构合法性，没有声称识别标准域。

### 1.1 有限图、根闭包及比较

图 $G=(C_0,\ldots,C_{m-1})$。第 $j$ 列由压缩组

$$
(k,p,q),\qquad k<j,\quad q\le p<j
$$

组成，所有坐标都是自然数；不要求 $k\le p$。它表示全部原子
$(k,t,p,j)$，其中 $0\le t\le q$。同一 $(k,p)$ 的组只保留最大 $q$。
以下“图中的原子”总指这个完整根闭包。

组按 $(p,k,q)$ 递减排列；列内及列间均用字典序，真前缀较小。
这与把每列全部原子按 $(p,k,t)$ 递减列出再比较相同：同一父和行的根组成
连续段，首先不同的最大根已经决定比较结果。

### 1.2 展开

$0[n]=0$。非空图第零项删末列；若末列为空，任何指标都删末列。
其余情形令 $x=m-1$，按 $(k,q,p)$ 选择末列最大控制组 $(k,c,r)$，置

$$
\ell=x-c>0,\qquad
\phi_b(i)=\begin{cases}i&i<c,\\i+b\ell&i\ge c.\end{cases}
$$

$G[n]$ 有 $x+n\ell$ 列，按下列并集再取根闭包、规范化：

* 对 $b=0,\ldots,n$，复制 $G\restriction x$，其行锚、父、最大根、子列
  四坐标全部由 $\phi_b$ 移动。
* 对 $b=0,\ldots,n-1$，在 $x+b\ell$ 列放接缝。每个原末列组 $(h,p,q)$：
  若 $h<k$，加入 $(\phi_b(h),\phi_b(p),\phi_b(q))$；
  若 $h=k$，将最大根改为
  $\min(\phi_b(q),\phi_b(r)-1)$，非负才加入；若 $h>k$，不加入。
* 同一接缝还加入所有 $(h,\phi_b(c),\phi_b(c))$，其中 $0\le h<\phi_b(k)$。

切点是控制父 $c$，不是 $\max(k,c)$。各复制块在切点前重合，重合不重复计边。
这是一段有限循环的定义，不调用新输出图的展开。

标准种子及标准域为

$$
A_0=0,\quad A_1=[\varnothing],\quad
A_{n+1}=A_n\frown[(n-1,n-1,n-1)]\quad(n\ge1),
\qquad U=\bigcup_{n<\omega}D(A_n),
$$

其中 $D(H)$ 包含 $H$ 及其有限展开后代。展开路径忽略 $0\to0$ 自环。
外顶端 $\mathsf{Top}$ 大于一切有限标准式，且 $\mathsf{Top}[n]=A_n$。

## 2. 有限结构引理

**引理 2.1。** 展开保持结构合法性，且
$G[n]$ 是 $G[n+1]$ 的完整列前缀。

$\phi_b$ 严格递增，所以复制保持所有向前引用。生成组满足
$h<\phi_b(k)<x+b\ell$，父及根 $\phi_b(c)<x+b\ell$。
切点前各列的全部引用仍在切点前，故所有复制对此前缀一致。
从指标 $n$ 增至 $n+1$ 时，新接缝从 $x+n\ell$ 开始，
新来源块也从该位置开始，旧输出完全不动。空末列及零的情形直接成立。证毕。

**引理 2.2。** $G\ne0$ 时，$G[n]<G$。

删列情形直接成立。其余情形，前 $x$ 列不变。第 $x$ 列是第零接缝与
下一块的来源列 $C_c$ 的并集。来源列全部父坐标小于 $c$，且这些坐标不移动。
控制最大性还说明末列没有行大于 $k$ 的组。原末列中父大于 $c$ 的组全部保留：行小于 $k$ 的不截断；行等于 $k$ 的
最大根必须小于 $r$，否则违背 $(k,r,c)$ 是控制最大元。
在父 $c$、行 $k$ 处，原最大根 $r$ 被降至 $r-1$ 或整个组消失。
生成组的行都小于 $k$，来源组的父都小于 $c$，不能填回该差异。
因此按 $(p,k,q)$ 比较，第一个差异严格变小。证毕。

任意前缀可由反复第零项删除获得。以上引理还没有证明良序，后文先独立构造展开下降秩。

## 3. KP 所需的集合构造

暂在 $S+V=L$ 中工作。取最小不可数序数 $\kappa$；这是用完整归纳在一个
已知不可数序数以下取最小元，不是用完整分离收集“不可数”谓词。
$\kappa$ 是极限序数，每个 $0<\alpha<\kappa$ 有自然数满射。

对这些满射作 $\Delta_0$ 收集，取得包含见证的集合 $C$。在 $V=L$ 中
该集合有构造出的集合良序；从 $C$ 中按该良序选每个 $\alpha$ 的首个有效见证，得到

$$
e:\kappa\times\omega\longrightarrow\kappa,
\qquad e(\alpha,\cdot):\omega\twoheadrightarrow\alpha\quad(0<\alpha<\kappa),
\quad e(0,n)=0.
$$

作为下文一阶结构的函数符号时，把它扩成总二元函数：第二参数不在 $\omega$ 中时取值 0。

此处只用一个已有集合的可构造良序，不用任意集合族的选择公理。
可构造良序可在足够高的 $L$ 层中按定义公式及有限参数元组递归构造。

**可数有界性。** 对每个集合函数 $v:\omega\to\kappa$，有
$\sup_n(v(n)+1)<\kappa$。否则用 $e$ 枚举各 $v(n)+1$，再对自然数对编码，
得到 $\omega$ 到 $\kappa$ 的满射，矛盾。

普通 KP 可用 $\Sigma_1$ 收集、$\Delta_1$ 分离、有限元组集合、
沿给定序数的有界定义递归，以及集合结构的满足关系。
相关背景见 [McKenzie，§2，Lemma 2.2、2.3、2.6、Theorem 2.8](https://arxiv.org/html/1806.08500v4#S2)。
这里只调用这些背景工具，以下动态关系和拼接是本记号需要另证的部分。

有限图、有限模板和有限路径用自然数编码；其原始递归解码与计算关系是可用的集合。
需要字面上的有界公式时，先取得这些解码表，以表作为固定集合参数；
不把任意算术公式未经处理就称为纯集合语言的 $\Delta_0$ 公式。

## 4. 动态有限需求关系

设 $B=(\kappa+1)^{<\omega}$，即所有取值于 $\kappa+1$ 的有限元组构成的集合。
对宽度 $m$ 的图定义

$$
\operatorname{Inc}(f)\iff |f|=m\ \land\
\omega<f(0)<\cdots<f(m-1)<\kappa,
$$

$$
\operatorname{Rep}(G,f)\iff
\operatorname{Inc}(f)\land
\bigwedge_{(h,t,p,j)\in G}R(f(h),f(t),f(p),f(j)).
\tag{4.1}
$$

空元组满足对应的空条件。严格递增及标签大于 $\omega$ 是表示的正式组成部分，
不能只保留边的合取。

模板 $N$ 是有限组 $(h,t,p)$，其中 $h<m$、$t\le p<m$。定义

$$
\operatorname{End}_b(N,f)=\bigwedge_N R(f(h),f(t),f(p),b),
$$

$$
\operatorname{Adm}_{K,\theta}(N,f,c)=
\bigwedge_N\bigl[f(h)<K\ \lor\
(f(h)=K\land t<c\land f(t)<\theta)\bigr].
$$

$FR_{K,\theta}(a,b)$ 断言：对所有有限合法 $G,N$、切点 $c<m$、$f\in B$，若

$$
\operatorname{Rep}(G,f),\quad f[m]\subset b,\quad f(c)=a,\quad
\operatorname{Adm}_{K,\theta}(N,f,c),\quad\operatorname{End}_b(N,f),
$$

则存在 $g\in B$ 满足

$$
\operatorname{Rep}(G,g),\quad g[m]\subset a,\quad
g\restriction c=f\restriction c,\quad\operatorname{End}_a(N,g).
\tag{4.2}
$$

其中 $f[m]\subset b$ 意味着每个分量小于 $b$。特别注意输出模板中行值是
$g(h)$，不是被冻结的 $f(h)$。输出无需再次满足原来的 $\operatorname{Adm}$。

定义

$$
R(K,\theta,a,b)\iff
K<b\le\kappa\ \land\ \theta\le a<b\ \land\ \omega<a
\ \land\ FR_{K,\theta}(a,b).
\tag{4.3}
$$

### 4.1 这个递归确实给出集合

允许一切 $K<\kappa$，不预先固定可数的行域上界。按 $(b,K,\theta)$ 字典序递归：

* 输入图内部关系的右端点小于 $b$。
* 输出图内部及输出模板的右端点不大于 $a<b$。
* 输入端点模板由于 $\operatorname{Adm}$，具有更小的行参数，或者同行而根参数更小。

定义递归操作时，先排除不允许的输入，再读取它的端点模板；不能无条件查询尚未定义的关系。
无效守卫直接赋假，不需要递归查询。

例如置 $T=(\kappa+1)\cdot\kappa$、$\Gamma=T\cdot(\kappa+1)$，用

$$
\iota(b,K,\theta)=T\cdot b+(\kappa+1)\cdot K+\theta
$$

编码有效阶段 $K<\kappa,\theta<b\le\kappa$。阶段编号小于 $\Gamma$，严格保持所需顺序。
阶段编码及其坐标投影也预先制成集合表：在固定有界积域上对 KP 可用的
$\Delta_1$ 序数运算应用收集和分离即可；核验历史时只查询这些表。
给定历史后，该阶段为哪些 $a\le\kappa$ 成立，是对 $\kappa+1$ 的有界分离：
图形码、模板码、切点都在固定编码集合中，所有标签组都在 $B$ 中。
有效历史可用有界条件检验，且由归纳唯一。沿 $\Gamma$ 递归，极限阶段用
$\Sigma_1$ 收集已经存在的短历史并取并；没有收集全部可能历史的幂集步骤。
所得 $R$ 因而是一个集合关系。

### 4.2 三个直接性质

1. **严格守卫：** $R(K,\theta,a,b)$ 蕴含式 (4.3) 的全部不等式。
2. **根弱化：** 若 $\eta\le\theta$ 且 $R(K,\theta,a,b)$，则 $R(K,\eta,a,b)$。
   原因是 $(K,\eta)$-允许的需求包含于 $(K,\theta)$-允许的需求。
3. **降低行：** 若 $H<K$、$\eta\le a$、$R(K,\theta,a,b)$，则 $R(H,\eta,a,b)$。
   每个 $H$-允许模板的行值不大于 $H$，故严格小于 $K$。其余输入及输出条件相同。
   **不要求 $H\le a$**；后文确实需要允许行锚在切点以后。

## 5. 任意有限图的初始表示

置 $P(K,\theta,a)=R(K,\theta,a,\kappa)$，考虑一个固定集合结构

$$
\mathcal A=(\kappa;<,R\restriction\kappa,P,e,\omega).
$$

$R\restriction\kappa$ 表示四个坐标都小于 $\kappa$ 的限制。
结构中没有域外常量 $\kappa$，也没有冻结的行域上界常量。

### 5.1 足够多的初等初段

对每个 $\gamma<\kappa$，存在

$$
\max(\omega,\gamma)<\delta<\kappa,
\qquad\mathcal A\restriction\delta\prec\mathcal A.
\tag{5.1}
$$

利用集合满足关系，为每个存在公式选取序数顺序中的最小见证，无见证时取 0。
这些是可作为集合取得的可数个有限元 Skolem 运算。
将 $\omega\cup\{\omega,\gamma\}$ 对这些运算及 $e$ 闭合，得到集合 $H$。
有限闭项可实际用自然数枚举，故 $H$ 可数；这不是选择可数个任意见证。
若 $\alpha\in H$，由所有自然数在 $H$ 且对 $e$ 闭合可知 $\alpha\subseteq H$。
所以 $H$ 是序数 $\delta$，不可数性给 $\delta<\kappa$，而闭包包含
$\omega,\gamma$ 给严格下界。见证判据给出初等性。
只反射这个集合结构，不调用集合论宇宙的反射原理。

### 5.2 端点一致性

对每个上述 $\delta$，有

$$
P(K,\theta,a)\iff R(K,\theta,a,\delta)
\quad(K<\delta,\ \theta\le a<\delta).
\tag{5.2}
$$

对 $(K,\theta)$ 作字典归纳，同时考虑所有 $a$。若 $a\le\omega$，两边守卫皆假。

正向：给一个在 $\delta$ 下的允许输入，其端点模板由允许性只查询较早的
$(K,\theta)$。用归纳假设把这些模板换成 $P$ 模板，应用 $\kappa$ 处的
$FR$。输出全在 $a$ 以下，内部和输出模板读取同一个 $R$，就是所需输出。

反向：假定右边成立而 $P$ 不成立。守卫已经满足，故有固定有限形状
$G,N,c$ 及反例输入。其反例性可写成结构 $\mathcal A$ 中的一个有限公式：

> 存在标签组 $f$，满足内部表示、$f(c)=a$、$(K,\theta)$-允许性和
> $P$ 端点模板，但不存在全在 $a$ 以下、保留切点前缀的表示输出及指向 $a$ 的模板。

此处将每份固定有限标签组展开为有限个变量。公式的参数只有
$K,\theta,a,\omega$ 及有限形状信息，全部低于 $\delta$；特别不能漏掉参数 $K$。
初等性给出全在 $\delta$ 内的反例输入，再用归纳假设把其 $P$ 模板换成指向
$\delta$ 的模板。“无输出”在两结构中相同，因为候选输出全部小于 $a<\delta$，
且查询的右端点不大于 $a$。这与右边的 $FR$ 矛盾。

### 5.3 强端点供应

对同一 $\delta$，有

$$
P(K,\theta,\delta)\quad(K<\kappa,\ \theta\le\delta).
\tag{5.3}
$$

这里特意允许 $K\ge\delta$。取任何在 $\kappa$ 处、切点标签为 $\delta$ 的
允许需求 $G,N,c,f$。仅固定前缀 $u=f\restriction c$，其分量均小于 $\delta$。
反射以下有限存在公式：

$$
\exists(z_i)_{i<m}\left[
\operatorname{Inc}(z)\land z\restriction c=u\land
\bigwedge_G R(z_h,z_t,z_p,z_j)\land
\bigwedge_N P(z_h,z_t,z_p)\right].
\tag{5.4}
$$

旧输入 $f$ 见证其真。该公式没有控制参数 $K,\theta$，不固定 $z_c=\delta$，
不冻结任何切点后的旧行值，也不要求输出再次满足原允许性。
把 $\operatorname{Inc}$ 展开成结构中的公式时只写 $\omega<z_0<\cdots<z_{m-1}$；
末界“$<\kappa$”已经由变量的量词域保证，不是额外的域外参数。
初等性得到全在 $\delta$ 内的 $z$。每个新行值 $z_h<\delta$，
故 (5.2) 把 $P$ 模板逐项换成指向 $\delta$ 的模板。这正是 $FR$ 输出。

### 5.4 初始表示引理

取宽度为 $m$ 的任意结构合法图，有限次应用 (5.1)，选择递增的初等高度
$\delta_0<\cdots<\delta_{m-1}$，令 $f(i)=\delta_i$。
对原子 $(h,t,p,j)$，在 $\delta_p$ 处用 (5.3) 得
$P(\delta_h,\delta_t,\delta_p)$，即使 $h\ge p$ 也允许。
再在 $\delta_j$ 用 (5.2)，因 $h<j$ 而得

$$
R(\delta_h,\delta_t,\delta_p,\delta_j).
$$

所以 $\operatorname{Rep}(G,f)$ 成立。空图直接用空元组。
此处只选有限个高度，不需要另作无界选择。

## 6. 动态四坐标拼接引理

**引理。** 若非空图 $G$ 有末标签为 $\beta$ 的表示，则对每个 $n$，
$G[n]$ 有全部标签严格小于 $\beta$ 的表示。

空末列或指标零直接限制原表示。下面处理非空末列；沿用 $x,k,c,r,\ell,\phi_b$，置

$$
N_b=x+b\ell,\qquad c_b=c+b\ell.
$$

### 6.1 输出的分块分解

令 $D_0=G\restriction x$。从 $D_b$ 到 $D_{b+1}$，只追加 $\ell$ 列：
新第 $N_b+i$ 列是来源 $C_{c+i}$ 通过 $\phi_{b+1}$ 四坐标复制的列，
其中 $i=0$ 还并入第 $b$ 个接缝；最后规范化。

因为 $\phi_{b+1}(c)=N_b$，这恰好分解了第 1.2 节的展开并集，故
$D_n=G[n]$。这里来源仍是原图 $G$，不是把当前 $D_b$ 再展开一次。

设原表示为 $F$，$F(x)=\beta$。归纳构造宽度 $N_b$ 的 $f$，满足：

1. $\operatorname{Rep}(D_b,f)$，所有标签小于 $\beta$。
2. 每个原前缀组 $(h,p,q)\in C_j$、$j<x$，都有来源事实
   $$
   R(f(\phi_b(h)),f(\phi_b(q)),f(\phi_b(p)),f(\phi_b(j))).
   \tag{6.1}
   $$
3. 每个原末列组 $(h,p,q)$ 都有固定虚拟端点模板
   $$
   R(f(\phi_b(h)),f(\phi_b(q)),f(\phi_b(p)),\beta).
   \tag{6.2}
   $$

第零阶段由 $F\restriction x$ 给出，因 $\phi_0$ 是恒等映射。

### 6.2 接缝是一个允许的有限需求

在第 $b$ 阶段令

$$
K=f(\phi_b(k)),\quad\theta=f(\phi_b(r)),\quad a=f(c_b).
$$

控制组的 (6.2) 给出 $R(K,\theta,a,\beta)$。取 $N$ 为第 $b$ 接缝的
全部根原子的三坐标模板，视为当前 $D_b$ 中的地址。所有地址均小于 $N_b$。

普通接缝组的最大根关系来自 (6.2)，其较小根由根弱化得到。
若行来自 $h<k$，严格递增性使行标签小于 $K$；若行来自 $h=k$，
截断确保其每个根 $t<\phi_b(r)\le c_b$，所以 $t<c_b$、$f(t)<\theta$。
因此普通接缝全部允许。

生成组对应任意 $h<\phi_b(k)$、$t\le c_b$。有 $f(h)<K$、$f(t)\le a$，
对控制关系用降低行性质，得到

$$
R(f(h),f(t),a,\beta).
$$

它同样是允许模板。此处 $h$ 可以大于等于 $c_b$，所以不能额外要求行标签小于 $a$。

现在对整张 $D_b$ 应用 $FR_{K,\theta}(a,\beta)$，取得 $g$，满足

$$
\operatorname{Rep}(D_b,g),\quad g[N_b]\subset a,\quad
g\restriction c_b=f\restriction c_b,\quad\operatorname{End}_a(N,g).
\tag{6.3}
$$

### 6.3 拼接并核对所有来源

令

$$
h=g\frown f[c_b,N_b).
\tag{6.4}
$$

它的长度为 $N_b+\ell=N_{b+1}$。$g$ 全部小于 $a=f(c_b)$，故 $h$ 严格递增，
全在 $\beta$ 以下，且 $h(N_b)=a$。关键等式是

$$
h(\phi_{b+1}(i))=f(\phi_b(i))\qquad(i<x).
\tag{6.5}
$$

若 $i<c$，它处于固定前缀内，(6.3) 给等式。若 $i\ge c$，
$\phi_{b+1}(i)\ge N_b$，按拼接定义取到
$f(\phi_{b+1}(i)-\ell)=f(\phi_b(i))$。

该等式同时适用于行锚、根、父、子，不能只搬运后三个坐标。由它立刻得到下一阶段
的全部来源事实 (6.1) 和虚拟模板 (6.2)。再检查实际 $D_{b+1}$ 的全部原子：

* **旧图原子：** 子列小于 $N_b$，全部引用也小于 $N_b$，所以四个标签都取自
  $g$，由 $\operatorname{Rep}(D_b,g)$ 成立。
* **新来源组：** 先用 (6.5) 在最大根的四个坐标上运输 (6.1)。根闭包还可能填入
  $\phi_{b+1}$ 跳过的坐标；对任意 $t\le\phi_{b+1}(q)$，严格递增性给
  $h(t)\le h(\phi_{b+1}(q))$，再用根弱化。无需每个新根都是某个旧根的精确映像。
* **新接缝原子：** 子列是 $N_b$，其余坐标小于 $N_b$。由 (6.3)，
  这些坐标取自 $g$，而子标签是 $a=h(N_b)$，正好得到所需关系。

规范化的最大根总来自一个已经加入的组；不会创造新的行锚或父。
所以以上三类及其根弱化穷尽所有输出原子，$\operatorname{Rep}(D_{b+1},h)$ 成立。
归纳完成，取 $b=n$ 即得引理。证毕。

## 7. 一个全局下降秩与标准域良序

### 7.1 秩是单个实际集合函数

令 $Q\subseteq\omega$ 为唯一规范图码集，不把不同输入字符串作为不同图。
有限解码可总化，非法码返回错误标记；由其全定义的 $\Delta_1$ 性和
$\Sigma_1$ 收集，先取得所有输出，再用 $\Delta_1$ 分离取得解码函数表。
也可直接取得长度表和原子关联表。随后所有语法查询都只读这些已有集合。

定义

$$
\mu(G)=\begin{cases}
0,&G=0,\\
\min\{\beta<\kappa:\exists f\in B\,
[\operatorname{Rep}(G,f)\land f(|G|-1)=\beta]\},&G\ne0.
\end{cases}
\tag{7.1}
$$

初始表示引理保证每个非空图都有候选。固定解码表、$R$ 和 $B$ 后，候选性是
有界公式；加上“所有更小 $\gamma<\beta$ 均非候选”仍有界。
所以在 $Q\times\kappa$ 上一次分离便得到整个函数图，不需要额外收集各图的表示。
这里没有从部分 $\Sigma_1$ 解码函数偷用 $\Sigma_1$ 分离。

非空表示的标签均大于 $\omega$，故 $\mu(G)>\omega>0$。对实现最小末标签的表示
应用拼接引理，得

$$
G\ne0\quad\Longrightarrow\quad\mu(G[n])<\mu(G).
\tag{7.2}
$$

若输出为空，其秩为 0；否则输出有一个末标签小于旧最小末标签的表示。
序数不容无限严格下降链，因此所有非零展开都良基。

### 7.2 后代锥按可达性全排列

对 $\mu(H)$ 归纳，证明 $D(H)$ 中任意 $V,W$ 按展开可达性可比。
$H=0$ 时只有一个图。若一个等于 $H$，结论直接成立。
否则两条有限路径的首步分别是 $H[i]$、$H[j]$。令 $t=\max(i,j)$。
由完整前缀及反复第零项删除，二者均属于 $D(H[t])$，故 $V,W$ 也属于此锥。
由 (7.2)，$\mu(H[t])<\mu(H)$，使用归纳假设即得可比。

由引理 2.2，在同一锥内不同的 $V,W$，可达方向与列字典序严格下降方向一致，故

$$
V<W\quad\Longrightarrow\quad V\in D(W)\setminus\{W\}
\quad\Longrightarrow\quad\mu(V)<\mu(W).
\tag{7.3}
$$

注意逻辑顺序：先独立取得展开下降秩，再证明可达性全排列，最后才得到秩的保序性。
不能仅由前缀性质直接宣称任意后代锥是初段。

### 7.3 标准域和外顶端

$A_{n+1}[0]=A_n$，因此任意两个标准图都有共同的种子祖先。
(7.3) 说明同一个集合函数 $\mu\restriction U$ 在整个标准域严格保序。
对任意非空集合 $W\subseteq U$，其秩像是 $\kappa$ 的一个集合子集；
取像的最小序数，再取原像，便是 $W$ 的最小元。

这证明列字典序在 $U$ 上良序，不依赖“任意递增良序的并仍良序”这个错误的无条件说法。
还可推出每个 $D(A_n)$ 在 $U$ 中是初段：若 $V<W\in D(A_n)$ 且 $V\in U$，
共同种子锥内的可达性给 $V\in D(W)\subseteq D(A_n)$。

把外顶端的秩设为 $\kappa$，即可将 $U\cup\{\mathsf{Top}\}$ 严格嵌入
$\kappa+1$，且它到每个 $A_n$ 的展开也严格下降。
顶端不参与“第零项删列”的归纳；它在有限标准域证明之后单独加入。

## 8. 移除辅助假设 V=L

普通 KP 的可构造内类 $L$ 满足同样的 KP，具有相同的序数与自然数。
这调用的是普通 KP 的构造内类方法，不是幂集版 KP 或额外的大基数假设。
背景可参阅 [Rathjen，导言关于普通 KP 与 V=L 的说明及 §2 的 KP 公理](https://arxiv.org/html/1801.01897v1)。

具体地，$L_\alpha$ 层及其递归在 KP 中可构造；有界公式在传递的层之间绝对。
为验证 $L$ 中的有界收集，可在环境中收集见证连同其所属层的指标，再以一个共同层
覆盖它们；所用的是环境可用的 $\Sigma_1$ 收集。完整归纳也可相对化。
这里没有声称 KP 证明自身存在一个传递的集合模型。

若环境的 $\nu$ 不可数，则 $L$ 中也不存在 $\omega$ 到 $\nu$ 的满射，
因为任何这样的 $L$ 中函数也是环境中的函数。因此在 $L$ 内可以进行前文构造，
取得某个序数 $\chi$ 和一个实际集合函数

$$
\mu:Q\longrightarrow\chi
$$

及其非零展开严格下降性质。$\chi$ 是 $L$ 的最小不可数序数；不要求它在环境中仍不可数。

有限图的规范编码、展开计算、有限路径和种子都由有限计算决定，在环境与 $L$ 中逐码一致。
函数 $\mu$ 及其序数值是实际集合，严格序数比较绝对。因此环境中同一个函数仍满足 (7.2)。
在环境中重新应用第 7.2、7.3 节，得到标准域列序良序，并将顶端映到 $\chi$。

特别是环境可能有不属于 $L$ 的子集 $W\subseteq U$，但

$$
\{\beta\in\chi:\exists G\in W\ (\mu(G)=\beta)\}
$$

仍可有界分离取得并取最小元。转移的是这个实际的秩函数，不只是“$L$ 认为它良序”的断言。
故结论在原来的 $S$ 中成立。证毕。

## 9. 结论的边界与普通 Lean 验证

本文证明当前 ARD 在所有结构合法有限图上的非零展开良基、标准域的列序良序，以及加入最大外顶端后的良序。原始图全域的列序不是良序，第 1 节已给出反例。

动态行锚与其他三个坐标一起变化。第 5.3 节允许 $K\ge\delta$ 的强端点供应，以及第 6 节的四坐标恒等式，是相对于固定行标论证必须补出的内容，不能直接将旧 Lean 定理改名使用。

独立的普通 Lean 入口是 [ARDFinal.lean](../../lean/ARD-legacy/src/ARDFinal.lean)。其中有限几何采用完整根闭包编码；动态语义关系实际按 $(b,K,\theta)$ 递归构造，不把反射或初始表示当作外加公理。语义后端通过最小坏见证、最小前缀延拓见证及可数有限元闭包，构造端点一致性、强供应和初始表示。闭包运算的代码只有有限形状及自然数；可变序数 $K$ 是运算输入，不假设全部序数构成可数类型。

普通 Lean 构造与第 3—8 节的弱体系论证有以下具体区别：

- Lean 先在序数类型上作良基递归，守卫包含 $K<b$，然后限制到选定环境的 $\kappa$ 以下；纸面则直接在 $\kappa$ 以下取得一个有界集合表。递归依赖相同，但普通类型论中的构造本身不验证纸面的 KP 集合存在性账本。
- Lean 对实际最小 Bad、Ext 见证的坐标运算取闭包，而不构造 $\mathcal A$ 的完全初等初段。Bad 闭包要求 $K,\theta,a<\delta$；强供应仍允许 $K\ge\delta$，因为反射后的新行值全部小于 $\delta$。这实现了第 5.2—5.4 节真正需要的端点论证，不假设初等子结构供应器。
- 普通 HostAmbient 实现使用 mathlib 的实际第一不可数序数和经典选择来选择枚举。这不是纸面的 $S+V=L$ 构造或从 $L$ 转回 $S$ 的编码。特别地，Lean 公理报告中的 Classical.choice 不等于向本文的对象理论加入选择公理。
- Lean 的原始 Valid 谓词只检查坐标不等式，不要求排序或根闭包；标准式则是规范的。纸面压缩图表示完整根闭包。发布代码还给出独立有限并定义 PaperEdge、PaperFs：具体 Lean 展开与之逐原子相同，并在规范输入上作为唯一规范图完全相等；两者生成的标准域一致。压缩也保持图比较和控制组的选择。

最终普通 Lean 模块已编译通过，公理报告仅包含 propext、Classical.choice、Quot.sound，没有 sorry 或新增公理。在 OrdinalFormal.ARD 命名空间中，公开结论包括：

```text
valid_accessible
valid_step_wellFounded
standard_wellFounded
standard_strictWellOrder
standard_with_top_strictWellOrder
paper_standard_with_top_strictWellOrder
```

最后一个定理直接作用于独立有限并纸面定义生成的标准式。独立发布目录的完整重编译及验证清单见 [Lean 项目](../../lean/README.md)；增量模块编译不能代替该发布验收。

纸面证明不使用幂集、选择公理、完整分离、完整收集或额外反射公理。发布的普通 Lean 代码没有编码 $S$ 的语法、证明系统及“这是一段 $S$-推导”的验证器。有界程序测试核对实现，不代替数学良序证明；普通 Lean 核验也不自动成为 Python/JavaScript 解析器及绘图代码的逐行形式验证。

最后，本文不把 $\kappa$ 或 $\chi$ 的存在转换成未经证明的具体 PTO 比较，不声称这个公理上界最优，也不从共享一个上界推断 ARD 与旧记号等强或更强。

