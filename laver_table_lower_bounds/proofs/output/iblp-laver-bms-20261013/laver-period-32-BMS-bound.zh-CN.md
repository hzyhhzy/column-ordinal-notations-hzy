# 周期首次达到 32 的阶数：一个 BMS 极限层 FGH 下界

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本篇将本目录的统一引理接成最终数值比较。
公理条件是 **ZFC + I3**；这是纸面证明，尚未 Lean 形式化。
初始化直接使用 Qi 已发表的 linedness 结论，不依赖本目录较早的标记补全、
32 步启动或保端点重定位的证明。亦不使用另一个研究目录中的行数反馈。

BMS 端直接调用用户指定的
[固定指标下降与 FGH 对接总结](<BMS-fixed-index-to-FGH-summary.zh-CN.md>)
中的统一定理；该总结只证明 BMS 一侧，本篇负责补齐 Laver 一侧及最后的数值比较。
这完成的是 **BMS 层级的严格下界**，不是对主线所要求的结构性超 BMS 记号的交付。
不把 BMS 极限加一个后继、加 $\omega$ 或乘 $\omega$ 当成主线目标完成。

**更强的已接合结论：**[两次反馈的三层 BMS FGH 下界](<../iblp-030-laver-20261014/nested-bms-FGH-bound.zh-CN.md>)
给出 $q(5)>F_{\mathrm{BMS}}(F_{\mathrm{BMS}}(F_{\mathrm{BMS}}(F_3(257))))$。
它另检查了每次输出转成下一轮行数的开销。本篇保留不依赖反馈的基础证明，
两篇的依赖方向是该篇调用本篇的长链初始化及整数预算。

## 结论与约定

令

$$
q(5)=\min\{m:\text{大小为 }2^m\text{ 的普通二元 Laver 表首行周期至少为 }32\}.
$$

使用原 BM4 基本列，令

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h),\qquad
D(h)=\text{从 }R_h\text{ 固定取原 }[1]\text{ 到空的总步数}.
$$

原 `[1]` 等于本目录父表新表示的 `[2]`，所以也记作 $D_2(R_h)$。
FGH 的约定是

$$
F_\varnothing(x)=x+1,\quad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\quad
F_M(x)=F_{M[x]}(x)\quad(M\text{ 末列非零}),
$$

其中 $Z$ 是全零列。外顶端采用 $\mathrm{BMS}[x]=B_{x+1}$，即
$F_{\mathrm{BMS}}(x)=F_{B_{x+1}}(x)$。有限下标的 $F_3$ 也用同一约定。

**定理。** 在以上约定及 I3 假设下，$q(5)$ 存在，而且

$$
\boxed{q(5)>F_{\mathrm{BMS}}\bigl(F_3(257)\bigr).}
\tag{1}
$$

更一般地，令 $C=f(p_{\omega+2},1)$，其不使用序数记号的确切有限递归
定义见式 (5)。对任意正整数 $r,x$，有

$$
\boxed{r+\lceil\log_2(x+2)\rceil\le C
\quad\Longrightarrow\quad q(5)>F_{B_r}(x).}
\tag{1a}
$$

下面同时给出固定下降下界，以及原目标
$q(5)>F_{B_{11}}(10)=F_{\mathrm{BMS}[10]}(10)$ 的独立推论。
比较的是表的阶参数 $m$，不是元素个数 $2^m$。

## 1. 所需行数：任意高度的统一定理

记 $\ell(x)=\lceil\log_2(x+2)\rceil$。
[BMS 对接总结](<BMS-fixed-index-to-FGH-summary.zh-CN.md>)的统一定理给出

$$
\boxed{D(h)\ge F_{B_r}(x)
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}
\tag{2}
$$

它是关于任意 $r,x,h$ 的全称证明，不仅限于 17 行：
先把 FGH 精确编译成 $H_{W(B_r)}$，再加一行森林控制参数增长，
最后用祖先覆盖和行宽交换承载这个 $r+1$ 行、$x+4$ 列的辅助矩阵。
完整局部证明依次是
[FGH 到 Hardy](<fixed-index-growth-interface.md>)、
[森林控制器](<diagonal-forest-hardy-proof.zh-CN.md>)、
[计数覆盖与行宽交换](<ancestor-cover-growth.zh-CN.md>)。
所用输入是特定种子 $R_h$，不是任意有 $h$ 行的矩阵。

特别地，对每个 $h\ge7$，

$$
D(h)\ge F_{B_{h-6}}(10).
\tag{3}
$$

这里六行的损失对应固定输入 10；一般输入的损失为 $2+\ell(x)$。
不能在 (3) 中只换输入而保持同一行数要求。

## 2. 已发表的长链及其长度

固定 I3 嵌入 $j$，所有嵌入和临界点均来自同一个 $\operatorname{Iter}(j)$。
沿用[低端点初始化](<short-terminal-initialization.zh-CN.md>)中的
$K=j_{(11)}$、$\theta_5=K(\kappa_3)$、$\theta_6=j_{(10)}(\kappa_3)$、
$\theta_7=K(\theta_5)$。已知
$\theta_5<\theta_6<\theta_7<\kappa_4$。

[Qi《Notes on Laver Tables》第 3 节命题 1.3(1) 的证明](https://arxiv.org/html/2501.06733v5#S3)
直接给出

$$
(\kappa_0,\kappa_1,\theta_5)\text{ 是 }C\text{-lined},
\qquad C=f(p_{\omega+2},1),\qquad 2^C=m_{\omega+2}(2).
\tag{4}
$$

这里用的是该证明中的实际链，而不是反过来从临界点下标很大猜测链存在。
其长度可完全用有限整数递归写出：

$$
\begin{aligned}
g(x)&=x2^x,& u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),&C&=w(w(1)).
\end{aligned}
\tag{5}
$$

确切性由 $m_k(2^x)=2^{u_k(x)}$ 归纳得到；$m_\omega,m_{\omega+1}$
经这个共轭分别成为 $v,w$，故 $m_{\omega+2}(2)=2^{w(w(1))}$。
不需要计算上述整数的十进制表示。

## 3. 将长链变成保持小周期的 BMS 行数

有限初始化已有嵌入 $L_3$，满足

$$
\operatorname{crit}(L_3)=\kappa_3,\qquad
L_3(\kappa_3)=\theta_6,\qquad L_3(\theta_6)=\theta_7.
$$

令 $E=L_3(K)$，括号表示 application。由应用点像恒等式，

$$
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,\quad
E(\theta_6)=L_3(\theta_5)<\theta_7.
\tag{6}
$$

将 (4) 的每个点和每个嵌入统一取 $E$-像，得到
$(\kappa_2,\theta_6,E(\theta_5))$ 的 $C$ 段链，且
$E(\theta_5)<E(\theta_6)<\theta_7<\kappa_4$。

[统一前端插入引理](<lined-front-insertion.zh-CN.md>)因此给出高度
$H=C+2$ 的闭合相容组，封口严格低于 $\kappa_4$。
该引理对任意指定的有限链长成立，并同时归纳维护共同截断和封口界；
不是将互不相容的见证直接计作 BMS 行。

相容组为 $R_H$ 提供[带实现](<ribbon-initialization.zh-CN.md>)。
一次固定原 `[1]` 由若干删端点及一次保末端复制实现。
[有限计数引理](<balanced-ribbon-bridge.zh-CN.md>)给出：$H\ge3$ 时，
总下降步数严格小于实际删端点数；后者不超过初始末端的临界点下标。

若 $\kappa_4=\gamma_s$，则
$q(5)=s+1$：因为 $\kappa_3=\gamma_4$，而
$j(\gamma_t)=\gamma_a$ 当且仅当首行周期在阶参数 $a$ 处仍不超过
$2^t$、在 $a+1$ 处首次超过它。这使用
[Dougherty 第二篇第 2 节的有限表对应](https://arxiv.org/pdf/math/9503204)。
I3 保证这些临界点下标有限；周期每次只会保持或翻倍，故这里首次达到的周期是 32。
所以

$$
\boxed{q(5)>D(C+2).}
\tag{7}
$$

全部下降均使用标准 BMS 后代，终止性也可使用已有的
[BMS 良序定理](https://arxiv.org/html/2307.04606v2)。
辅助非标准矩阵的终止与计数比较另由祖先覆盖证明，不混同其数字字典序与序数。

## 4. 行数预算超过四倍的输入

令 $t=F_3(257)$。由 FGH 约定，

$$
F_2(x)=(x+1)2^{x+1}-1,\qquad t=F_2^{\circ258}(257).
$$

对于 $x\ge1$，$g(x)\ge2x$，且

$$
g^2(x)\ge g(2x)=2x2^{2x}\ge(x+1)2^{x+1}>F_2(x).
$$

函数均严格递增，又有 $g^3(1)=2048>257$，所以

$$
t<g^{\circ516}(257)<g^{\circ519}(1).
\tag{8}
$$

写 $b=g^{\circ258}(1)$。注意

$$
v(1)=u_2(1)=u_1(u_1(1))=u_1(8)=g^{\circ256}(8)=b.
$$

各 $u_k$ 对输入严格递增且大于恒等函数，并随 $k$ 不减。
这些性质对 $k$ 归纳：$u_{k+1}(x)$ 是递增且大于恒等的 $u_k$
迭代 $2^x$ 次，故至少为 $u_k(x)$；增加输入同时增加初值和迭代次数。
于是 $v,w$ 也递增且大于恒等函数。
因此

$$
\begin{aligned}
C&>w(1)=v(b)=u_{2^b}(b)\\
 &\ge u_1(b)=g^{\circ2^b}(b)
 =g^{\circ(2^b+258)}(1)\\
 &\ge g^{\circ521}(1)>g^2(t)\ge4t.
\end{aligned}
\tag{9}
$$

这里 $b\ge2048$，故中间的迭代次数比较绰绰有余。
仅用旧参数 $b+2$ 不能直接作同一推论：事实上
$F_2(x)>g(x)$ 且 $257>1$，所以 $t>b$。
本篇用文献现成长链 $C$ 补足了这点，而不是默认两者已足够接近。

## 5. 合并

先证明统一式 (1a)。若 $r+\ell(x)\le C$，则
$r+2+\ell(x)\le C+2$。把 $h=C+2$ 代入 (2)，再用 (7)，得到

$$
\boxed{q(5)>D(C+2)\ge F_{B_r}(x).}
\tag{10}
$$

严格性来自 Laver 一侧的第一步；没有把 BMS 总结中的非严格不等式改写为严格不等式。

对 $t\ge2$，$\ell(t)\le t$。式 (9) 因而给出

$$
C+2>t+3+\ell(t).
$$

把 $r=t+1,x=t,h=C+2$ 代入 (2)，再用 (7)：

$$
q(5)>D(C+2)\ge F_{B_{t+1}}(t)
=F_{\mathrm{BMS}}(t)=F_{\mathrm{BMS}}(F_3(257)).
$$

这证明 (1)。它没有使用一般的“序数下标越大，FGH 数值就越大”。
行数充足直接通过祖先覆盖及结构模拟转成计数比较。

原目标也直接得到：$C+2\ge17$，代入 $r=11,x=10$，有
$q(5)>F_{B_{11}}(10)$。同样，旧参数界 $q(5)>D(b+2)$
由 $C>b$ 和祖先覆盖的固定计数单调性恢复，不再需要标记启动证明。

统一式还能直接给出两个明确实例：

$$
q(5)>F_{B_{C-4}}(10),\qquad
q(5)>F_{\mathrm{BMS}}\!\left(\left\lfloor\frac{C-1}{2}\right\rfloor\right).
\tag{11}
$$

第一式用 $\ell(10)=4$。第二式置
$z=\lfloor(C-1)/2\rfloor\ge2$，有
$z+1+\ell(z)\le2z+1\le C$，故可取 $r=z+1,x=z$。
每个结论均独立满足行数预算，不需要先证明
$F_{\mathrm{BMS}}$ 对所有自然数输入单调。

## 6. 证明依赖和未使用的加强

整条证明只用以下三组接口：

1. BMS 总结中的 $D(h)\ge F_{B_r}(x)$，包括非标准辅助矩阵的覆盖处理。
2. Qi 命题 1.3(1) 证明给出的实际 $C$-lined 链，以及有限初始化中的
   $L_3$、$E=L_3(K)$。这里没有从“端点的临界点下标很大”倒推出 linedness。
3. 统一前端插入、无补全的平衡带保持性及删端点计数。
   它们将一条给定有限长度的链变成特定 $R_{C+2}$ 的实现。

所有实际嵌入始终属于同一个 $\operatorname{Iter}(j)$。
一般 $C$ 的构造使用有限归纳，不要求用程序生成 $C$ 个见证。
这是在 I3 条件下的数值定理；没有在此消除大基数假设。

不使用完整 IBLP 的良序性、原 IBLP `[2]` 与短复制的认同、
任意序数大小对固定指标次数的单调性，或“任意多一行就支配所有少一行矩阵”。
也不使用两次行数反馈，因此本结论可与后续超 BMS 设计分开审计。

## 核验范围

本篇新增的是对已发表链的选取、搬运及整数比较。通用构造和组合计数的
证明分别见上面的本地链接。有限检查没有替代这些全称归纳。

本轮重新运行：

- `three_row_certificate.py`：17 个派生应用项、两层和三层的初始化均通过。
- `diagonal_forest_compiler.py`：1,608 条完整森林轨迹、14,070 步，另有 180 项原 BM4 交叉核验。
- `ancestor_cover_growth.py`：559 次覆盖模拟、130 次行宽变换，22 条路径触及准备上限，仍记为未完成。
- `fgh_hardy_compiler.py`：5,600 个局部恒等式；88 次数值相等、74 次超出资源预算，后者不计作通过。

这些脚本中保留的 `...proved: false` 字段表示该脚本本身不证明最终全称定理，
不是把有限测试升格为形式化。没有计算巨大的完整下降，没有修改记号定义或推送仓库。
