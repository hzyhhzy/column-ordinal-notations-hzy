# 父包补全的有限参数增长函数与周期三十二

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。在同一个 I3 生成元的代数中，父包补全不仅具有固定 `[2]`
的删行计数界，也可接入普通 BLP 的有限参数 linedness 递归。对已有九行实际种子
$S$，下面证明一个新的、明确定义的计算值满足
$$
\boxed{q(5)>2^{f_{\rm PP}(S,1)}.}\tag{1}
$$
这是数值接口的扩展，不是 $f_{\rm PP}$ 已被证明强于 BMS 的结论。
特别是 $f_{\rm PP}$ 与全指标父包记号的 FGH、固定 `[2]` 次数并不按定义相同。

## 1. 递归所用的有限操作

沿用 [父包规则](<parent-packet-short-tail-definition.zh-CN.md>) 的普通行、
准确 marks 和正确一基 paper copy guard。这里保留固定首两行，零项为
$(01):1,(012):1$，不是完全空数组。

令 $M_{\rm PP}$ 是一次 raw 短复制，再从旧末行位置开始执行一次父包扫描。
先检验首次完整复制的地址域；失败的项在下面递归中走 cut，不调用 $M_{\rm PP}$。
因而它在这些非退化输入上恰是全指标候选的 `[2]`。

使用普通 BLP 的**辅助类型**：末 core 为 $(0,1,2,n):2$ 时称 E-successor；
末 core 为 $(0,1,2,a,n):3$、$2<a<n$ 时称 E-limit。其他非零项称 transient。
这些是下面数值递归的分支名，不与全指标候选自己的后继判定混同。

对上述两种 E 类型，设 $a=2$ 或相应的 $a>2$，定义：

- $E_P(0)=\operatorname{cut}P$；
- 若 $E_P(t)$ 有 $d$ 行，在它后面添加辅助 core $(a,d+1):1$，再作一次 raw 短复制，得到 $E_P(t+1)$。

辅助复制的坐标映射为
$$
\psi_a(x)=\begin{cases}x,&x<a,\\x+d+1-a,&x\ge a.\end{cases}\tag{2}
$$
它处处有定义，不作 native 或 mark 扫描。指定 $m$ 后恰好执行 $m$ 次这种复制。
这没有向基本列定义加入“运行到出现某种类型为止”的隐藏循环。

## 2. 证书类与操作保持

用 $\mathcal C_m$ 表示以下实际有限实现：

1. 普通行边由同一 $\operatorname{Iter}(j)$ 中的 owners 实现，首两行固定；
2. ActiveSat、proper marks、准确 traces 和正的标记源均成立；
3. 每枚 mark 具有末因子后继所定义的自然 membership 截断证书；
4. 首三点 $(\theta_0,\theta_1,\theta_2)$ 有一份有限 $m\ge1$ 的同端点 linedness 见证。

对普通步长一的 eligible 行，Sat 自动成立；其他步长一行是 inactive 长行。
故这里 ActiveSat 与原普通证明使用的 Sat 一致。

cut 与取前缀保持证书。由
[任意真实输入的父包传送定理](<parent-packet-propagation-selector.zh-CN.md>)，
$M_{\rm PP}$ 保持普通行、自然截断、准确 traces 及 Sat，保留总 cap 和末 owner
在 raw 短复制后的值。新 mark 的源来自旧正源或非空 native 的 $p\ge1$，故仍为正。

E 的实现不需要改变。其辅助复制具有合法 paper copy 证书；自然截断的一般
full、low、high 闭包覆盖它，包括 limit 的非邻接 trace。
Sat 也由 (2) 直接保持：若被复制行原来满足
$\delta(e)\le p$，对应新不等式为
$\delta'(\psi_a(e))\le\psi_a(p)$。当 $e<a$ 时它读取未动前缀；
当 $e\ge a$ 时则是旧行的单调重编号。
新旧 blocks 之间不存在另外的待扫描事件。

这里引用的是自然截断闭包，不是已知有反例的“所有 mark 固定使用目标后继整界”语义。
E 的同 cap 实现和有限 linedness 参数来自
[原有限参数定量桥](<../iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md>)。
该构造只依赖 E 输入类型的三条点像，不依赖 M 选择哪个 native 包。

因此 $\mathcal C_m$ 中允许的 cut、$M_{\rm PP}$、$E_P(m)$ 都有真实实现；
改变 native 选择器没有损坏 E 的输入接口。

## 3. 定义增长计算

令 $g_0(m)=m2^m$。先把下式视为部分递归，不预设全域终止：
$$
f_{\rm PP}(P,m)=
\begin{cases}
g_0(m),&P\text{ 是固定两行零项},\\
f_{\rm PP}(\operatorname{cut}P,m),&\text{首次完整复制地址域失败},\\
\bigl(x\mapsto f_{\rm PP}(\operatorname{cut}P,x)\bigr)^{\circ2^m}(m),
&P\text{ 是 E-successor},\\
f_{\rm PP}(E_P(m),m),&P\text{ 是 E-limit},\\
f_{\rm PP}(M_{\rm PP}(P),m),&P\text{ 是其余非零项}.
\end{cases}\tag{3}
$$
分支优先级如式中顺序，零项优先。每个非递归结构操作有明确有限范围；
整个递归可能极长，这正是要比较的计算，不能将它隐藏在一次基本列展开中。

这项完整复制检查不会意外截断 E 两类：它们都有 $p=1$、最小地址 0，
映射把 0 送到 2 或 $a$，把所有 $x\ge1$ 送到 $x+n-1$，
所以在全部非负地址上有定义。双块递归确实使用 (3) 的 E-successor 分支。

## 4. 同 cap 的有限表势

设一个至少两行的实现（包括固定两行零项）的 cap 为 $\Theta=\gamma_r$，
末 owner 在 $2^r$ 元 Laver 表中
的代表为 $1\le b<2^r$。置
$$
\Phi(P)=2^{r+1}-b.\tag{4}
$$
这里使用真实实现的 cap 与 owner，不声称同一个语法项只有一种 $\Phi$。

cut 降低 $r$，所以严格降势；保 cap 的短复制令末 owner 变为 $J(K)$，
有限表中的 $b*_r c>b$ 给严格降势。父包扫描保留这个末 owner。
E 的自然实现经过两次 application；中间 owner 的临界点为
$J(\theta_0)=\theta_a<\Theta$，所以它仍非单位元余类，同样严格降势。
详见 [直接单步势证明](<../iblp-laver-bms-20261013/direct-step-bridge.zh-CN.md>)。

因此可对自然数 $\Phi$ 作强归纳，不必在本有限参数结论中另调用抽象 Steel
关系的良基性。I3 仍用于这些实际实现和同生成元有限商，不能据此删去公理前提。

## 5. 定量定理与双块归纳

**定理。** 若 $P\in\mathcal C_m$，则 $f_{\rm PP}(P,m)$ 有定义，而且
$$
(\theta_0,\theta_1,\Theta)
\quad\text{有}\quad f_{\rm PP}(P,m)\text{ 段 linedness。}\tag{5}
$$

对 (4) 作强归纳，同时量化所有实际实现和它们携带见证的所有有限参数 $m$，
并同时证明调用有定义与 (5)。零项用两行 linedness 引理；
地址域失败先向 cut 归纳，再延长最后一段至原 cap。E-limit 和 transient 分别
使用第 2 节的 E、$M_{\rm PP}$ 实现及严格降势。这里只使用当前有限 $m$ 的见证。

E-successor 需要处理参数会变大的递归调用。令 $Q=\operatorname{cut}P$、
$g(x)=f_{\rm PP}(Q,x)$、$Q_i=E_P(i)$，则 $Q_0=Q$，
$Q_{i+1}$ 是 $Q_i$ 在 $a=2$ 处的一次双块复制。

对 $i$ 归纳证明强化断言：任意满足第 2 节证书的 $Q_i$ 实现 $R$，
若 $\Phi(R)<\Phi(P)$，则它从当前有限参数 $R.m$ 给出
$g^{\circ2^i}(R.m)$ 段 linedness，并同时给出这些调用的定义性。

$i=0$ 是外层归纳。由 $i$ 到 $i+1$，先取旧块；其 cap 为 $\nu<R.\Theta$，
归纳给 $M=g^{\circ2^i}(R.m)$ 的同端点见证。再从新块抽取一个 $Q_i$ 实现：
它的 cap 与末 owner 和 $R$ 相同，但首三点现在具有参数 $M$ 的见证。
新块的全部 mark 因子来自地址至少为 2 的复制区；对最后因子 $t$，
$\psi_2(t+1)=\psi_2(t)+1$，所以每个自然界在抽取前后是同一个实际序数。
抽取保留完整证书，且其 $\Phi$ 恰等于 $\Phi(R)$，仍低于 $\Phi(P)$。

再次应用强化断言，得到
$$
g^{\circ2^i}(M)=g^{\circ2^{i+1}}(R.m).
$$
抽取只涉及 raw E 双块，不依赖 PP 或旧 native 如何产生了 $Q_i$。
最后对自然实现 $E_P(m)$ 使用 $i=m$，其势严格低于 $P$，即得到
E-successor 分支。所有函数调用的定义性都随这个有限归纳产生，
没有预先假设 $g$ 对任意整数都已全定义。

## 6. 九行种子的明确周期界

[九行 ordinary 种子 $S$](<same-owner-L3-sat-closure.zh-CN.md>)
具有第 2 节全部证书，初始有限参数为 1，总 cap 为
$\theta_6<\kappa_4$。它不是任意手写的语法模式。

同生成元 linedness 计数引理把 (5) 转为
$$
\theta_6\ge\gamma_{2^{f_{\rm PP}(S,1)}}.
$$
因 $\kappa_4=\gamma_{q(5)-1}$，严格单调性给出式 (1)。
同理可使用满足相同证书的前缀种子，但不声称删前缀一定保留计算的强度。

式 (1) 比单纯 $\#\mathrm{steps}<2^{q(5)}$ 提供了另一种接口：
它直接将一个递归增长值置于阶参数 $q(5)$ 以下，而不是只界住表的元素个数。
但此处并未比较 $f_{\rm PP}$ 与旧 $f_\star$，也未证明它支配内部超 BMS
记号的 FGH。额外 native 包可能改变下一次复制根，不能用“加了更多点”补上这种比较。

## 7. 与主目标的距离

本定理允许后续的结构模拟使用 E 双块和父包短 M，并由同一窗口得到严格数值界。
仍需一个复制闭合的内部端口编码，以及它到 (3) 或固定 `[2]` cut 计数的
非退化计算比较。只有这两项也完成，才能把式 (1) 称为所要求的结构性超 BMS 下界。

本稿为纸面推导；没有实际求值 $f_{\rm PP}(S,1)$，没有将有界实验当作全称证明。

**独立审计。** 第二代理逐项核对了完整复制 fallback、E 的 Sat 与自然截断、
任意实现的双块抽取、有限势归纳与参数替换，以及最后的指数方向。
审计提出的两行零项势定义域已在第 4 节补齐；未发现其余缺口。

## 8. 同一定量桥覆盖最长合法前缀版

[最长合法前缀修正](<parent-packet-partial-copy-audit.zh-CN.md>)将复制失败处理改为：
复制指定源区间内的最长合法初段，在第一个坏源行之前停止，不跳过坏行。
将其短复制加 PP 扫描记为 $M_\dagger$。若首个源行即坏，结果是 cut；
资源限额不属于这里的数学失败条件。

定义 $f_\dagger$ 时，保留 (3) 的零项、E-successor 和 E-limit 分支；
其余非零项直接取
$$
f_\dagger(P,m)=f_\dagger(M_\dagger(P),m).\tag{6}
$$
不再预先用完整复制检查把合法短复制截断。E 两类地址域本来全定义，故这项改动
不影响它们的分支归属或双块抽取。$M_\dagger$ 的零成功行情况本来就是 cut。

设成功复制源区间为 $[p,h)$，其中 $p<h\le e$。输出 cap 与末 owner 分别是
$$
\Theta'=J(\theta_h)\le J(\theta_e)=\Theta,
\qquad J(K_{h-1}).\tag{7}
$$
即使第 $h$ 行的 core 含缺域引用，地址 $h\ge p$ 自身仍在平移域中，
所以最后隐含 cap 确实存在；无需假设第 $h$ 行也有成功副本。
逐成功源行的 copy 自然证书只读取已复制前文和旧 cut 前缀。
PP 扫描随后保留 (7)，所有证书仍在第 2 节的类中。

若 $h=e$，沿用保 cap 的 application 降势。若 $h<e$，cap 严格降低，
不论末 owner 在较小商中的代表为何，(4) 都严格降低。
首源即坏时按 cut 降势。因此第 5 节的有限势归纳仍适用。

**必须补的端点步骤：** 在真正的 partial-short 情形，归纳先只给
$(\theta_0,\theta_1,\Theta')$ 的相应 linedness；此时不能说 transient 保末点。
应用原 cut 分支使用的同代数端点延长引理，将最后一段从 $\Theta'$ 延长到
$\Theta$，段数不变，才得到定理需要的原 cap 结论。
这是有限见证的延长，不是向记号的一步展开添加额外操作。

由此对同一九行种子有
$$
\boxed{q(5)>2^{f_\dagger(S,1)}.}\tag{8}
$$
第二代理独立核对了 (7)、最后因子自然界、partial 分支的端点延长，以及 E 与
双块归纳不受影响。此处分别证明两个计算的上界，没有证明
$f_\dagger\ge f_{\rm PP}$；下降关系包含本身不足以推出这样的数值单调性。
