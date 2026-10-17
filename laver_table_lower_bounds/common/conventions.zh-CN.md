# 共同定义、指标和证明范围

本目录收集截至 2026-10-18 的三条纸面证明链。Laver 端统一在 **ZFC + I3** 中工作；BMS 计数引理本身只借用标准 BMS 良序性。这里没有新增 Lean 定理。

## 1. 周期阈值

普通二元 Laver 表 $A_m$ 有 $2^m$ 个元素，编号 $1,\ldots,2^m$，满足左自分配律和 $a*1=a+1\pmod {2^m}$。若首行最小周期为 $p_m$，定义

$$
q(n)=\min\{m:p_m\ge2^n\}.
$$

所以本目录比较的是**阶参数 $q(5)$**；对应表的元素数是 $2^{q(5)}$。I3 保证所用阈值存在。

固定同一个 $j:V_\lambda\to V_\lambda$。所有 owners、临界点、链见证和搬运都在同一 $\mathcal I=\operatorname{Iter}(j)$ 中。写

$$
j_{(1)}=j,\quad j_{(n+1)}=j_{(n)}(j),\qquad
\kappa_0=\operatorname{crit}(j),\quad\kappa_{i+1}=j(\kappa_i).
$$

以 $\gamma_0<\gamma_1<\cdots$ 枚举这个代数的临界点。所用标准接口为

$$
\kappa_4=\gamma_{q(5)-1}.
\tag{1}
$$

**Application** 写成 $F(G)$，普通函数复合写成 $F\circ G$。只在真正像点处使用

$$
F(G)(F(\xi))=F(G(\xi)),\quad
\operatorname{crit}(F(G))=F(\operatorname{crit}(G)).
\tag{2}
$$

一般不能把 $F(G)(\xi)$ 换成 $F(G(\xi))$。

## 2. 有实际见证的有限链

$L(a,b,c;m)$ 表示有严格递增的

$$
b=t_0<t_1<\cdots<t_m=c
$$

及 $U_i\in\mathcal I$，使

$$
\operatorname{crit}(U_i)=a,\quad U_i(a)=t_i,\quad U_i(t_i)=t_{i+1}.
$$

链可以整体取像、拼接或保端点缩短。若有 $L(a,b,c;m)$ 与 $L(b,c,d;n)$，逐段取像并拼接得到

$$
L(a,b,d;m2^n).
\tag{3}
$$

原来的前 $m$ 段可以逐字保留。其具体证明在[预算代数](../proofs/scratch/iblp-I-to-I0-20261016/local-budget-algebra.txt)第三节。

临界计数接口为

$$
L(\kappa_0,\kappa_1,z;m),\ z<\kappa_4
\quad\Longrightarrow\quad
\gamma_{2^m}\le z<\kappa_4,
\quad q(5)>2^m.
\tag{4}
$$

这里必须有实际链见证；单独的临界点下标下界不能反过来制造链。

## 3. BMS 指标的一位差

全目录的数学公式采用**原 BM4 指标**：

- `[0]` 删除最后一列；
- 正末列的 `[n]` 保留删尾前缀，接上 $n$ 份坏块；
- 全零末列在所有指标下都删除。

此前父表展示版的固定 `[2]`，等于这里的原 BM4 固定 `[1]`。本文令

$$
B_r=(0^r)(1^r),\qquad R_h^{\rm BMS}=(0^h)(1^h)(1^h),
$$
$$
D(h)=d_1(R_h^{\rm BMS}),\qquad T(h)=D(h)+2,
$$

其中 $d_1$ 统计到空的**全部步骤**；$s_M(1)$ 只统计零末列删除。这里的 $T$ 不是任何嵌入，也不是第三组的总运行次数。

## 4. Hardy 和 FGH

对于指定基本列的记号，零和真后继分别采用

$$
H_0(x)=x,\qquad H_{P+1}(x)=H_P(x+1),
$$
$$
F_0(x)=x+1,\qquad F_{P+1}(x)=F_P^{\circ(x+1)}(x).
$$

非零非后继统一取

$$
H_P(x)=H_{P[x]}(x),\qquad F_P(x)=F_{P[x]}(x).
\tag{5}
$$

在原版 IBLP 中，真后继指末 core 恰为 $(0,r)$、步长 1。复制失败后选择 cut，并不会使该父式自动成为真后继。

令 $\Lambda=\lim(\mathrm{BMS})$。第二组采用

$$
\Lambda[x]=B_{x+1},\qquad
(\Lambda+\omega)[x]=\Lambda+(x+1).
\tag{6}
$$

第一组的 $F,H$ 则使用固定原版 IBLP 的实际基本列。相同下降树秩不自动允许换一套基本列。

## 5. 两种 mark guard

原版 `iblp.py` 的完整展开及特殊 `[1]` 固定为[随附代码](../code/iblp_original.py)；版本哈希见[来源清单](../SOURCE_MANIFEST.json)。这里称其混合 mark 筛选为 **legacy guard**。

论文的 **paper guard** 会检查混合词的下一来源，和 legacy guard 有一个位置的差异。第三组的初值是原版完整展开产生的准确式子；之后计数的是 paper-guard 短 $M_\star$ 加完整冻结扫描及 cut。两次入口展开中两种 guard 的一致性另有证明，不能外推至全部后续轨道。

父包 $M_{\rm PP}$ 又是另一条规则：native 包加入本轮直接父行的整个新 family。第二组强化初始化用到它。三个记号和对应数值递归不可互换。

## 6. 出版范围

本目录将既有纸面论证和明确依赖整理在一起，并推导原证明内部自然输入的版本。局部脚本只核对有限语法和文件关系。它们不检验 I3 嵌入语义、全称归纳或巨大函数值。原论文列在[文献表](../BIBLIOGRAPHY.md)，不把外部标准定理伪装成本目录新证明。
