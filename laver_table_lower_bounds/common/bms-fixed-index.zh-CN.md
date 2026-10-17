# BMS 的三列种子：固定 `[2]` 次数与 FGH 的强比较

本篇把可复用的 BMS 端证明单独列出。原 BM4 的固定 `[1]` 等于此前父表展示版的固定 `[2]`。全文采用[共同约定](conventions.zh-CN.md)中的原 BM4 指标，不用 I3、Laver 表或 BLP 的良序性。

## 1. 统一结论

令

$$
B_r=(0^r)(1^r),\quad R_h=(0^h)(1^h)(1^h),\quad
D(h)=d_1(R_h),
$$
$$
e_0=1,\quad e_{n+1}=2^{e_n},\qquad
\ell(x)=\lceil\log_2(x+2)\rceil.
$$

对整数 $r,x\ge1$，纸面证明给出

$$
\boxed{h\ge r+2+\ell(x)\quad\Longrightarrow\quad
D(h)\ge s_{R_h}(1)\ge e_{F_{B_r}(x)}.}
\tag{1}
$$

所以也有较弱而常用的 $D(h)\ge F_{B_r}(x)$。取 $r=x+1$、$g=F_\Lambda$ 和 $\rho(x)=x+3+\ell(x)$，得到

$$
h\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad
D(h)\ge e_{g(x)},\qquad T(h)=D(h)+2\ge\rho(g(x)).
\tag{2}
$$

这是指定**三列种子族**的结论。不能只凭某个任意矩阵有 $h$ 行，就把式 (1) 套上去。两列种子 $B_h$ 的固定原 $[1]$ 计算很短。

## 2. 父表域、祖先覆盖和终止接口

辅助矩阵采用规范父链深度域：父搜索能恢复给定父表，较高行的祖先也必须是较低行祖先。不是任意向左图。

覆盖是末列对齐的严格递增列映射，每条源父边映成目标同一行的非空祖先链。目标可以有额外列和行。对原 `[n]` 的同步复制，先有限次降低末列、准备控制行和切点；其余已选祖先关系保持。准备在固定前缀、固定坐标上界下严格降低末列字典序，故有限。控制项就位后，按原 BM4 父表公式逐副本检查跨接缝边。

若 $M$ 被 $N$ 覆盖且目标的固定正指标计算终止，则

$$
d_n(M)\le d_n(N),\qquad s_M(n)\le s_N(n)\qquad(n\ge1).
\tag{3}
$$

关键是固定正指标的终止轨道会经过它所需的每个列前缀：每步保留删末列前缀，宽度至多减 1。准备中出现的 `[0]` 可以按实际固定指标轨道到达该前缀；源的每次后继删除占用至少一次目标后继删除。

完整准备和接缝证明见[规范非标准矩阵的覆盖证明，第 2–5 节](../proofs/output/new-notation-20260918/BMS-nonstandard-row-bound.zh-CN.md)；固定计数及有限行宽交换见[定量祖先覆盖](../proofs/output/iblp-laver-bms-20261013/ancestor-cover-growth.zh-CN.md)。这些是本地引理，不能仅引用标准 BMS 良序定理来代替。

## 3. FGH 到 Hardy 的准确编译

令 $Z$ 为零列。变换 $W(M)$ 添加一个零首列，再将原各列的第 0 行加 1，其他行不动。由原父表公式有

$$
W(0)=Z,\quad W(MZ)[n]=W(M)^{\frown(n+1)},\quad
W(M)[n]=W(M[n])\quad(M\text{ 末列非零}).
\tag{4}
$$

上式各份为相互独立的块。因此，沿标准源 $M$ 的良基归纳，同时证明目标 Hardy 计算终止以及

$$
H_{W(M)}(x)=F_M(x).
\tag{5}
$$

后继时的 $x+1$ 份块从右到左求值，下一块接收上一块的实际输出，所以实现的是变参数迭代。[逐项证明](../proofs/output/iblp-laver-bms-20261013/fixed-index-growth-interface.md)

## 4. 一行森林将变指标计算压入固定指标

定义 $\Sigma(M)$：加一个零首列，在原矩阵下方新增连续父链 $1,2,\ldots,|M|$，原各行整体上移。置

$$
K(M,x)=s_{\Sigma(MZ^x)}(1).
$$

森林末点不是根时，目标固定 `[1]` 与森林一步逐点交换；末点为根时，目标产生一份新的原坏块，并将剩余森林搬到新块之后。每份出生块与下一份原 BM4 副本有直接父对应。跳过冻结森林列后，得到末列对齐覆盖。

长度 $x$ 的链森林给出 $e_x$ 份坏块，而 $e_x\ge2x$ 足以重新保留 $x$ 个参数列。于是

$$
K(MZ,x)=K(M,x+1),\qquad
K(M,x)\ge K(M[x],x)quad(M\text{ 末列非零}).
\tag{6}
$$

沿终止的 Hardy 轨道跟踪式 (6)，终点参数 $y=H_M(x)$ 满足

$$
K(0,y)=s_{\Sigma(Z^y)}(1)=e_y.
$$

故保留下来的强结论是

$$
K(M,x)\ge e_{H_M(x)}.
\tag{7}
$$

完整根模板、两个局部步骤及副本父号见[森林控制器证明](../proofs/output/iblp-laver-bms-20261013/diagonal-forest-hardy-proof.zh-CN.md)。不能在式 (7) 丢掉 $e_y$，然后在反馈中无依据地加回来。

## 5. 行数换宽度，支付全部尺寸

记对角矩阵

$$
\Delta_{k,m}=(0^k)(1^k)\cdots((m-1)^k).
$$

父表计算给出 $R_h[1]$ 覆盖 $\Delta_{h-1,3}$，并且

$$
s_{\Delta_{k,m}}(1)\ge s_{\Delta_{k-1,2m-2}}(1)
\quad(k\ge2,m\ge3).
$$

迭代 $t$ 次，得到 $\Delta_{h-1-t,\,2+2^t}$ 的覆盖。而

$$
P_{r,x}=\Sigma(W(B_r)Z^x)
$$

恰有 $r+1$ 行、$x+4$ 列。取 $t=\ell(x)$，条件 $h\ge r+2+\ell(x)$ 使目标行数足够，且 $2+2^t\ge x+4$。于是

$$
D(h)\ge s_{R_h}(1)\ge s_{P_{r,x}}(1)
\ge e_{H_{W(B_r)}(x)}=e_{F_{B_r}(x)},
$$

证明式 (1)。所有辅助式都由标准对角矩阵覆盖，因此终止接口最终归结为标准 BMS 良序性，没有额外假定非标准域良序。

## 6. 依赖与查阅次序

完整源证明依次为：规范父表覆盖 → 定量祖先覆盖 → 精确 $W$ 变换 → 森林控制器。另附[原 BMS 端总结](../proofs/output/iblp-laver-bms-20261013/BMS-fixed-index-to-FGH-summary.zh-CN.md)和[最小依赖审计](../proofs/output/iblp-030-laver-20261014/FGH-standalone-dependency-audit.zh-CN.md)。原总结醒目公式只写较弱界；上面的 $e_{F}$ 强界来自森林终点式 (7)。
