# pIBLP 初始长链严格超过原文献常数

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。在 [pIBLP 有限参数定量桥](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.zh-CN.md>)
的实际实现条件和 ZFC + I3 下，记

$$
G(m)=f_{\rm PP}(S,m),\qquad
H(m)=f_{\rm PP}(P_4,m),\qquad C=C_{\rm line}=H(1),
$$

其中 $S$ 是九行实际种子，$P_i$ 是其前 $i$ 行。则

$$
\boxed{G(1)\ge H(C)\ge C2^C>C.}\tag{1}
$$

这里所有被使用的部分递归调用均随实际有限势归纳而有定义；没有假设
$G,H$ 在所有参数上全定义，也没有假设它们对参数单调。

## 一次辅助复制与一个前缀

用一基显示、core 逆序的原文格式，两个前缀是

```text
P4 = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2
P5 = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,3,2,1,0)3
```

$P_5$ 的末 core 升序为 $(0,1,2,3,5)$，步长为 3，故是 E-limit。
其完整复制 guard 通过，有限参数 1 的递归分支给出

$$
f_{\rm PP}(P_5,1)=f_{\rm PP}(E_{P_5}(1),1).\tag{2}
$$

辅助规则先取 $\operatorname{cut}P_5=P_4$，加一行 $(3,5):1$，
再作一次 raw 短复制；此操作不扫描 native 或 marks。原末行步长 1，
控制点为 $a=3$，源行是第 3、4 行，地址平移为
$\psi_3(x)=x$（$x<3$）及 $x+2$（$x\ge3$）。
短复制把第 3 行变为 core $(0,1,2,5):2$，把第 4 行及其 mark
变为 $(0,1,2,*5,6):2$。所以完整结果是

```text
E_P5(1) = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,2,1,0)2(6,*5,2,1,0)2
```

它有五行字面前缀

```text
R = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,2,1,0)2
```

$R$ 的末 core 是 $(0,1,2,5)$，步长为 2，marks 为空，完整复制 guard
也通过。因此 $R$ 是 E-successor，且 $\operatorname{cut}R=P_4$。

## 严格数值增量

[同一实际 BLS 内的前缀数值单调性](<baseline-piblp-Cline-prefix.md>)
在固定当前参数 1 下分别用于 $P_5\sqsubseteq S$ 及
$R\sqsubseteq E_{P_5}(1)$，给出

$$
G(1)\ge f_{\rm PP}(P_5,1)
=f_{\rm PP}(E_{P_5}(1),1)
\ge f_{\rm PP}(R,1).
$$

E-successor 的定义恰好迭代两次，故

$$
f_{\rm PP}(R,1)
=H^{\circ2}(1)=H(H(1))=H(C).\tag{3}
$$

这个等式的两个子调用的定义性由定量桥的 E-successor 双块归纳给出。
前缀实现保留原首三点的同一当前有限参数见证，不额外要求任意参数上的
共同 linedness。既有小图案推导给出 $H(1)=C$。有限求值树的通用下界

$$
f_{\rm PP}(P,m)\ge m2^m
$$

应用于当前已定义的 $H(C)$，即得到 (1)。这是实际递归值的严格增加，
不是由序型增加推断出的下降长度增加。

## 更大的合法入口高度

$G(1)$-lined 的 $(\kappa_0,\kappa_1,\theta_6)$ 输出整体取
$E=L_3(K)$-像，得到 $G(1)$-lined 的
$(\kappa_2,\theta_6,\tau)$ 链。统一前端插入给出高度

$$
h_*=G(1)+2
$$

的合法入口 fan，封口严格小于 $\tau$。因此已有递归 corridor 端点定理和
[FGH 强缓冲编译](<audit-recursive-corridor-FGH.zh-CN.md>)可用于这个高度。
由 $C\ge3$，令 $x=2^C$，有

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil=2^C+C+4
\le C2^C+2\le h_*.
$$

所以同一编译证明直接给出另一个明确的界

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(F_\Lambda(F_\Lambda(2^C))\bigr).}\tag{4}
$$

此处仍约定 $(\Lambda+\omega)[x]=\Lambda+(x+1)$。
$2^C>F_3(256)$ 本身不能在未另证 $F_\Lambda$ 输入单调性的情况下
推出 (4) 的具体右端严格大于旧界的具体右端。所需的专门比较现已由
[BMS 对角输入单调性](<audit-BMS-diagonal-input-monotonicity.zh-CN.md>)
补齐：它使用基本列的字面前缀与两列种子的行数比较，不假定一般的 FGH
下标单调性。因此 (4) 的右端确实严格大于
$F_{\Lambda+\omega}(F_\Lambda(F_\Lambda(F_3(256))))$。
整合结论见 [pIBLP 增强下界](<q5-piblp-enhanced-bound.zh-CN.md>)。

## 有限核验

audit-P5-strict-prefix.py（历史参考：`audit-P5-strict-prefix.py`） 独立构造并逐项断言
$P_5$ 的一次 raw 辅助复制、全部 steps 和 marks、$R$ 的 E-successor
行型及 guard，以及 $\operatorname{cut}R=P_4$。预算为两秒、20 行和
500 个存储项。它不求值任何巨大递归值；全称数值推论由上面的有限势与
前缀比较论证给出。
