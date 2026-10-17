# 共享 012 端口给出更大的 q(5) 初始化

> 整理阅读版 / Collected reading edition. 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-14。本篇在既有 ZFC + I3、同一个 `Iter(j)` 的实际证书和
父包有限参数定量桥下，严格提高 `G(1)=f_PP(S,1)` 的纯整数下界。
它没有把某个完整的超 BMS 序数记号编译进 pIBLP，也没有把 pIBLP
全指标序型直接当作有限参数增长递归。

设 `F=P4=S[0]^5`，`P5=S[0]^4`，并记

$$
H(m)=f_{\rm PP}(F,m),\qquad C=H(1),\qquad B=H(C).
$$

已有 [纯 E 归约](<../piblp-external-FGH-20261014/P4-pure-E-collapse.zh-CN.md>)
把 `H` 准确写成 `u_(ω^ω)`。本篇只需 `H(1)=C` 及所有被实际使用的
调用满足 `H(m)≥m2^m`，不需要其全域输入单调性。

新结论为

$$
\boxed{G(1)\ge H^{\circ(2^B+2)}(1).}
\tag{1}
$$

旧初始化只使用 `G(1)≥H²(1)=B`。式 (1) 沿同一条严格增长的 `H`
轨道，使用指数级于 `B` 的迭代次数，因而是严格提高。

## 1 一条正确的有限参数入口，不只是 NER 可达路径

沿用升序 core、冒号后步长的简写：

```text
F  = 01:1 012:1 0123:2 012*34:2
P5 = F 01235:3
```

这里第四行的 mark 是地址 3，星号仅记 mark，不是额外 core 元素。
在参数 1 上，`P5` 是 E-limit，故 `f(P5,1)=f(E_P5(1),1)`。
一次真实辅助 E 及一次普通短 M 的完整结果是

```text
E_P5(1)   = F 0125:2 012*56:2
M(E_P5(1))= F 0125:2 256:1 2567:2 256*78:2 .
```

这两处末行都是 transient（不是 E-successor 或 E-limit），首次完整复制
guard 全部通过。后一项有前缀

```text
T = F 0125:2 256:1 .
```

对 T 作一次 M，结果及其前缀 V 为

```text
M(T) = F 0125:2 01256:3 0125*67:3
V    = F 0125:2 01256:3 .
```

T 的 guard 通过，且末行 transient，所以 `f(T,1)=f(M(T),1)`。
V 则是 E-limit，根地址是 5，其辅助 E(1) 只复制尾部的第 5 行，得

```text
E_V(1) = F 0125:2 0126:2 .
```

这一步不扫描父包；F 的行和 mark 全部不动。V 正是共享 0、1、2
的 active graft `F⋉p_ω`，但上面这些有限数组已足以证明后文的函数等式，
不必假设一般 active graft 的全指标模拟。

## 2 实际语义、定义性和 cap

P5 是 S 的实际前缀，保留相同的首三点和初始 1-linedness。
父包定量桥供应 E 与 M 的真实实现及全部自然截断 mark 证书；其 cap
不高于 S 的 `θ6<κ4`。T、V 的前缀实现也继承同一个首三点。

上述路径使用的两次 M 确实是 f 递归的 transient 分支，而不是擅自用
NER `[2]` 替换某个 E 分支。每次取前缀只使用既已证明的
“同一实际实现内，固定参数下的前缀数值不减”引理。由此

$$
\begin{aligned}
G(1)&\ge f(P5,1)=f(E_{P5}(1),1)\\
&=f(M(E_{P5}(1)),1)\ge f(T,1)\\
&=f(M(T),1)\ge f(V,1).
\end{aligned}
\tag{2}
$$

所有这些调用及随后 E-successor 产生的大参数调用的定义性，都由同一有限
表势归纳和双块定量桥一并给出。没有假定固定原三元组能支持任意大的参数，
也没有先假设 G 全域终止。

## 3 两条 E-successor 正好生成巨大次数的 H 迭代

令 R=F 后接一条全局 `012n:2` 的 E-successor 行，并记

$$
K(m)=f(R,m)=H^{\circ 2^m}(m).
\tag{3}
$$

V 的一次辅助 E(1) 正好得到 F 后接两条这种 E-successor 行，故

$$
f(V,1)=K^{\circ2}(1)=K(B)
=H^{\circ2^B}(B)=H^{\circ(2^B+2)}(1).
\tag{4}
$$

这里 `K(1)=H²(1)=B`，每个等式是原递归定义的精确等式。
结合 (2) 即得 (1)。特别地不需从“更大的序型”推断“更多计算”。

## 4 接回现有 BMS 反馈

设

$$
J=H^{\circ(2^B+1)}(1),\qquad
\rho(x)=x+3+\lceil\log_2(x+2)\rceil .
$$

由 (1) 和通用下界 `H(J)≥J2^J`，新的实际高度
`h*=G(1)+2` 满足

$$
h_*\ge J2^J+2\ge\rho(2^J),
\tag{5}
$$

最后一步只用 `J≥3`：`ρ(2^J)=2^J+J+4≤J2^J+2`。
与 [既有增强下界](<../piblp-q5-enhancement-20261014/q5-piblp-enhanced-bound.zh-CN.md>)
第 3—5 节完全相同的实际前端插入、端点模板与 FGH 缓冲编译给出

$$
\boxed{q(5)>F_{\Lambda+\omega}
 \bigl(F_\Lambda(F_\Lambda(2^J))\bigr),\quad
\Lambda=\lim(\mathrm{BMS}).}
\tag{6}
$$

仍约定 `(Λ+ω)[x]=Λ+(x+1)`。
这个右端严格超过原先 `2^C` 输入的右端：沿同一 H 轨道有 `J>C`，
再用已经单独证明的 BMS 对角输入严格单调性即可，不依赖一般 FGH
下标单调性。若需要更简洁但较弱的表达，可改用

$$
J_0=H^{\circ C}(1)
$$

代替 J；因为 `2^B+1≥C`，沿同一个 H 轨道有 `J≥J0`。

这一推进增强了实际数值初始化，但主干 FGH 下标仍是 `Λ+ω`。
它本身不能回答“把 Y、RPD 或另一完整的超 BMS 系统送进 pIBLP”的问题。

## 5 有限数组证书

active-port-initialization-audit.py（历史参考：`active-port-initialization-audit.py`）
逐步核对上述 E、M、T、V 的完整 core、步长和 marks，并检查各 guard。
明确上限是两秒、30 行和 1000 个存储项；实际 9 行、46 个存储项，
单轮不足 0.1 秒退出。它不计算任何巨大迭代的十进制值，也没有后台进程。

NER 的一般 `[1]` 是 first-item、`[2]` 是短 M，但在 P4 这个特定项上
两者完整数组恰好相同，证书也断言了这件事。因此旧稿的 A 名称在这里
没有导致实际不同的项。本文直接写出 T、V 的全部形貌。

## 6 再两步的宏将纯 E 控制提高到 omega 的 omega 次方

还可不在 M(T) 的前缀 V 处停下，而对 M(T) 再作一次 transient M，
所得项的七行前缀是

```text
Q = F 0125:2 01256:3 567:1 .
```

Q 的 guard 通过，末行也是 transient，一次短 M 正好给

```text
Z = M(Q) = F 0125:2 01256:3 01267:3 = F⋉p_(ω^ω) .
```

因此结合前缀数值比较有 `G(1)≥f(Z,1)`。对任意基函数 H，沿用
[共享端口的函数代入定理](<../piblp-external-FGH-20261014/active-E-graft-functional-substitution.zh-CN.md>)
的递归

$$
U_0^H=H,\qquad U_{\alpha+1}^H(m)=(U_\alpha^H)^{\circ2^m}(m),\qquad
U_\lambda^H(m)=U_{\lambda[2^m]}^H(m),
$$

得到更强的准确界

$$
\boxed{G(1)\ge U_{\omega^\omega}^H(1).}
\tag{7}
$$

H 本身已经是 `u_(ω^ω)`，故准确地说右端是 `u_(ω^ω·2)(1)`：
对于本处固定 β=ω^ω、α≤ω^ω，`u_(β+α)=U_α^(u_β)` 可按 α 归纳，
因为所用基本列恰满足 `(β+α)[n]=β+α[n]`，后继也相容。
这里的 `ω^ω·2` 仍只是有限参数递归的控制下标，不是整个 pIBLP 的序型。

为了把 (7) 送回带缓冲的 BMS 初始化，令

$$
\widehat J=U_{\omega+1}^H(1).
$$

在参数 1 处，三次极限降阶依次为
`ω^ω→ω²→ω·2→ω+2`，因此

$$
U_{\omega^\omega}^H(1)
=U_{\omega+2}^H(1)
=(U_{\omega+1}^H)^{\circ2}(1)
=U_{\omega+1}^H(\widehat J)\ge H(\widehat J)
\ge\widehat J2^{\widehat J}.
\tag{8}
$$

其中 `U_α^H(m)≥H(m)` 可直接按 α 归纳：后继迭代的第一轮已满足该界，
后续轮次只需 `U_α^H(x)≥x`，不需 H 对输入单调。极限向下继承。
本次所有调用也可直接由实际 Z 的定量桥保证定义性。

所以前面的 J 可以再提高为 `Ĵ`，并有

$$
\boxed{q(5)>F_{\Lambda+\omega}
 \bigl(F_\Lambda(F_\Lambda(2^{\widehat J}))\bigr).}
\tag{9}
$$

这严格增强 (6)：`Ĵ=(U_ω^H)²(1)>U_ω^H(1)>J`，都是同一增值轨道上的
有限比较，接着使用已证 BMS 输入单调性。若与
[动态深度模板](<dynamic-depth-Lambda-omega-successor.zh-CN.md>)结合，则同样可用
`x=2^Ĵ`，得到

$$
q(5)>F_{\Lambda+\omega+1}
 \!\left(F_{\Lambda+\omega}(F_\Lambda(F_\Lambda(2^{\widehat J})))\right).
\tag{10}
$$

所有新数组均已加入同一有界证书。式 (7)—(10) 的严格比较来自上述递归
等式和实际实现，不是仅从有限样例推断的全称嵌入。
