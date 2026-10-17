# 自然截断、标记传送及本目录实际调用的局部引理

本页索引第三组和父包初始化所需的局部证明，避免把一个未打包的私有 PDF 或“已有闭包”当作黑箱。

## 1. 证书

每行 core 为严格递增整数列，隐含最后点是物理下一列；步长边和最小条目临界点由同一 $\operatorname{Iter}(j)$ 的 owner 实现。mark proper，实际 $p$-trace 精确命中配对源。

若非终点词是 $W=F_{v_0}\circ\cdots\circ F_{v_{d-1}}$，定义

$$
\Delta(W)=(F_{v_0}\circ\cdots\circ F_{v_{d-2}})(\theta_{v_{d-1}+1}).
$$

要求 carrier $F_r\equiv_{\Delta(W)}W$，其中 $\equiv$ 是 membership 截断。自然界满足

$$
\theta_{v_0}<\Delta(W)\le\theta_{v_0+1},\qquad
\Delta(P\circ W)=P(\Delta(W)).
$$

对应[自然截断引理](../proofs/natural-mark-lemmas/natural_trace_cutoff_semantics.md)第 1 节给出逐因子证明，之后逐项验证 full、low、high 的复制分支与正确 paper guard。

## 2. 从语法到实际复制词

[复制词识别](../proofs/natural-mark-lemmas/copy_trace_word_identification.md)逐步追踪实际 $p$ 链，分别识别全因子复制、low 旧尾词和 mixed 高分支；不预设待证的 mark 语义。

据此才能用 application 输送旧自然截断。不得把最终词凭形式相似就猜成某个复合，也不能把 legacy 的混合筛选偷换为 paper guard。

## 3. Sat 与扫描内部的包传送

ordinary eligible 行的 Sat 条件是 $B(e(v))\le p(v)$。对实际读取非空记录的内部因子 $v\to w$，所需入口条件是

$$
p(v)=w,\qquad B(e(v))\le w.
$$

[Sat 包定理](../proofs/natural-mark-lemmas/sat_endpoint_packet_theorem.md)先证明宽度单调，再证明内部连接为空或完整，随后对整个冻结扫描归纳。它比强制内部相邻更一般，也不允许完全丢掉内部包条件。

[自然截断语义](../proofs/natural-mark-lemmas/natural_trace_cutoff_semantics.md)后半部在实际整包传送的基础上证明补全读值、新行边和新 mark 语义；两篇互相承担不同接口，不能单独用其中一篇代替另一篇。

其余有限扫描接口包括：

- [标记补全区间](../proofs/natural-mark-lemmas/marked_completion_interval_lemma.md)；
- [多 mark 补全交换](../proofs/natural-mark-lemmas/multiple_mark_completion_commutation.md)；
- [复制后扫描与 mark 修补](../proofs/natural-mark-lemmas/copy_scan_mark_repair.md)；
- [ordinary 域及 Sat 的操作保持](../proofs/natural-mark-lemmas/marked_blp_order_domain.md)，尤其第 9 节；
- [辅助 E 的自然界与后继新块抽取](../proofs/natural-mark-lemmas/marked_E_transfer_work.md)第 2、3、7 节。

## 4. 只需要有限参数的地方

[有限参数定量桥](../proofs/output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md)把上述局部引理合成为当前有限 $m$-linedness 的增长计算。后继新块抽取保留全部因子及自然界，允许换成前半块产生的实际新参数；不假设原三元组有任意大参数的共同见证。

父包版另见[父包选择器](../proofs/output/iblp-030-laver-20261014/parent-packet-propagation-selector.zh-CN.md)与[父包有限参数桥](../proofs/output/iblp-030-laver-20261014/parent-packet-quantitative-transfer.zh-CN.md)。它们用直接父行的新 family 保证包传送，不能替代原版 ordinary 扫描而不说明规则已变。

## 5. 本目录不调用的更强结论

随附历史合成稿中还有借助 I2 和“同一端点全部有限 linedness”证明整个标准域良序的论证。本目录只取它明确证明的局部行边、扫描和 Sat 接口。三个主定理均沿用 ZFC + I3 的有限实际证书，不把那条 I2 全局定理作为隐藏前提。

第三组的因子后继闭合抽取及有限表势函数在其[主文](../03-iblp-modify.zh-CN.md)中重新完整给出。语义闭包证明和整数计数证明是两个独立义务；良序性本身不会自动提供 modify 次数界。
