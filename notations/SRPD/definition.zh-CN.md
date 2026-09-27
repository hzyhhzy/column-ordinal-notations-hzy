# SRPD：父列表记号 · [English](definition.md)

整理于 2026-09-28。SRPD 是 RPD 第零层的去冗余父列表表示，旧名 RPD0。
它抽出若干已有记号的**公共初段**，不是整个 RPD 的改名，也不是一次强度增强。
[NER](SRPD.ne-rewritten.js)与[Python](srpd.py)沿用 2026-09-26 的隐含根版本，数学规则未改。

## 1. 表达式和标准域

公共根 $C_0=[]$ 不写出。一个式子是有限列串 $G=(C_1,\ldots,C_N)$。
第 $j$ 列是空列，或一个长度为 $h$ 的非增自然数列表，满足

$$j>p_0\ge\cdots\ge p_{h-1}\ge h-1.$$

每个数都是此前列的地址。无可见列是零，一个空列是一。固定起点为

$$S=([0]),$$

其计数显示为 `2`。**标准域仅包含 S 及其有限次基本列后代。**
解析器只验证上述原始语法，不能把任意手写合法图自动认证为标准项。
讨论“SRPD 的极限序型”时，取 S 的严格后代域，不把 S 本身算进去；包含它时多一个最大元。
NER 中的 `Limit` 是 S 的输入别名，不是另加一种特殊顶端。

## 2. 唯一的展开规则

指标 $n$ 为非负整数。零仍为零；$n=0$ 或末列为空时删去末列。
否则，依次进行 n 次以下反射，最后删去临时末列。

设当前可见列数为 N，末列 C 长 h，末数为 c，跨度 $d=N-c$。

1. 保存第 $c+1,\ldots,N$ 列的移动副本，移动规则见下。
2. 把当前末列改成 `C[:-1] + C_c[h-1:]`。
3. 把保存的副本追加到右侧。

移动一个来源列 A：先把每个 $p\ge c$ 改成 $p+d$，得到 B；若 B 有零基第 c 项，
则在该项前插入 d 个相同的 `B[c]`；否则不插入。
读取父0时直接取公共空根，父号不需要重编号。

```python
def expand(graph, n):
    if not graph or not n or not graph[-1]:
        return graph[:-1]
    result = graph.copy()
    for _ in range(n):
        column = result[-1]
        parent = column[-1]
        span = len(result) - parent
        source = result[parent - 1] if parent else []

        def move(column):
            moved = [p + span if p >= parent else p for p in column]
            return moved[:parent] + moved[parent:parent + 1] * span + moved[parent:]

        copies = [move(column) for column in result[parent:]]
        result[-1] = column[:-1] + source[len(column) - 1:]
        result.extend(copies)
    return result[:-1]
```

完整 Python 文件另检查指标非负。这里没有调用 RPD、e0MN 或 TBMS 引擎。
保留临时末列会改错规则。每次反射只改当前末列并在右边追加，故
$G[0]$ 为删末列，$G[n]$ 总是 $G[n+1]$ 的完整列前缀。

| n | S[n] | 计数序列 |
| --- | --- | --- |
| 0 | `0` | `0` |
| 1 | `[]` | `1` |
| 2 | `[][1]` | `1,2` |
| 3 | `[][1][2,2]` | `1,2,4` |
| 4 | `[][1][2,2][3,3,3]` | `1,2,4,8` |

复制补层的条件是**来源列的长度大于控制父号 c**，不是末列恰为 `[1]`。
例如标准项 `[][1][2,2][3,3,3][2]` 的 `[1]` 为
`[][1][2,2][3,3,3][1][5,5][6,6,6,6,6,6]`。
末列 `[2]` 也会触发补层，见[带标准路径的例子](fixtures/completion-counterexample.json)。
不能只搬父号而删掉插层；这样会改变标准项的基本列，连逐列的无限展开极限也会改变。

## 3. 顺序、局部降低及计数

比较逐列进行，列内使用自然数列表的通常字典序，真前缀较小。
所有显示模式最终使用同一个父列表比较器。
前缀性质和末列修改约束要结合标准可达性及严格下降使用，不能单凭原始语法便宣布全部图良序。

固定此前各列，局部降低就是

$$C\longmapsto C[:h-1]\mathbin{\frown}C_c[h-1:].$$

它由一次真实 `[1]` 后删去新增列实现。某列的计数，是反复这样局部降低直到空列，
再删除空列所需的次数；它不是实际整条基本列倒数的长度，也不是该列的行数。

可用动态规划精确计算。公共根 $T_0(t)=0$；超出第 j 列长度时 $T_j(t)=0$，否则

$$T_j(t)=T_j(t+1)+1+T_{C_j[t]}(t),\qquad \operatorname{count}(C_j)=T_j(0)+1.$$

引用只指向早列，故逐列、列内倒序求值即可，不运行大数次下降。
Python 使用任意精度整数，JS 用 BigInt。列数组本身仍可能很大：
这个表示简化规则，但未必比稀疏的 `(父,最高根)` 对省空间。

## 4. 三种 NER 显示

默认“列表”是实际父列表；“等价表示”另有两项，未重复注册“列表”。

* **计数序列：**每列一个精确局部计数；预算耗尽后保留算出的前缀，未知位置显示 `?`。
* **层级列表：**BMS 式节点高度 $H_j(r)=1+H_{C_j[r]}(r)$，缺格高度为0。

例如父列表 `[][1][2,2][3,3,3]` 的高度显示为 `[][1][2,1][3,2,1]`。
高度是同层父链长度，不是父号、根编号或计数；使用这种显示不意味着改用 BMS 展开规则。
高层恢复父项时须沿低一层父链找更低高度，不能随意逐行向左取最近较小数。
[标准反例](fixtures/height-naive-counterexample.json)记录了后一种恢复办法失败的路径。

高度视图对所有手写合法图并不单射，例如 `[][1][1][2]` 与 `[][1][1][3]`。
程序显示前必须恢复父图并核对，失败就报错；反向解析也检查重新计算的高度。
因此成功显示时是无损的。**尚未一般证明此视图覆盖全部标准项**，有界往返测试不替代该定理。

## 5. 公共初段及良序性

记 $\alpha_{\rm SRPD}$ 为 S 严格后代域的序型。
按已收录纸面对应文稿的约定，处理好有限底部与端点后，

$$\alpha_{\rm SRPD}
=|\mathrm{RPD}(1,2)|
=|\mathrm{ARD}(1,1,3)|
=|\mathrm{ARD2}(1,1,3)|
=|\mathrm{IPD}(1,2)|
=|\mathrm{e0MN}(1,3)|.$$

此处 e0MN 是 @test_alpha0 的普通版。指定的新 strong 版另对应 `1,2`。
这些是各自端点**严格以下**的公共初段，不是整个 RPD／ARD／ARD2／IPD 的序型。
LRD、Ω-LRD3 不能仅凭规则相似就自动加入这个等号链。

[对应与良序转移说明](correspondence.zh-CN.md)给出坐标投影，并链接既有比较稿。
特别地，RPD 的首空列被改成公共隐含根，计数删首 `1`；旧零和旧一同时投影到新零。
要声称序同构，须对最低有限段重新编号，不能把该原始投影称为处处单射。
普通 M13 的严格后代与 SRPD 严格后代直接同图、同指标展开；端点满足

$$S[n+1]=\mathrm{M13}[n],\qquad S[0]=0.$$

SRPD 标准域良序由 RPD 标准低段的纸面同构继承，可沿用仓库的
$KP_\omega+\text{存在不可数序数}$（保留完整集合归纳）纸面上界。
**SRPD 的投影、公共初段比较和 TBMS 比较尚无独立 Lean 定理**；原 RPD 的 Lean 证明没有自动认证这份 JS。

## 6. 使用、版本与核验

把 [JS](SRPD.ne-rewritten.js) 的完整内容导入
[ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/) 的自定义记号，选 SRPD。
输入 `Limit`、`SRPD[4][1]`、完整父列表或自然数；自然数表示相应数量的空列。
不要把计数串当成未经实现的反向解析格式。旧 `RPD0` 路径别名仍保留。
旧显式根数据需要删掉首个 `[]`；新注册 ID 为 `srpd-implicit-root-v02`，避免缓存混淆。

```sh
python -B notations/SRPD/srpd.py 4 1
node --max-old-space-size=512 tests/srpd.cjs
node --max-old-space-size=512 tests/srpd.cjs --python-cases | python -B tests/srpd_python.py
```

JS 的一秒工作预算、8192列及100万表项等保护是软件限制，不是数学定义。
Python 核心没有展开规模限制，批量调用须另设预算。
[来源清单](provenance.json)固定两个实现及例子；[发布核验](../../tools/srpd-validation.json)
区分完成、跳过和未遍历分支，不宣称无限制算法验证或新做过浏览器点击验收。
[SRPD 与 TBMS 的研究汇总](../../research/srpd-tbms/README.zh-CN.md)另列最新承载界与未决猜想。
