# DQDN · [English](README.md)

**Demand Query Diagram Notation，按需查询图列记号**，通过有限类型推导生成查询程序。这次沿用 2026-10-05 的增量生成器规则，不是 CTN，也不是刻意允许非良序部分的 CK 伪序。

## 文件与状态

| 内容 | 入口 | 状态 |
| --- | --- | --- |
| 定义 | [中文](definition.zh-CN.md)、[英文](definition.md) | 数学规则及实现边界 |
| NER | [DQDN.ne-rewritten.js](DQDN.ne-rewritten.js) | 独立单文件，四种视图 |
| Python | [standard.py](standard.py) | 检查公共标准域的入口，依赖已全部收进本目录 |
| 良序 | [纸面证明](../../proofs/paper/dqdn-well-ordering.zh-CN.md) | 尚未 Lean 认证 |
| 定位与比较 | [研究总览](../../research/dqdn/README.zh-CN.md) | 区分纸面等号、下界及未决问题 |
| 来源与复核 | [来源清单](provenance.json)、[验收记录](../../research/dqdn/validation.zh-CN.md) | 有限测试不认证序数结论 |

**没有 DQDN Lean 项目。** 旧 PD 系列的弱 KP 公理上界不自动适用于 DQDN；整个 DQDN 极限恰等于 PTO(Zω) 也没有完成证明。

## NER 使用

将 JavaScript 全文导入 [ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/) 的自定义记号，无须构建或安装 Python。使用 ID 为 `dqdn-20261005-init-v2` 的这一份，不同时启用两份同名记号。

四种视图为计数序列、完整列列表、最简操作序列、增列序列。三个基本列选项调用同一数学规则。原子整数使用 BigInt；超限报错，不返回截断式子。

默认项为 TOP、TOP[2]、TOP[1]、TOP[1][1]、1、0，列数依次为 **1、4、2、18、1、0**。880 列的 ω^ω 例子仍可按路径手动输入，但不再预置；否则在 ε₀ 下方放着它，会使 NER 首次展开 ε₀ 时超过默认的兄弟界搜索次数。

已有纸面校准的小例子：

| 值 | 输入 | 列数 |
| --- | --- | ---: |
| 0 | `TOP[0]` | 0 |
| 1 | `TOP[1][0]` | 1 |
| ω | `TOP[1][1]` | 18 |
| ω² | `TOP[1][4]` | 26 |
| ε₀ | `TOP[1]` 或 `1,2` | 2 |
| 第二层，尚无精确 PTO 定位 | `TOP[2]` 或 `1,2,1,2` | 4 |

最简路径是**每一步下标最小**，不是总步数最少。增列视图合并一次正下标展开及紧随的删除，记净增长，只用逗号、不加中括号。TOP 算一列：ε₀ 显示 `1`，ω 显示 `1,16`。零式显示 `∅`，单个增列值 `0` 则表示一列的序数 1；这是该视图专用解析器的含义。

## Python 与复现

在仓库根目录运行：

```sh
python -B notations/DQDN/standard.py "TOP[1][1]" --expand 3
python -B notations/DQDN/standard.py "TOP[2]" --list
python -B tests/dqdn.py
```

作为库使用时，将本目录放进 Python 导入路径，调用 `standard.from_path`、`expand`、`counts`、`compare`、`is_limit`、`Budget`、`ResourceLimit`。入口只解析字面 TOP 路径，不执行输入代码；直接传列图时，会先检查公共标准域。

`typed_builder.py` 才是完整的全局类型生成器。`dqdn.py` 仅是普通按需计算核，**不是完整公共记号**。`lqdn.py`、`lcdn.py`、`lambda_columns.py` 是本地辅助实现，不是另加的三个记号，也不增加合法根。其历史裸图接口可以构造不标准且非良序的图。

Python 默认预算为一秒、100,000 内部节点、20,000 输出列和一百万工作步；测试另有子进程总时间和内存保护。超限只表示该次计算未完成，不代表式子不标准或非良序。
