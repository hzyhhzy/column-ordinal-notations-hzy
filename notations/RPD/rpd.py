"""当前按列比较的 RPD：独立定义版，Python 3.10+，仅依赖标准库。

每列由三元组 (k, p, q) 组成：层 k、父列 p、根列 q；列号从 0 起。
第 j 列须满足 0 <= q <= p < j；构造器补齐同一 (k, p) 的所有小根。
因此 columns 中保存的是全部根关系，而不只是各组的最大根。

RPD() / ZERO 是零，TOP 是外加顶端；a[n] / a.fs(n) 是基本列第 n 项。
标准式是从 TOP 经有限次展开得到的记号。构造器只检查有限图结构，
不判定手工输入是否为标准式。同图相等，与展开历史无关。

整数使用 Python 任意精度 int；没有规模、内存或时间保护。
本文件不含解析器、绘图、计数或缓存。命令行参数为从 TOP 出发的展开指标。
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import total_ordering


Edge = tuple[int, int, int]  # (k, p, q)
Column = tuple[Edge, ...]


def _nat(n: int) -> None:
    if type(n) is not int or n < 0:
        raise ValueError("需要非负整数")


@total_ordering
@dataclass(frozen=True)
class RPD:
    # None 表示外加顶端；空元组表示零；每个内层元组表示一列。
    columns: tuple[Column, ...] | None = ()

    def __post_init__(self) -> None:
        """根向下闭包、去重、规范排序；也接受列表形式的输入。"""
        if self.columns is None:
            return
        columns = []
        for j, column in enumerate(self.columns):
            closed = set()
            for k, p, q in column:
                for value in (k, p, q):
                    _nat(value)
                if not q <= p < j:
                    raise ValueError(f"第 {j} 列的关系须满足 0 <= q <= p < j")
                closed.update((k, p, r) for r in range(q + 1))
            # 列内比较优先级是 p、k、q；大关系排在前面。
            columns.append(tuple(sorted(
                closed, key=lambda e: (e[1], e[0], e[2]), reverse=True
            )))
        object.__setattr__(self, "columns", tuple(columns))

    @classmethod
    def seed(cls, n: int) -> RPD:
        """种子 S_n：两列，第二列含层 0,...,n 的关系 (k,0,0)。"""
        _nat(n)
        return cls(((), tuple((k, 0, 0) for k in range(n + 1))))

    @property
    def kind(self) -> str:
        if self.columns is None:
            return "limit"
        if not self.columns:
            return "zero"
        return "limit" if self.columns[-1] else "successor"

    def fs(self, n: int) -> RPD:
        """基本列。有限非零项的 [0] 删末列；零的各项仍为零。"""
        _nat(n)
        if self.columns is None:
            return RPD.seed(n)
        if not self.columns:
            return self
        if n == 0 or not self.columns[-1]:
            return RPD(self.columns[:-1])

        x = len(self.columns) - 1
        # 控制边按 k、q、p 取最大，注意不同于列内比较顺序。
        K, c, r = max(self.columns[-1], key=lambda e: (e[0], e[2], e[1]))
        length = x - c
        result = [set() for _ in range(x + n * length)]

        for b in range(n + 1):
            def move(i: int) -> int:
                return i if i < c else i + b * length

            # 源图为删去原末列后的图，放入原位及 n 份平移副本。
            for j, column in enumerate(self.columns[:-1]):
                for k, p, q in column:
                    result[move(j)].add((k, move(p), move(q)))

            # 接缝只保留较低层或同层严格较小根的末列关系。
            if b < n:
                for k, p, q in self.columns[-1]:
                    for u in range(move(q) + 1):
                        if k < K or (k == K and u < move(r)):
                            result[x + b * length].add((k, move(p), u))

        # 平移可能跳过一些根号；构造器补齐根向下闭包。
        return RPD(tuple(tuple(column) for column in result))

    __getitem__ = fs

    def _order_key(self) -> tuple:
        if self.columns is None:
            return (1, ())  # 顶端大于所有有限图。
        return (0, tuple(
            tuple((p, k, q) for k, p, q in column)
            for column in self.columns
        ))

    def __lt__(self, other: RPD) -> bool:
        if not isinstance(other, RPD):
            return NotImplemented
        # 从左到右逐列、逐关系比较；各级真前缀较小。
        return self._order_key() < other._order_key()

    def __str__(self) -> str:
        if self.columns is None:
            return "Ω"
        if not self.columns:
            return "0"
        return "".join(
            "[" + ",".join(f"({k},{p},{q})" for k, p, q in column) + "]"
            for column in self.columns
        )


ZERO = RPD()
TOP = RPD(None)
OMEGA = TOP


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="RPD: expand TOP along a finite path")
    parser.add_argument("indices", nargs="*", type=int, help="successive fundamental-sequence indices")
    args = parser.parse_args()
    value = TOP
    for index in args.indices:
        value = value[index]
    print(value)
