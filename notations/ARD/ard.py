"""ARD（Anchored Row Diagrams）的独立定义版；Python 3.10+，仅依赖标准库。

每列由三元组 (行锚, 父列, 最大根) 组成，列号从 0 开始。
最大根 q 表示包含全部根 0,...,q；同锚同父只保存最大的 q。
行锚是此前某列的地址，复制时与父、根、子坐标一起移动。

AnchoredRows() 是零，TOP 是外顶端；a[n] 等同于 a.fs(n)。
标准域为种子的有限展开后代及顶端；构造器只检查结构合法性。
普通 Lean 良序证明已完成；弱体系内推导仅有纸面证明，未证明强于旧记号。

不含解析、计数、绘图、缓存或资源保护。整数任意精度；
大指标可能产生巨量列，请不要用本定义版作无界展开搜索。
"""

from dataclasses import dataclass
from functools import total_ordering


Edge = tuple[int, int, int]  # (anchor, parent, maximum_root)
Column = tuple[Edge, ...]


def _natural(value: int) -> None:
    if type(value) is not int or value < 0:
        raise ValueError("需要非负整数（不接受 bool）")


def _column_key(edge: Edge) -> tuple[int, int, int]:
    anchor, parent, maximum_root = edge
    return parent, anchor, maximum_root


@total_ordering
@dataclass(frozen=True)
class AnchoredRows:
    # None 表示顶端；() 表示零；((),) 表示一个空列，即 1。
    columns: tuple[Column, ...] | None = ()

    def __post_init__(self) -> None:
        """验证坐标、合并重复组并排序；也接受列表形式的构造输入。"""
        if self.columns is None:
            return

        normalized = []
        for child, column in enumerate(self.columns):
            groups = {}
            for anchor, parent, maximum_root in column:
                for value in (anchor, parent, maximum_root):
                    _natural(value)
                if not (anchor < child and maximum_root <= parent < child):
                    raise ValueError(
                        f"第 {child} 列须满足 0≤行锚<子列、0≤最大根≤父列<子列"
                    )
                key = anchor, parent
                groups[key] = max(maximum_root, groups.get(key, -1))

            edges = [(anchor, parent, root) for (anchor, parent), root in groups.items()]
            normalized.append(tuple(sorted(edges, key=_column_key, reverse=True)))

        object.__setattr__(self, "columns", tuple(normalized))

    @classmethod
    def finite(cls, n: int) -> "AnchoredRows":
        """自然数 n：恰有 n 个空列。"""
        _natural(n)
        return cls(tuple(() for _ in range(n)))

    @classmethod
    def seed(cls, n: int) -> "AnchoredRows":
        """A₀=0，A₁=[]；此后每次追加 [(n−1,n−1,n−1)]。"""
        _natural(n)
        columns = []
        for child in range(n):
            if child == 0:
                columns.append(())
            else:
                previous = child - 1
                columns.append(((previous, previous, previous),))
        return cls(tuple(columns))

    @property
    def kind(self) -> str:
        if self.columns is None:
            return "limit"
        if not self.columns:
            return "zero"
        return "limit" if self.columns[-1] else "successor"

    def _order_key(self) -> tuple:
        if self.columns is None:
            return (1, ())
        return (0, tuple(
            tuple(_column_key(edge) for edge in column)
            for column in self.columns
        ))

    def __lt__(self, other: "AnchoredRows") -> bool:
        if not isinstance(other, AnchoredRows):
            return NotImplemented
        # 从左到右逐列比较；列内按父、行锚、根比较；真前缀较小。
        return self._order_key() < other._order_key()

    def fs(self, n: int) -> "AnchoredRows":
        """基本列第 n 项。有限非零式的第零项删末列。"""
        _natural(n)
        if self.columns is None:
            return self.seed(n)
        if not self.columns:
            return self
        if n == 0 or not self.columns[-1]:
            return AnchoredRows(self.columns[:-1])

        last = len(self.columns) - 1
        # 控制优先级是行锚、根、父，与列内排序不同。
        control_anchor, cut, control_root = max(
            self.columns[-1], key=lambda edge: (edge[0], edge[2], edge[1])
        )
        block_width = last - cut
        result = [[] for _ in range(last + n * block_width)]

        # 切点以前的列及其全部引用均固定，不必重复复制。
        for child in range(cut):
            result[child].extend(self.columns[child])

        for block in range(n + 1):
            def move(index: int) -> int:
                if index < cut:
                    return index
                return index + block * block_width

            # 复制来源块；特别注意行锚也要 move。
            for child in range(cut, last):
                for anchor, parent, maximum_root in self.columns[child]:
                    result[move(child)].append(
                        (move(anchor), move(parent), move(maximum_root))
                    )

            if block == n:
                break  # 最后一份来源块后面不再添加接缝。

            seam = result[last + block * block_width]
            for anchor, parent, maximum_root in self.columns[-1]:
                if anchor < control_anchor:
                    new_root = move(maximum_root)
                elif anchor == control_anchor:
                    new_root = min(move(maximum_root), move(control_root) - 1)
                else:
                    continue
                if new_root >= 0:
                    seam.append((move(anchor), move(parent), new_root))

            # 新包：全部较早行锚，父和最大根均为本块切点。
            moved_cut = move(cut)
            for anchor in range(move(control_anchor)):
                seam.append((anchor, moved_cut, moved_cut))

        return AnchoredRows(tuple(tuple(column) for column in result))

    __getitem__ = fs

    def __str__(self) -> str:
        if self.columns is None:
            return "Limit of ARD"
        if not self.columns:
            return "∅"
        return "".join(
            "[" + ",".join(f"({anchor},{parent},{root})" for anchor, parent, root in column) + "]"
            for column in self.columns
        )


ZERO = AnchoredRows()
TOP = AnchoredRows(None)
