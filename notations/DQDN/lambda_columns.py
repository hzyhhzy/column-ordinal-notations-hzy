"""Experimental lambda-DAG columns, with literal-prefix basic sequences.

This is a local rule, NOT a claim that every untyped graph is well-founded.
Only a separately specified compatible family of strongly-normalising roots
may be admitted.  Type certificates are not yet a global-root implementation.
"""

from dataclasses import dataclass, field
from math import isqrt
from time import monotonic


class ResourceLimit(RuntimeError):
    pass


@dataclass
class Budget:
    seconds: float = 1.0
    nodes: int = 100_000
    columns: int = 20_000
    operations: int = 1_000_000
    started: float = field(default_factory=monotonic)
    used: int = 0

    def tick(self):
        self.used += 1
        if self.used > self.operations:
            raise ResourceLimit("operation budget")
        if self.used % 256 == 0 and monotonic() - self.started > self.seconds:
            raise ResourceLimit("time budget")


class Terms:
    """Immutable hash-consed syntax; sharing never memoises a Q answer."""

    def __init__(self, budget):
        self.budget = budget
        self.data = []
        self.index = {}
        self.shift_cache = {}
        self.subst_cache = {}

    def make(self, tag, *args):
        self.budget.tick()
        item = (tag, *args)
        if item not in self.index:
            if len(self.data) >= self.budget.nodes:
                raise ResourceLimit("syntax DAG budget")
            self.index[item] = len(self.data)
            self.data.append(item)
        return self.index[item]

    def shift(self, root, amount, depth=0):
        target = (root, amount, depth)
        stack = [(root, depth, False)]
        while stack:
            node, level, ready = stack.pop()
            key = (node, amount, level)
            if key in self.shift_cache:
                continue
            self.budget.tick()
            tag, *args = self.data[node]
            if tag == "v":
                k = args[0]
                result = self.make("v", k + amount if k >= level else k)
            elif tag == "q":
                result = node
            elif not ready:
                stack.append((node, level, True))
                stack.extend((x, level + (tag == "l"), False) for x in reversed(args))
                continue
            else:
                result = self.make(tag, *(self.shift_cache[(x, amount, level + (tag == "l"))]
                                          for x in args))
            self.shift_cache[key] = result
        return self.shift_cache[target]

    def substitute(self, body, argument, depth=0):
        target = (body, argument, depth)
        stack = [(body, depth, False)]
        while stack:
            node, level, ready = stack.pop()
            key = (node, argument, level)
            if key in self.subst_cache:
                continue
            self.budget.tick()
            tag, *args = self.data[node]
            if tag == "v":
                k = args[0]
                result = (self.shift(argument, level) if k == level else
                          self.make("v", k - 1 if k > level else k))
            elif tag == "q":
                result = node
            elif not ready:
                stack.append((node, level, True))
                stack.extend((x, level + (tag == "l"), False) for x in reversed(args))
                continue
            else:
                result = self.make(tag, *(self.subst_cache[(x, argument, level + (tag == "l"))]
                                          for x in args))
            self.subst_cache[key] = result
        return self.subst_cache[target]

    def numeral(self, n):
        body = self.make("v", 0)
        function = self.make("v", 1)
        for _ in range(n):
            body = self.make("a", function, body)
        return self.make("l", self.make("l", body))

    def spine(self, root):
        arguments = []
        while self.data[root][0] == "a":
            self.budget.tick()
            _, function, argument = self.data[root]
            arguments.append(argument)
            root = function
        return root, arguments

    def head_step(self, root, n):
        head, arguments = self.spine(root)
        tag, *args = self.data[head]
        if tag == "l" and arguments:
            result = self.substitute(args[0], arguments.pop())
        elif tag == "q":
            result = self.numeral(n)
        else:
            return None
        while arguments:
            result = self.make("a", result, arguments.pop())
        return result

    def child(self, root, i):
        tag, *args = self.data[root]
        if tag == "v":
            raise ValueError("a variable is terminal")
        if tag == "l":
            return args[0]
        if tag == "q":
            return self.numeral(fair_index(i))
        head, _ = self.spine(root)
        has_step = self.data[head][0] in ("l", "q")
        width = 3 if has_step else 2
        position = i % width
        if position < 2:
            return args[position]
        return self.head_step(root, fair_index(i // width))


def fair_index(i):
    """0; 0,1; 0,1,2; ... . Every possible child recurs infinitely often."""
    row = (isqrt(8*i + 1) - 1) // 2
    return i - row*(row + 1)//2


def decode(columns, terms):
    roots = []
    for column in columns:
        if not isinstance(column, tuple) or not column:
            raise ValueError("each column must be a nonempty tuple")
        tag, *args = column
        if any(type(x) is not int or x < 0 for x in args):
            raise ValueError("indices must be natural numbers")
        if tag == "v" and len(args) == 1:
            root = terms.make("v", args[0])
        elif tag == "q" and not args:
            root = terms.make("q")
        elif tag in ("l", "a") and len(args) == (2 if tag == "a" else 1):
            if any(x >= len(roots) for x in args):
                raise ValueError("syntax references must point left")
            root = terms.make(tag, *(roots[x] for x in args))
        else:
            raise ValueError("unknown column format")
        roots.append(root)
    return roots


def append_column(columns, column, budget):
    if len(columns) >= budget.columns:
        raise ResourceLimit("output column budget")
    columns.append(column)
    budget.tick()


def emit(root, columns, positions, terms):
    """Append a postorder block, reusing the earliest existing syntax nodes."""
    already_present = root in positions
    stack = [(root, False)]
    while stack:
        current, visited = stack.pop()
        if current in positions:
            continue
        tag, *args = terms.data[current]
        children = args if tag in ("l", "a") else ()
        if not visited:
            stack.append((current, True))
            stack.extend((child, False) for child in reversed(children))
            continue
        column = (tag, *(positions[x] for x in args)) if children else (tag, *args)
        positions[current] = len(columns)
        append_column(columns, column, terms.budget)
    if already_present:
        tag, *args = terms.data[root]
        column = (tag, *(positions[x] for x in args)) if tag in ("l", "a") else (tag, *args)
        append_column(columns, column, terms.budget)


def expand(columns, n, budget=None):
    if type(n) is not int or n < 0:
        raise ValueError("the basic-sequence index must be natural")
    budget = budget or Budget()
    terms = Terms(budget)
    roots = decode(columns, terms)
    if not columns:
        return ()
    result = list(columns[:-1])
    if n == 0 or terms.data[roots[-1]][0] == "v":
        return tuple(result)
    positions = {}
    for index, root in enumerate(roots[:-1]):
        positions.setdefault(root, index)
    leaf = terms.make("v", 0)
    for i in range(n):
        positions.setdefault(leaf, len(result))
        append_column(result, ("v", 0), budget)
        child = terms.child(roots[-1], i)
        emit(child, result, positions, terms)
    return tuple(result)


def counts(columns, budget=None):
    terms = Terms(budget or Budget())
    return tuple(1 if terms.data[root][0] == "v" else 2 for root in decode(columns, terms))


def compare(left, right):
    """Only meaningful together inside one compatible standard domain."""
    a, b = counts(left), counts(right)
    return (a > b) - (a < b)


OMEGA = (("v", 0), ("l", 0))
OMEGA_SQUARED = OMEGA + (("l", 1),)
OMEGA_OMEGA = (("q",),)
