"""Lambda Computation Diagram Notation: bounded research implementation.

Data: ('v', k), ('q',), ('l', i), ('a', i, j). Activity: ('run', i).
Data pointers and activity pointers go strictly left. A variable's k is a
de Bruijn distance, NOT a column index. Only activity columns are limits.

This file reuses the old explicit capture-avoiding DAG substitution helper.
It does not yet specify a complete global family with a Z-omega lower bound.
"""

from __future__ import annotations

from math import isqrt
import lambda_columns as base

Budget = base.Budget
ResourceLimit = base.ResourceLimit
LEAF = ("v", 0)


def unpair(index):
    diagonal = (isqrt(8 * index + 1) - 1) // 2
    second = index - diagonal * (diagonal + 1) // 2
    return diagonal - second, second


class Terms(base.Terms):
    atom_arities = {"v": 1, "q": 0}
    pointer_arities = {"l": 1, "a": 2}

    def __init__(self, budget):
        super().__init__(budget)
        self.redex_cache = {}

    def children(self, node):
        tag, *args = self.data[node]
        return args if tag in self.pointer_arities else []

    def is_redex(self, node):
        tag, *args = self.data[node]
        return (tag == "q" or
                (tag == "a" and self.data[args[0]][0] == "l"))

    def _binding_walk(self, root, parameter, depth, substitution):
        """Capture-avoiding DAG walk; constants never masquerade as pointers."""
        cache = self.subst_cache if substitution else self.shift_cache
        target = (root, parameter, depth)
        stack = [(root, depth, False)]
        while stack:
            node, level, ready = stack.pop()
            key = (node, parameter, level)
            if key in cache:
                continue
            self.budget.tick()
            tag, *args = self.data[node]
            children = self.children(node)
            if tag == "v":
                k = args[0]
                if substitution:
                    result = (self.shift(parameter, level) if k == level else
                              self.make("v", k - 1 if k > level else k))
                else:
                    result = self.make("v", k + parameter if k >= level else k)
            elif not children:
                result = node
            elif not ready:
                stack.append((node, level, True))
                stack.extend((x, level + (tag == "l"), False)
                             for x in reversed(children))
                continue
            else:
                result = self.make(tag, *(cache[(x, parameter, level + (tag == "l"))]
                                          for x in children))
            cache[key] = result
        return cache[target]

    def shift(self, root, amount, depth=0):
        return self._binding_walk(root, amount, depth, False)

    def substitute(self, body, argument, depth=0):
        return self._binding_walk(body, argument, depth, True)

    def redex_count(self, root):
        """Count occurrences without expanding a shared graph into a tree.

        The count can be exponential in the DAG length, but its binary length
        is linear.  Exact integers let selection skip entire shared subtrees.
        """
        stack = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node in self.redex_cache:
                continue
            self.budget.tick()
            children = self.children(node)
            if children and not ready:
                stack.append((node, True))
                stack.extend((child, False) for child in reversed(children))
                continue
            answer = int(self.is_redex(node)) + sum(self.redex_cache[x] for x in children)
            self.redex_cache[node] = answer
        return self.redex_cache[root]

    def reducible(self, root):
        return self.redex_count(root) > 0

    def contract(self, root, numeral):
        tag, *args = self.data[root]
        if tag == "q":
            return self.numeral(numeral)
        if tag == "a" and self.data[args[0]][0] == "l":
            return self.substitute(self.data[args[0]][1], args[1])
        return None

    def context_step(self, root, address, numeral):
        directions = []
        current = address + 1
        while current > 1:
            self.budget.tick()
            directions.append(current & 1)
            current //= 2
        path = []
        selected = root
        for side in reversed(directions):
            self.budget.tick()
            args = self.children(selected)
            if side >= len(args):
                return None
            path.append((selected, side))
            selected = args[side]
        result = self.contract(selected, numeral)
        if result is None:
            return None
        for parent, side in reversed(path):
            tag, *args = self.data[parent]
            args[side] = result
            result = self.make(tag, *args)
        return result

    def computation_child(self, root, index):
        occurrence, numeral = unpair(index)
        occurrence %= self.redex_count(root)
        selected, path = root, []
        while True:
            self.budget.tick()
            tag, *args = self.data[selected]
            is_redex = self.is_redex(selected)
            if is_redex:
                if occurrence == 0:
                    break
                occurrence -= 1
            children = self.children(selected)
            for side, child in enumerate(children):
                count = self.redex_count(child)
                if occurrence < count:
                    path.append((selected, side))
                    selected = child
                    break
                occurrence -= count
            else:
                raise AssertionError("redex occurrence count is inconsistent")
        child = self.contract(selected, numeral)
        if child is None:
            raise AssertionError("selected occurrence is not a redex")
        for parent, side in reversed(path):
            tag, *args = self.data[parent]
            args[side] = child
            child = self.make(tag, *args)
        return child


def activity(column):
    return isinstance(column, tuple) and len(column) == 2 and column[0] == "run"


def decode(columns, terms):
    roots = []
    for column in columns:
        if not isinstance(column, tuple) or not column:
            raise ValueError("a column must be a tuple")
        tag, *args = column
        if any(type(x) is not int or x < 0 for x in args):
            raise ValueError("indices must be natural numbers")
        if tag in terms.atom_arities and len(args) == terms.atom_arities[tag]:
            root = terms.make(tag, *args)
        elif (tag == "run" and len(args) == 1 or
              tag in terms.pointer_arities and len(args) == terms.pointer_arities[tag]):
            if any(x >= len(roots) or roots[x] is None for x in args):
                raise ValueError("pointers must refer to earlier data columns")
            if tag == "run":
                if not terms.reducible(roots[args[0]]):
                    raise ValueError("an activity must have a redex")
                root = None
            else:
                root = terms.make(tag, *(roots[x] for x in args))
        else:
            raise ValueError("unknown column format")
        roots.append(root)
    return roots


def emit_data(root, columns, positions, terms):
    stack = [(root, False)]
    while stack:
        node, ready = stack.pop()
        if node in positions:
            continue
        tag, *args = terms.data[node]
        children = terms.children(node)
        if children and not ready:
            stack.append((node, True))
            stack.extend((x, False) for x in reversed(children))
            continue
        column = (tag, *(positions[x] for x in children)) if children else (tag, *args)
        positions[node] = len(columns)
        base.append_column(columns, column, terms.budget)
    return positions[root]


def expand(columns, n, budget=None, term_type=Terms):
    if type(n) is not int or n < 0:
        raise ValueError("the basic-sequence index must be natural")
    terms = term_type(budget or Budget())
    roots = decode(columns, terms)
    if not columns:
        return ()
    result = list(columns[:-1])
    if n == 0 or not activity(columns[-1]):
        return tuple(result)
    source = roots[columns[-1][1]]
    positions = {}
    for index, root in enumerate(roots[:-1]):
        if root is not None:
            positions.setdefault(root, index)
    leaf = terms.make("v", 0)
    for i in range(n):
        positions.setdefault(leaf, len(result))
        base.append_column(result, LEAF, terms.budget)
        child = terms.computation_child(source, i)
        if terms.reducible(child):
            pointer = emit_data(child, result, positions, terms)
            base.append_column(result, ("run", pointer), terms.budget)
        else:
            base.append_column(result, LEAF, terms.budget)
    return tuple(result)


def counts(columns):
    return tuple(2 if activity(column) else 1 for column in columns)


def compare(left, right):
    a, b = counts(left), counts(right)
    return (a > b) - (a < b)


def append_program(columns, source_terms, source_root):
    """Authoring only: compatibility comes from preserving the entire prefix."""
    target = type(source_terms)(Budget(seconds=2.0))
    roots = decode(columns, target)
    positions = {}
    for index, root in enumerate(roots):
        if root is not None:
            positions.setdefault(root, index)
    translated = {}
    for index, (tag, *args) in enumerate(source_terms.data):
        translated[index] = (target.make(tag, *(translated[x] for x in args))
                             if tag in source_terms.pointer_arities else target.make(tag, *args))
    root = translated[source_root]
    result = list(columns)
    if target.reducible(root):
        pointer = emit_data(root, result, positions, target)
        base.append_column(result, ("run", pointer), target.budget)
    else:
        base.append_column(result, LEAF, target.budget)
    return tuple(result)


def tower_seed(terms, fixed_base=False):
    q = terms.make("q")
    x = terms.make("v", 0)
    identity = terms.make("l", x)
    zero = terms.make("l", identity)
    right_q = terms.make("l", terms.make("a", x, q))
    e = terms.make("a", terms.make("a", q, right_q), zero if fixed_base else q)
    return terms.make("a", terms.make("a", e, identity), zero)


OMEGA = (("q",), ("run", 0))
