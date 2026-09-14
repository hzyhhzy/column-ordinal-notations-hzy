"""SPD: flat, integer slot-profile diagrams (research reference definition).

A column contains only (head, parent, argument, root) integer quadruples.
At child j, root<=parent is ROOT, root=j is SELF, root=j+1 is LATENT.
Derived shared heads are temporary indices, never notation input.

Fixed rule: highest visible head fiber, LATENT low packs, canonical guarded
connector, and typed carry after the first block. No experimental switches.
All public graph operations normalize list/tuple inputs. Standard membership
is NOT asserted or decided here. Resource exhaustion raises; results are never
silently truncated. Set individual Budget limits to None explicitly to disable.
"""
from dataclasses import dataclass, field
from functools import cmp_to_key
from math import isfinite
from time import monotonic


def _nat(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer, not bool")
    return value


def _sign(a, b):
    return (a > b) - (a < b)


@dataclass
class Budget:
    """A shared allocation/event allowance for one or several operations."""
    seconds: float | None = 15.0
    max_events: int | None = 2_000_000
    max_nodes: int | None = 100_000
    max_slots: int | None = 600_000
    max_pairs: int | None = 250_000
    max_contexts: int | None = 100_000
    max_columns: int | None = 2_000
    max_rows: int | None = 200_000
    used: dict = field(default_factory=dict, init=False)
    started: float = field(default_factory=monotonic, init=False)

    def __post_init__(self):
        for name in ('events', 'nodes', 'slots', 'pairs', 'contexts', 'columns', 'rows'):
            limit = getattr(self, 'max_' + name)
            if limit is not None and (_nat(limit, 'max_' + name) == 0):
                raise ValueError('Budget limits must be positive or None')
        if self.seconds is not None:
            if type(self.seconds) not in (int, float) or not isfinite(self.seconds) or self.seconds <= 0:
                raise ValueError('seconds must be finite and positive, or None')

    def tick(self):
        self.claim('events')
        if self.seconds is not None and monotonic() - self.started > self.seconds:
            raise TimeoutError('SPD time budget exhausted')

    def claim(self, kind, amount=1):
        value = self.used.get(kind, 0) + amount
        limit = getattr(self, 'max_' + kind)
        if limit is not None and value > limit:
            raise OverflowError(f'SPD {kind} budget exhausted')
        self.used[kind] = value

    def width(self, value):
        if self.max_columns is not None and value > self.max_columns:
            raise OverflowError('SPD column budget exhausted')

    def pending_rows(self, amount):
        if self.max_rows is not None and self.used.get('rows', 0) + amount > self.max_rows:
            raise OverflowError('SPD pending relation budget exhausted')


@dataclass(frozen=True, slots=True)
class _Node:
    kind: int                         # 0=Z, 1=ROOT, 2=N, 3=A, 4=B
    value: int = 0
    head: int = 0
    args: tuple = ()
    depth: int = 0


class _Heads:
    def __init__(self, budget):
        self.budget = budget
        self.nodes, self.intern = [], {}
        self.comparisons, self.contexts = {}, {}
        self.add(_Node(0))

    def add(self, node):
        self.budget.tick()
        if node in self.intern:
            return self.intern[node]
        self.budget.claim('nodes')
        if node.kind == 2:
            self.budget.claim('slots', len(node.args))
        value = len(self.nodes)
        self.nodes.append(node)
        self.intern[node] = value
        return value

    def atom(self, value):
        return self.add(_Node(1, value))

    def node(self, head, args):
        args = tuple(args)
        depth = max(self.nodes[head].depth + 1,
                    max((self.nodes[x].depth for x in args), default=0))
        return self.add(_Node(2, head=head, args=args, depth=depth))

    def known(self, a, b):
        if a == b:
            return 0
        x, y = self.nodes[a], self.nodes[b]
        if x.depth != y.depth:
            return _sign(x.depth, y.depth)
        if x.kind != 2 or y.kind != 2:
            return _sign(x.kind, y.kind) or _sign(x.value, y.value)
        return self.comparisons.get((a, b))

    def remember(self, a, b, value):
        self.budget.claim('pairs', 2)
        self.comparisons[a, b], self.comparisons[b, a] = value, -value

    def compare(self, a, b):
        """Iterative ordinary-child domination, then head/arity/lex LPO."""
        stack = [(a, b, 0, 0)]
        while stack:
            self.budget.tick()
            left, right, phase, position = stack.pop()
            if self.known(left, right) is not None:
                continue
            x, y = self.nodes[left], self.nodes[right]
            if phase < 2:
                children, other = (x.args, right) if phase == 0 else (y.args, left)
                if position == len(children):
                    stack.append((left, right, phase + 1, 0))
                    continue
                child = children[position]
                value = self.known(child, other)
                if value is None:
                    stack.extend(((left, right, phase, position), (child, other, 0, 0)))
                elif value >= 0:
                    self.remember(left, right, 1 if phase == 0 else -1)
                else:
                    stack.append((left, right, phase, position + 1))
            elif phase == 2:
                value = self.known(x.head, y.head)
                if value is None:
                    stack.extend(((left, right, phase, 0), (x.head, y.head, 0, 0)))
                elif value or len(x.args) != len(y.args):
                    self.remember(left, right, value or _sign(len(x.args), len(y.args)))
                else:
                    stack.append((left, right, 3, 0))
            else:
                if position == len(x.args):
                    raise AssertionError('Distinct interned heads compared equal')
                u, v = x.args[position], y.args[position]
                value = self.known(u, v)
                if value is None:
                    stack.extend(((left, right, phase, position), (u, v, 0, 0)))
                elif value:
                    self.remember(left, right, value)
                else:
                    stack.append((left, right, phase, position + 1))
        return self.known(a, b)

    def at_parent(self, root, parent):
        """Replace A by ROOT parent; B stays the common greatest atom."""
        stack = [root]
        while stack:
            self.budget.tick()
            i = stack[-1]
            if (i, parent) in self.contexts:
                stack.pop()
                continue
            node = self.nodes[i]
            if node.kind in (0, 1, 4):
                value = i
            elif node.kind == 3:
                value = self.atom(parent)
            else:
                needed = (node.head, *node.args)
                missing = next((v for v in needed if (v, parent) not in self.contexts), None)
                if missing is not None:
                    stack.append(missing)
                    continue
                value = self.node(self.contexts[node.head, parent],
                                  (self.contexts[v, parent] for v in node.args))
            self.budget.claim('contexts')
            self.contexts[i, parent] = value
            stack.pop()
        return self.contexts[root, parent]


class Diagram:
    """Temporary normalized columns and their derived shared comparison index."""
    def __init__(self, budget=None):
        self.budget = budget if budget is not None else Budget()
        self.arena = _Heads(self.budget)
        self.columns, self.heads = [], []

    def head_at(self, h, parent):
        return self.arena.at_parent(self.heads[h], parent)

    def head_key(self, h, k, parent):
        return self.arena.compare(self.head_at(h, parent), self.head_at(k, parent)) or _sign(h, k)

    def pair(self, h, s, k, t, parent):
        return self.head_key(h, k, parent) or self.head_key(s, t, parent)

    def profile(self, a, b):
        h, p, s, q = a
        k, r, t, v = b
        return (self.arena.compare(self.head_at(h, p), self.head_at(k, r)) or _sign(h, k)
                or self.arena.compare(self.head_at(s, p), self.head_at(t, r))
                or _sign(s, t) or _sign(q, v))

    def edge(self, a, b):
        return _sign(a[1], b[1]) or self.profile(a, b)

    def append(self, rows):
        self.budget.tick()
        j = len(self.columns)
        self.budget.width(j + 1)
        maximum = {}
        for row in rows:
            self.budget.tick()
            self.budget.claim('rows')
            if not isinstance(row, (tuple, list)) or len(row) != 4:
                raise ValueError('Each relation must be a four-integer list/tuple')
            h, p, s, q = (_nat(v, 'relation coordinate') for v in row)
            if not (h <= p < j and s <= p and (q <= p or q in (j, j + 1))):
                raise ValueError(f'Illegal relation at column {j}: {tuple(row)}')
            maximum[h, p, s] = max(q, maximum.get((h, p, s), -1))
        rows = tuple(sorted(((*key, q) for key, q in maximum.items()),
                            key=cmp_to_key(self.edge), reverse=True))
        self.columns.append(rows)
        visible = [e for e in rows if e[3] != j + 1]
        if not visible:
            self.heads.append(0)
            return j
        hstar = max((e[0] for e in visible), key=cmp_to_key(lambda h, k:
                    self.arena.compare(self.heads[h], self.heads[k]) or _sign(h, k)))
        args = []
        for h, p, s, q in sorted(visible, key=lambda e: (e[1], e[2], e[0], e[3]), reverse=True):
            if h == hstar:
                letter = self.arena.add(_Node(3 if q == p else 4)) if q in (p, j) else self.arena.atom(q)
                args.extend((self.heads[s], letter))
        self.heads.append(self.arena.node(self.heads[hstar], args))
        return j

    def control(self):
        return max(self.columns[-1], key=cmp_to_key(lambda a, b:
                   self.profile(a, b) or _sign(a[1], b[1])))


def read(graph, budget=None):
    if not isinstance(graph, (tuple, list)):
        raise ValueError('A graph must be a list/tuple of columns')
    result = Diagram(budget)
    for column in graph:
        if not isinstance(column, (tuple, list)):
            raise ValueError('A column must be a list/tuple of relations')
        result.append(column)
    return result


def normalize(graph, budget=None):
    return tuple(read(graph, budget).columns)


def seed(index, budget=None):
    """S_index has index+1 columns; S_0 is one empty column, not the empty graph."""
    width = _nat(index, 'seed index') + 1
    result = Diagram(budget)
    result.budget.width(width)
    for j in range(width):
        result.append(()) if j == 0 else result.append(((j - 1, j - 1, j - 1, j),))
    return tuple(result.columns)


def _move(row, old_child, new_child, address):
    h, p, s, q = row
    q = new_child + 1 if q == old_child + 1 else new_child if q == old_child else address(q)
    return address(h), address(p), address(s), q


def _connector(d, chosen, seam):
    h, cut, s, _ = chosen
    upper = d.head_at(h, seam), seam if h == cut else h, d.head_at(s, seam), seam if s == cut else s
    rows = []
    for k in range(seam + 1):
        for t in range(seam + 1):
            d.budget.tick()
            value = (d.arena.compare(d.head_at(k, seam), upper[0]) or _sign(k, upper[1])
                     or d.arena.compare(d.head_at(t, seam), upper[2]) or _sign(t, upper[3]))
            if value < 0:             # LATENT is maximal; equal pairs cannot pass.
                d.budget.pending_rows(len(rows) + 1)
                rows.append((k, seam, t, seam + 2))
    return rows


def fs(graph, index, budget=None):
    """Fundamental sequence: [0] deletes the last canonical column."""
    index = _nat(index, 'FS index')
    old = read(graph, budget)
    if not old.columns:
        return ()
    if index == 0 or not old.columns[-1]:
        return tuple(old.columns[:-1])
    chosen = old.control()
    h, cut, _, _ = chosen
    x = len(old.columns) - 1
    result = read(old.columns[:-1], old.budget)
    shift = 0
    for block in range(index):
        address = lambda i: i if i < cut else i + shift
        child = x + shift
        hh, cc, ss, qq = moved = _move(chosen, x, child, address)
        seam = [_move(row, x, child, address) for row in old.columns[-1] if row != chosen]
        if qq:
            lower = child if qq == child + 1 else cc if qq == child else qq - 1
            seam.append((hh, cc, ss, lower))
        for k in range(cc + 1):
            for t in range(cc + 1):
                result.budget.tick()
                if result.pair(k, t, hh, ss, cc) < 0:
                    result.budget.pending_rows(len(seam) + 1)
                    seam.append((k, cc, t, child + 1))
        if block:
            seam.extend(_move(row, cut, child, address) for row in old.columns[cut]
                        if row[3] == cut + 1 or row[0] == h)
        result.append(seam)
        bridge = _connector(result, moved, child)
        if bridge:
            result.append(bridge)
        shift += x - cut + 1 + bool(bridge)
        address = lambda i: i if i < cut else i + shift
        for j in range(cut, x):
            result.append(_move(row, j, address(j), address) for row in old.columns[j])
    return tuple(result.columns)


def compare(left, right, budget=None):
    """Direct first differing normalized column, not reachability search."""
    a = read(left, budget)
    b = read(right, a.budget)
    for xs, ys in zip(a.columns, b.columns):
        for x, y in zip(xs, ys):
            value = a.edge(x, y)       # All referenced columns precede this first difference.
            if value:
                return value
        if len(xs) != len(ys):
            return _sign(len(xs), len(ys))
    return _sign(len(a.columns), len(b.columns))


def counts(graph, budget=None):
    """Local frozen-prefix descent counts, not asserted ordinal values."""
    d = read(graph, budget)
    answer = []
    for j, column in enumerate(d.columns):
        total = 1
        for parent in {e[1] for e in column}:
            rows = [e for e in column if e[1] == parent]
            h, _, s, q = max(rows, key=cmp_to_key(d.profile))
            order = sorted(range(parent + 1), key=cmp_to_key(lambda h, k: d.head_key(h, k, parent)))
            rank = {h: i for i, h in enumerate(order)}
            digit = parent + 3 if q == j + 1 else parent + 2 if q == j else q + 1
            total += digit + (parent + 3) * ((parent + 1) * rank[h] + rank[s])
        answer.append(total)
    return tuple(answer)


if __name__ == '__main__':
    print('SPD research reference; seed column counts:', counts(seed(5)))
    print('seed(2)[1] =', fs(seed(2), 1))
