"""Lossless lists and head-free local counts for projection-copy FMP.

This module is not imported by the definition kernel.  Stars remain part
of the expression, but cannot affect the first replacement column's table.
An unknown count is never used as a numerical comparison value.
"""

import re

from fmp import Column, Pattern, trace


def validate(pattern):
    for r, column in enumerate(pattern.columns, 1):
        if not column.edges:
            if column.stars:
                raise ValueError('an empty column cannot carry stars')
            continue
        xs = tuple(x for x, _ in column.edges)
        ys = tuple(y for _, y in column.edges)
        if (len(xs) < 2 or tuple(sorted(set(xs))) != xs or
                tuple(sorted(set(ys))) != ys or xs[0] < 1 or
                xs[-2] >= r or xs[-1] != xs[-2] + 1 or
                ys[-2:] != (r, r + 1) or
                any(x >= y for x, y in column.edges)):
            raise ValueError(f'invalid completed map at column {r}')
        domain = set(xs)
        if any(y < xs[-2] and y not in domain for y in ys):
            raise ValueError(f'the map at column {r} is not self-closed')
        if not column.stars <= {y for y in ys[:-2] if y >= xs[-1]}:
            raise ValueError(f'a star is outside the internal upper window at column {r}')
        for source, head in column.edges:
            if head in column.stars and not trace(pattern.columns, head, source):
                raise ValueError(f'an inaccurate star at column {r}')
    return pattern


def display(pattern, full=False):
    if not pattern.columns:
        return '0'
    result = []
    for column in pattern.columns:
        if not column.edges:
            result.append('[]')
            continue
        edges = column.edges if full else column.edges[:-2]
        items = ','.join(f'{x}:{y}' + ('*' if y in column.stars else '')
                         for x, y in edges)
        if not full:
            items += (';' if items else '') + str(column.pivot)
        result.append('[' + items + ']')
    return ''.join(result)


def parse(text):
    """Read compact [x:y*,...;p], two-edge [p], or empty [] columns.

    Full explicit edge lists are accepted too.  This checks finite syntax,
    not reachability from the standard seeds.
    """
    text = re.sub(r'\s+', '', text)
    if text in ('', '0', '∅'):
        return Pattern()
    pieces = re.findall(r'\[([^\[\]]*)\]', text)
    if ''.join('[' + x + ']' for x in pieces) != text:
        raise ValueError('expected square-bracketed columns')
    columns = []
    for r, body in enumerate(pieces, 1):
        if not body:
            columns.append(Column())
            continue
        if ';' in body:
            part, pivot_text = body.split(';')
        elif ':' not in body:
            part, pivot_text = '', body
        else:
            part, pivot_text = body, None
        edges, stars = [], set()
        for item in part.split(',') if part else []:
            match = re.fullmatch(r'(\d+):(\d+)(\*)?', item)
            if not match:
                raise ValueError('an edge must be x:y or x:y*')
            x, y = int(match[1]), int(match[2])
            edges.append((x, y))
            if match[3]:
                stars.add(y)
        if pivot_text is not None:
            if not pivot_text.isdecimal():
                raise ValueError('the pivot must be a positive integer')
            pivot = int(pivot_text)
            edges.extend(((pivot, r), (pivot + 1, r + 1)))
        columns.append(Column(tuple(edges), frozenset(stars)))
    return validate(Pattern(tuple(columns)))


def state(column):
    """A count state omits stars and both head-dependent target endpoints."""
    return (column.pivot, column.edges[:-2]) if column.edges else None


def local_step(states, current):
    """Rewrite a nonempty compact column; None denotes the empty column.

    This rule has no head/length parameter.  Only the column at the pivot
    is consulted.  The omitted cap source must still be transportable.
    """
    pivot, internal = current
    source = states[pivot - 1]
    if source is None or not internal:
        return source
    minimum = internal[0][0]
    table = dict(internal)

    def image(x):
        return x if x < minimum else table[x]

    q, old = source
    try:
        if q + 1 < pivot:
            image(q + 1)  # Necessary even though the new cap is normalized.
        new_pivot = image(q)
        edges = tuple((image(x), image(y)) for x, y in old)
    except KeyError:
        return None  # The source column is forgotten, not the entire step.
    return new_pivot, edges


class Counter:
    """Exact context-dependent memoization, shared across all columns.

    A state created at position j can consult only positions below j.
    Rehanging it at any later head therefore gives the same local count.
    The memo must NOT be reused with a different earlier column context.
    """

    def __init__(self, pattern):
        self.states = tuple(state(c) for c in pattern.columns)
        self.memo = {None: 1}

    def count(self, current, check=lambda *_: None):
        path, seen = [], set()
        while current not in self.memo:
            check(len(path))
            if current in seen:
                raise ValueError('a local cycle was found')
            seen.add(current)
            path.append(current)
            current = local_step(self.states, current)
        value = self.memo[current]
        for item in reversed(path):
            value += 1
            self.memo[item] = value
        return value

    def compare(self, left, right, check=lambda *_: None):
        """Compare by the first meeting of the two local trajectories."""
        paths, current = [{}, {}], [left, right]
        depth = 0
        while True:
            if current[0] is None or current[1] is None:
                if current[0] is current[1]:
                    raise ValueError('equal counts in distinct columns: noncanonical input')
                return -1 if current[0] is None else 1
            for side in (0, 1):
                check(depth)
                item = current[side]
                if item in paths[1 - side]:
                    difference = depth - paths[1 - side][item]
                    if side:
                        difference = -difference
                    if not difference:
                        raise ValueError('equal counts in distinct columns: noncanonical input')
                    return 1 if difference > 0 else -1
                if item in paths[side]:
                    raise ValueError('a local cycle was found')
                paths[side][item] = depth
                current[side] = local_step(self.states, item)
            depth += 1


def counts(pattern, check=lambda *_: None):
    counter = Counter(pattern)
    return tuple(counter.count(item, check) for item in counter.states)


def compare(left, right, check=lambda *_: None):
    for i, (a, b) in enumerate(zip(left.columns, right.columns)):
        if a != b:
            counter = Counter(Pattern(left.columns[:i]))
            return counter.compare(state(a), state(b), check)
    return (len(left.columns) > len(right.columns)) - (len(left.columns) < len(right.columns))
