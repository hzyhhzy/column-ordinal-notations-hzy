"""CWY (Compact wY): finite columns of (parent, normalized address word).

Domain: Phi(Std_wY), with omega-Y *weak magma* as the source notation.
There is no stored numeric sequence, tree, operation history, or oracle.
Geometry reconstruction is only an inverse on the canonical image; successful
construction or structural validation is NOT a membership certificate.

seed(m) denotes Phi((1,m)); zero() is the empty tuple. Python integers are exact.
The conservative decrement reconstructs geometry and grafts its upper tail.
"""

from dataclasses import dataclass, field
from time import perf_counter
import re

Word = tuple[int, ...]
Column = tuple[tuple[int, Word], ...]
Expression = tuple[Column, ...]


class ResourceLimit(RuntimeError):
    """Computation stopped without a mathematical result or validity verdict."""


class InvalidStructure(ValueError):
    pass


@dataclass
class Budget:
    seconds: float = 2.0
    max_nodes: int = 25_000
    max_columns: int = 20_000
    max_word: int = 128
    max_payload: int = 1_000_000
    max_operations: int = 2_000_000
    started: float = field(default_factory=perf_counter, init=False)
    nodes: int = field(default=0, init=False)
    payload: int = field(default=0, init=False)
    operations: int = field(default=0, init=False)

    def tick(self, payload=0, node=False):
        self.operations += 1
        self.payload += payload
        self.nodes += bool(node)
        if (self.operations > self.max_operations or self.nodes > self.max_nodes
                or self.payload > self.max_payload
                or perf_counter() - self.started >= self.seconds):
            raise ResourceLimit("Budget exhausted; no truncation or validity verdict")


def zero() -> Expression:
    return ()


def kind(expr: Expression) -> str:
    return "zero" if not expr else "successor" if not expr[-1] else "limit"


def is_zero(expr: Expression) -> bool:
    return not expr


def is_successor(expr: Expression) -> bool:
    return bool(expr) and not expr[-1]


def is_limit(expr: Expression) -> bool:
    return bool(expr) and bool(expr[-1])


def word_key(word):
    return word[0], len(word), word


def compare(left: Expression, right: Expression) -> int:
    """Compare first differing columns; no FS or geometry evaluation."""
    for a, b in zip(left, right):
        ka = tuple((p, word_key(w)) for p, w in a)
        kb = tuple((p, word_key(w)) for p, w in b)
        if ka != kb:
            return 1 if ka > kb else -1
    return (len(left) > len(right)) - (len(left) < len(right))


def normalize_word(word):
    start = 0
    while start + 1 < len(word) and word[start] == word[start + 1]:
        start += 1
    return tuple(word[start:])


def normalize_column(entries):
    largest = {}
    for parent, word in entries:
        if parent not in largest or word_key(word) > word_key(largest[parent]):
            largest[parent] = tuple(word)
    result = []
    for parent in sorted(largest, reverse=True):
        word = largest[parent]
        if not result or word_key(result[-1][1]) < word_key(word):
            result.append((parent, word))
    return tuple(result)


def validate_structure(expr: Expression, budget=None):
    """Check syntax only, not the raw image or the standard generated domain."""
    budget = budget or Budget()
    if len(expr) > budget.max_columns:
        raise ResourceLimit("Column budget exceeded")
    dimension = 0
    for child, column in enumerate(expr):
        previous = child
        for parent, word in column:
            budget.tick(payload=1 + len(word))
            if type(parent) is not int or not 0 <= parent < previous:
                raise InvalidStructure("Parents must be earlier and strictly descending")
            previous = parent
            if not word or len(word) > budget.max_word:
                if not word:
                    raise InvalidStructure("Empty address word")
                raise ResourceLimit("Word-length budget exceeded")
            if word[0] > parent or (len(word) > 1 and word[0] == word[1]):
                raise InvalidStructure("The word is not normalized")
            for i, q in enumerate(word):
                if (type(q) is not int or q < 0 or (q > parent and q != child)
                        or (i and q < word[i - 1])):
                    raise InvalidStructure("Invalid ROOT/SELF address")
            dimension = max(dimension, len(word) - 1)
    return dimension


def seed(m: int, budget=None) -> Expression:
    """The canonical image of (1,m), for any positive natural m."""
    budget = budget or Budget()
    if type(m) is not int or m < 1:
        raise ValueError("m must be a positive integer")
    if m - 1 > budget.max_word:
        raise ResourceLimit("Seed word exceeds the word-length budget")
    budget.tick(payload=m)
    return ((), ()) if m == 1 else ((), ((0, (0,) + (1,) * (m - 2)),))


@dataclass(frozen=True, slots=True)
class _Point:
    column: int
    height: tuple[int, ...]
    parent: "_Point | None"
    word: "Word | None"
    index: int


def _height_key(height):
    return len(height), tuple(reversed(height))


def _recover(expr, budget):
    """Value-free geometry. Requires membership in the canonical image."""
    dimension = validate_structure(expr, budget)
    mountain = []
    for child, entries in enumerate(expr):
        column = []

        def append(height, parent=None, word=None):
            budget.tick(payload=len(height) + (len(word) if word else 0), node=True)
            point = _Point(child, tuple(height), parent, word, len(column))
            column.append(point)
            return point

        append(())  # The phantom is needed for the bottom horizontal chain.
        top = append((1,), mountain[child - 1][0] if child else None)
        mountain.append(column)
        for parent_index, maximum in entries:
            source = mountain[parent_index]
            while True:
                budget.tick()
                low, high = 0, len(source) - 1
                while low < high:
                    middle = (low + high + 1) // 2
                    if _height_key(source[middle].height) <= _height_key(top.height):
                        low = middle
                    else:
                        high = middle - 1
                parent = source[low]
                a, b = parent.height, top.height
                jump = max((i + 1 for i in range(max(len(a), len(b)))
                            if (a[i] if i < len(a) else 0)
                            != (b[i] if i < len(b) else 0)), default=0)
                if jump > dimension:
                    raise InvalidStructure("Required jump exceeds the profile dimension")
                old = source[low + 1].word if low + 1 < len(source) else (parent_index,)
                if old is None:
                    raise InvalidStructure("A phantom cannot be an upper subtraction parent")
                word = [old[0]] * max(0, jump + 1 - len(old)) + list(old)
                if jump:
                    word[-jump:] = [child] * jump
                word = normalize_word(word)
                if word_key(word) > word_key(maximum) or (top.word and word_key(top.word) >= word_key(word)):
                    raise InvalidStructure("The requested profile lies in a geometry gap")
                height = list(top.height) + [0] * max(0, jump + 1 - len(top.height))
                height[jump] += 1
                height[:jump] = [0] * jump
                top = append(height, parent, word)
                if word == maximum:
                    break
    return mountain


def minus_column(expr: Expression, budget=None) -> Column:
    """Exact geometric decrement, returning only the modified last column."""
    if not expr or not expr[-1]:
        raise ValueError("A nonempty limit column is required")
    budget = budget or Budget()
    mountain = _recover(expr, budget)
    child = len(expr) - 1
    column = mountain[-1]
    top = column[-1]
    parent = top.parent
    rows = [(point.parent.column, point.word) for point in column[2:-1]]
    for point in mountain[parent.column][parent.index + 1:]:
        budget.tick(payload=1 + len(point.word))
        rows.append((point.parent.column,
                     tuple(child if q == parent.column else q for q in point.word)))
    return normalize_column(rows)


def fs(expr: Expression, index: int, budget=None) -> Expression:
    """Canonical fundamental sequence; [0] deletes the last column."""
    if type(index) is not int or index < 0:
        raise ValueError("The index must be a natural number")
    budget = budget or Budget()
    if not expr:
        return ()
    if index == 0 or not expr[-1]:
        validate_structure(expr, budget)
        return expr[:-1]
    last = len(expr) - 1
    cut = expr[-1][-1][0]
    width = last - cut
    if last + index * width > budget.max_columns:
        raise ResourceLimit("Output column budget exceeded; no truncation")
    lowered = minus_column(expr, budget)
    result = list(expr[:-1])

    def moved(column, block):
        def move(q):
            return q if q < cut else q + block * width
        rows = []
        for parent, word in column:
            budget.tick(payload=1 + len(word))
            rows.append((move(parent), tuple(move(q) for q in word)))
        return tuple(rows)

    for block in range(index):
        budget.tick()
        result.append(moved(lowered, block))
        for offset in range(1, width):
            result.append(moved(expr[cut + offset], block + 1))
    return tuple(result)


def format_expr(expr: Expression, show_self=False) -> str:
    """Complete canonical text: no omitted columns, cached values or history."""
    if not expr:
        return "0"
    return "".join("[" + ";".join(
        str(parent) + ":(" + ",".join("*" if show_self and q == child else str(q) for q in word) + ")"
        for parent, word in column) + "]" for child, column in enumerate(expr))


def parse(text: str, budget=None) -> Expression:
    """Read the complete list syntax, checking structure but not membership."""
    budget = budget or Budget()
    if len(text) > budget.max_payload:
        raise ResourceLimit("Input text budget exceeded")
    text = re.sub(r"\s+", "", text)
    if text == "0":
        return ()
    if not text:
        raise InvalidStructure("Use 0 for the empty expression")
    token = re.compile(r"\d+|[][():;,*]")
    tokens = token.findall(text)
    if "".join(tokens) != text:
        raise InvalidStructure("Unexpected text")
    position, columns = 0, []

    def take(expected=None):
        nonlocal position
        if position == len(tokens):
            raise InvalidStructure("Unexpected end of expression")
        value = tokens[position]
        position += 1
        if expected is not None and value != expected:
            raise InvalidStructure("Expected " + expected)
        return value

    while position < len(tokens):
        take("[")
        column = []
        while position < len(tokens) and tokens[position] != "]":
            parent = int(take())
            take(":")
            take("(")
            word = []
            while True:
                value = take()
                word.append(len(columns) if value == "*" else int(value))
                if position == len(tokens) or tokens[position] != ",":
                    break
                take(",")
            take(")")
            column.append((parent, tuple(word)))
            if position == len(tokens) or tokens[position] != ";":
                break
            take(";")
        take("]")
        columns.append(tuple(column))
    result = tuple(columns)
    validate_structure(result, budget)
    return result


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=3, help="m in the source pair (1,m)")
    parser.add_argument("--index", type=int, default=6)
    args = parser.parse_args()
    value = seed(args.seed)
    print(format_expr(value))
    print(format_expr(fs(value, args.index)))
