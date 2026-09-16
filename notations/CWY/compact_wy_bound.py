"""CWY with an explicit upper boundary B and root-marker stretching.

The domain is exactly stretch(Phi(Std_wY)) together with B. This creates a
proper initial-segment copy of wY, not a substantial strength increase.
S is a genuine column symbol above every ordinary profile column. Nothing
stores the original numeric sequence or the expansion history.
"""

import re
import compact_wy as core

S = "S"
Budget = core.Budget
ResourceLimit = core.ResourceLimit
InvalidStructure = core.InvalidStructure


def zero():
    return ()


def boundary():
    return ((), S)


def is_boundary(expr):
    return expr == boundary()


def kind(expr):
    return "zero" if not expr else "successor" if expr[-1] == () else "limit"


def _check_width(width, budget):
    if width > budget.max_columns:
        raise ResourceLimit("Physical output column budget exceeded; no truncation")


def stretch(expr, budget=None):
    """Embed a core expression, replacing its second column by root markers."""
    budget = budget or Budget()
    core.validate_structure(expr, budget)
    if len(expr) < 2:
        _check_width(len(expr), budget)
        return expr
    root = expr[1]
    value = len(root[0][1]) + 1 if root else 1
    if root != core.seed(value, budget)[1]:
        raise InvalidStructure("The second column is not a canonical seed column")
    _check_width(len(expr) + value - 1, budget)

    def move(q):
        return 0 if q == 0 else q + value - 1

    result = [(), (), *([S] * (value - 1))]
    for column in expr[2:]:
        rows = []
        for parent, word in column:
            budget.tick(payload=1 + len(word))
            rows.append((move(parent), tuple(move(q) for q in word)))
        result.append(tuple(rows))
    return tuple(result)


def unstretch(expr, budget=None):
    """Inverse on the stretched canonical image, excluding B."""
    budget = budget or Budget()
    _check_width(len(expr), budget)
    if is_boundary(expr):
        raise InvalidStructure("B is not an old wY expression")
    if len(expr) < 2:
        core.validate_structure(expr, budget)
        return expr
    if expr[:2] != ((), ()):
        raise InvalidStructure("A stretched core starts with two empty columns")
    first_data = 2
    while first_data < len(expr) and expr[first_data] == S:
        budget.tick()
        first_data += 1
    value = first_data - 1

    def undo(q):
        if q == 0:
            return 0
        if type(q) is not int or q < value:
            raise InvalidStructure("A reference enters a synthetic root marker")
        return q - value + 1

    result = list(core.seed(value, budget))
    for column in expr[first_data:]:
        if column == S:
            raise InvalidStructure("A root marker occurs after ordinary tail data")
        rows = []
        for parent, word in column:
            budget.tick(payload=1 + len(word))
            rows.append((undo(parent), tuple(undo(q) for q in word)))
        result.append(tuple(rows))
    result = tuple(result)
    core.validate_structure(result, budget)  # Shape only, not image membership.
    return result


def seed(m, budget=None):
    budget = budget or Budget()
    return stretch(core.seed(m, budget), budget)


def fs(expr, index, budget=None):
    if type(index) is not int or index < 0:
        raise ValueError("The index must be a natural number")
    budget = budget or Budget()
    if not expr:
        return ()
    if index == 0:
        _check_width(len(expr) - 1, budget)
        return expr[:-1]
    if is_boundary(expr):
        _check_width(index + 1, budget)
        budget.tick(payload=index + 1)
        return ((), (), *([S] * (index - 1)))
    source = unstretch(expr, budget)
    shift = int(len(source) == 2 and bool(source[1]))
    # At a pure non-successor root use the old F_(n+1); [0] already deletes S.
    result = stretch(core.fs(source, index + shift, budget), budget)
    _check_width(len(result), budget)  # Check stretched physical width as well.
    return result


def compare(left, right):
    for a, b in zip(left, right):
        if a == S or b == S:
            difference = (a == S) - (b == S)
        else:
            difference = core.compare((a,), (b,))
        if difference:
            return difference
    return (len(left) > len(right)) - (len(left) < len(right))


def format_expr(expr, show_self=False):
    if not expr:
        return "0"
    result = []
    for child, column in enumerate(expr):
        if column == S:
            result.append("[S]")
        else:
            rows = (str(parent) + ":(" + ",".join(
                "*" if show_self and q == child else str(q) for q in word) + ")"
                for parent, word in column)
            result.append("[" + ";".join(rows) + "]")
    return "".join(result)


def parse(text, budget=None):
    """Parse full lists; success checks shape, not standard-domain membership."""
    budget = budget or Budget()
    if len(text) > budget.max_payload:
        raise ResourceLimit("Input text budget exceeded")
    text = re.sub(r"\s+", "", text)
    if text == "0":
        return ()
    if text == "B":
        return boundary()
    blocks = re.findall(r"\[([^\[\]]*)\]", text)
    if not blocks or "".join("[" + b + "]" for b in blocks) != text:
        raise InvalidStructure("Expected a complete column list")
    result = []
    for child, block in enumerate(blocks):
        if block == S:
            result.append(S)
            continue
        rows = []
        for row in block.split(";") if block else []:
            match = re.fullmatch(r"(\d+):\(((?:\d+|\*)(?:,(?:\d+|\*))*)\)", row)
            if not match:
                raise InvalidStructure("Expected parent:(address,...)")
            parent = int(match.group(1))
            word = tuple(child if q == "*" else int(q) for q in match.group(2).split(","))
            rows.append((parent, word))
        result.append(tuple(rows))
    result = tuple(result)
    if is_boundary(result):
        _check_width(2, budget)
    else:
        unstretch(result, budget)
    return result


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, help="Use stretched Phi((1,m)); otherwise use B")
    parser.add_argument("--index", type=int, default=4)
    args = parser.parse_args()
    value = boundary() if args.seed is None else seed(args.seed)
    print(format_expr(value))
    print(format_expr(fs(value, args.index)))
