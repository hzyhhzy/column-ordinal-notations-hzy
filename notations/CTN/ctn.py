"""CTN: Comprehension Table Notation, current linear-limit edition.

Former research name: CTN2. The original CTN frontend is retired.
Actual columns are 1 and 2; grouped displays never participate in expansion.
The mathematical rules are unchanged by this packaging and renaming.
"""

from ctn_table import table_ok as base_table_ok


def table_tree(encoded_values):
    """Uniform positive coding: k+1 denotes the actual table value k.

    Zero is a terminal branch at EVERY node, not a special omega rule.
    """
    return all(k > 0 for k in encoded_values) and base_table_ok([k - 1 for k in encoded_values])


def parse(word, tree=table_tree):
    """Check the padded domain in linear parsing plus one finite tree test.

    A failed child has only a terminal chain of 1s. A non-root cap may also
    have a terminal chain of 1s. We need not search for the first failed child:
    for a word ending in 1 with no cap, failure is allowed exactly when it is
    after the last occurrence of 2.
    """
    if not isinstance(word, str) or any(c not in "12" for c in word):
        raise ValueError("An expression must be a string of columns 1 and 2")
    values, offset, last_positive = [], 0, -1
    kind, opened = "entry", 0
    while offset < len(word):
        if word[offset] == "2":
            tail = word[offset + 1:]
            if any(c != "1" for c in tail):
                raise ValueError("Only successor columns may follow a cap")
            if not values and tail:
                raise ValueError("No expression is above the global top 2")
            if not tree(values):
                raise ValueError("A cap requires a consistent completed table")
            return values, "tail" if tail else "cap", 0
        offset += 1
        start = offset
        while offset < len(word) and word[offset] == "2":
            offset += 1
        opened = offset - start
        if offset == len(word):
            kind = "gap"
            break
        values.append(opened)
        if opened:
            last_positive = len(values) - 1
        offset += 1
        kind = "entry"
    # If the final symbol is 2, every completed block precedes that 2 and must
    # be valid. Otherwise only blocks before the last positive-valued block
    # must be valid: a failed block and its all-1 tail are terminal successors.
    checked = values if word.endswith("2") else values[:max(0, last_positive)]
    if not tree(checked):
        raise ValueError("A failed child cannot be followed by another 2")
    return values, kind, opened


def is_standard(word, tree=table_tree):
    try:
        parse(word, tree)
        return True
    except ValueError:
        return False


def is_successor(word):
    """For a LEGAL input, this is the complete constant-time criterion."""
    return word.endswith("1")


def is_limit(word):
    """No direct predecessor, even in the non-well-founded part of the order."""
    return word.endswith("2")


def fundamental(word, n, tree=table_tree):
    if not isinstance(n, int) or n < 0:
        raise ValueError("The basic-sequence index must be a natural number")
    values, kind, opened = parse(word, tree)
    if not word:
        return ""
    prefix = word[:-1]
    if n == 0 or word[-1] == "1":
        return prefix
    if kind == "cap":
        return prefix + "1" + "2" * (n - 1)
    if tree(values + [opened - 1]):
        return prefix + "12" + "1" * (n - 1)
    return prefix + "1" * n


def compare(left, right):
    return (left > right) - (left < right)


def encode_table(values, cap=False):
    """Encode a table, without claiming that the table passes the checker."""
    return "".join("1" + "2" * (k + 1) + "1" for k in values) + ("2" if cap else "")


TOP = "2"
OMEGA = "12"
