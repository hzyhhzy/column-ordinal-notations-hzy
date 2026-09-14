"""IPD: Iterated Profile Diagrams, zero-start version (2026-09-14).

Readable mathematical reference; no browser, graphics or counting engine.
An edge is (parent, (level, tree)). At level 0 a tree is a ROOT/SELF
integer. At positive levels ZERO=(), and a node is (head, children).
The head is CAP=-1 or a tree one level lower. A diagram is a column tuple.
Only descendants of the seeds form the standard notation domain.
"""

from dataclasses import dataclass
from functools import lru_cache, total_ordering

ZERO, CAP = (), -1


def node(head, children=()):
    return head, tuple(children)


@lru_cache(maxsize=50000)
def compare(level, a, b):
    """Arity-sensitive lexicographic path order, not tree-code order."""
    if a == b:
        return 0
    if level == 0:
        return (a > b) - (a < b)
    if a == ZERO or b == ZERO:
        return 1 if a != ZERO else -1
    ah, aa = a
    bh, bb = b
    if any(compare(level, child, b) >= 0 for child in aa):
        return 1
    if any(compare(level, child, a) >= 0 for child in bb):
        return -1
    if ah != bh:
        if ah == CAP or bh == CAP:
            return 1 if ah == CAP else -1
        relation = compare(level - 1, ah, bh)
        if relation:
            return relation
    if len(aa) != len(bb):
        return (len(aa) > len(bb)) - (len(aa) < len(bb))
    for left, right in zip(aa, bb):
        relation = compare(level, left, right)
        if relation:
            return relation
    raise AssertionError("Distinct trees must compare differently")


def maximum(level, terms):
    result = ZERO
    for term in terms:
        if compare(level, term, result) > 0:
            result = term
    return result


def cofinal_seed(level, index, parent, child):
    if level == 0:
        return parent if index == 0 else child
    return ZERO if index == 0 else node(CAP, (ZERO,) * (index - 1))


def lower(level, term, parent, child, index, tick=lambda: None):
    """Internal approximation. None means below the internal minimum."""
    tick()
    if level == 0:
        return None if term == 0 else parent if term == child else term - 1
    if term == ZERO:
        return None
    head, children = term
    smaller = cofinal_seed(level - 1, index, parent, child) if head == CAP else lower(
        level - 1, head, parent, child, index, tick)
    bound = maximum(level, (node(head), *children)) if children else ZERO
    heads = [(head, len(children) - 1)] if children else []
    if smaller is not None:
        heads.append((smaller, index))
    # Definition: all nonzero child positions. The NER version uses a proved
    # exact two-position pruning, not a different approximation rule.
    lowered = [(i, lower(level, t, parent, child, index, tick))
               for i, t in enumerate(children) if t != ZERO]
    for _ in range(index + 1):
        tick()
        candidates = [bound, *(node(h, (bound,) * arity) for h, arity in heads)]
        for i, low in lowered:
            candidates.append(node(head, (*children[:i], low, *((bound,) * (len(children) - i - 1)))))
        bound = maximum(level, candidates)
    return bound


def profile_compare(a, b):
    return (a[0] > b[0]) - (a[0] < b[0]) or compare(a[0], a[1], b[1])


def profile_lower(profile, parent, child, index, tick=lambda: None):
    level, term = profile
    result = lower(level, term, parent, child, index, tick)
    if result is not None:
        return level, result
    return (level - 1, cofinal_seed(level - 1, index, parent, child)) if level else None


def move_term(level, term, mapping):
    if level == 0:
        return mapping(term)
    if term == ZERO:
        return ZERO
    head, children = term
    h = CAP if head == CAP else move_term(level - 1, head, mapping)
    return node(h, (move_term(level, t, mapping) for t in children))


def move_profile(profile, mapping):
    return profile[0], move_term(*profile, mapping)


def normalize(column):
    values = {}
    for parent, profile in column:
        if parent not in values or profile_compare(profile, values[parent]) > 0:
            values[parent] = profile
    return tuple(sorted(values.items(), reverse=True))


def controller(column):
    result = column[0]
    for candidate in column[1:]:
        relation = profile_compare(candidate[1], result[1])
        if relation > 0 or relation == 0 and candidate[0] > result[0]:
            result = candidate
    return result


def valid_tree(level, term, parent, child):
    if level == 0:
        return type(term) is int and (0 <= term <= parent or term == child)
    if term == ZERO:
        return True
    if not isinstance(term, tuple) or len(term) != 2:
        return False
    head, children = term
    return isinstance(children, tuple) and (head == CAP or valid_tree(level - 1, head, parent, child)) and all(
        valid_tree(level, t, parent, child) for t in children)


def tree_text(level, term, child):
    if level == 0:
        return "*" if term == child else str(term)
    if term == ZERO:
        return "."
    head, children = term
    h = "^" if head == CAP else tree_text(level - 1, head, child)
    if head != CAP and level > 1:
        h = "{" + h + "}"
    return h if not children else h + "(" + ",".join(tree_text(level, c, child) for c in children) + ")"


@total_ordering
@dataclass(frozen=True)
class IPD:
    columns: tuple | None = ()

    def __post_init__(self):
        if self.columns is None:
            return
        for child, column in enumerate(self.columns):
            for parent, (level, tree) in column:
                if not (type(parent) is int and 0 <= parent < child and type(level) is int and level >= 0):
                    raise ValueError("Invalid parent or tree level")
                if not valid_tree(level, tree, parent, child):
                    raise ValueError("Invalid ROOT/SELF tree")
        object.__setattr__(self, "columns", tuple(normalize(c) for c in self.columns))

    @classmethod
    def seed(cls, n):
        if type(n) is not int or n < 0:
            raise ValueError("A natural index is required")
        return cls(((), ((0, (n, 0 if n == 0 else ZERO)),)))

    def __lt__(self, other):
        if not isinstance(other, IPD):
            return NotImplemented
        if other.columns is None:
            return self.columns is not None
        if self.columns is None:
            return False
        for a, b in zip(self.columns, other.columns):
            for (pa, ta), (pb, tb) in zip(a, b):
                relation = (pa > pb) - (pa < pb) or profile_compare(ta, tb)
                if relation:
                    return relation < 0
            if len(a) != len(b):
                return len(a) < len(b)
        return len(self.columns) < len(other.columns)

    def fs(self, index, tick=lambda: None):
        if type(index) is not int or index < 0:
            raise ValueError("A natural index is required")
        if self.columns is None:
            return self.seed(index)
        if not self.columns:
            return self
        if index == 0 or not self.columns[-1]:
            return IPD(self.columns[:-1])
        last = len(self.columns) - 1
        cut, _ = controller(self.columns[-1])
        width = last - cut
        result = [[] for _ in range(last + index * width)]
        for child in range(cut):
            result[child].extend(self.columns[child])
        for block in range(index + 1):
            mapping = lambda k: k if k < cut else k + block * width
            for child in range(cut, last):
                tick()
                result[mapping(child)].extend((mapping(p), move_profile(t, mapping)) for p, t in self.columns[child])
            if block == index:
                break
            for parent, profile in self.columns[-1]:
                shifted = move_profile(profile, mapping)
                if parent == cut:
                    shifted = profile_lower(shifted, mapping(parent), mapping(last), block, tick)
                if shifted is not None:
                    result[mapping(last)].append((mapping(parent), shifted))
        return IPD(result)

    def local_step(self, tick=lambda: None):
        """Keep the left prefix frozen; discard newly appended columns."""
        if self.columns is None:
            raise ValueError("The external TOP has no fixed-column local step")
        if not self.columns or not self.columns[-1]:
            return IPD(self.columns[:-1])
        child = len(self.columns) - 1
        cut, profile = controller(self.columns[-1])
        lower = profile_lower(profile, cut, child, 0, tick)
        column = [(p, t) for p, t in self.columns[-1] if p != cut]
        if lower is not None:
            column.append((cut, lower))
        column.extend((p, move_profile(t, lambda k: child if k == cut else k)) for p, t in self.columns[cut])
        return IPD((*self.columns[:-1], column))

    def __str__(self):
        if self.columns is None:
            return "Limit of IPD"
        return "".join("[" + ";".join(f"{p}:{d}/{tree_text(d,t,j)}" for p, (d,t) in column) + "]"
                       for j, column in enumerate(self.columns)) or "0"


TOP = IPD(None)
