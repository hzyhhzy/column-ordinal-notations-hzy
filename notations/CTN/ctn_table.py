"""CTN finite-table checker: fixed syntax, addresses, and local obligations.

This is the common logical table, not an obsolete notation frontend.
See definition.md. No proof search, model completion, or unbounded evaluation.
"""

from functools import lru_cache
from math import isqrt


ZERO, EQUAL, SUCC, ADD, MUL, MEMBER, NOT, AND, EXISTS_N, EXISTS_S = range(10)
MEMBERSHIP, TRUTH, WITNESS, COMPREHENSION, COMP_TEST, FORALL_TEST = range(6)


def pair(a, b):
    """Cantor pairing, with pair(0, 0) = 0."""
    return (a + b) * (a + b + 1) // 2 + b


def unpair(code):
    diagonal = (isqrt(8 * code + 1) - 1) // 2
    b = code - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def cons(head, tail):
    return 1 + pair(head, tail)


def encode_list(values):
    code = 0
    for value in reversed(values):
        code = cons(value, code)
    return code


@lru_cache(maxsize=4096)
def decode_list(code):
    values = []
    while code:
        head, code = unpair(code - 1)
        values.append(head)
    return tuple(values)


def formula(op, *arguments):
    """Encode a fixed-arity formula; variables are de Bruijn indices."""
    arity = {ZERO: 1, EQUAL: 2, SUCC: 2, ADD: 3, MUL: 3, MEMBER: 2,
             NOT: 1, AND: 2, EXISTS_N: 1, EXISTS_S: 1}[op]
    if len(arguments) != arity:
        raise ValueError("Wrong formula arity")
    payload = arguments[-1]
    for argument in reversed(arguments[:-1]):
        payload = pair(argument, payload)
    return pair(op, payload)


@lru_cache(maxsize=4096)
def scoped(code, number_count, set_count):
    """Syntactic scope checking, not truth evaluation."""
    op, data = unpair(code)
    if op == ZERO:
        return data < number_count
    if op in (EQUAL, SUCC, MEMBER):
        i, j = unpair(data)
        return i < number_count and j < (set_count if op == MEMBER else number_count)
    if op in (ADD, MUL):
        i, rest = unpair(data)
        j, k = unpair(rest)
        return max(i, j, k) < number_count
    if op == NOT:
        return scoped(data, number_count, set_count)
    if op == AND:
        left, right = unpair(data)
        return scoped(left, number_count, set_count) and scoped(right, number_count, set_count)
    if op == EXISTS_N:
        return scoped(data, number_count + 1, set_count)
    if op == EXISTS_S:
        return scoped(data, number_count, set_count + 1)
    return False


def context(code, numbers=(), sets=()):
    return pair(code, pair(encode_list(numbers), encode_list(sets)))


def truth_address(code, numbers_code, sets_code):
    return pair(TRUTH, pair(code, pair(numbers_code, sets_code)))


def membership_address(set_index, number):
    return pair(MEMBERSHIP, pair(set_index, number))


class Pending(Exception):
    """A required table entry has not yet been written."""


def check_entry(values, index):
    """Check one visible entry and its associated local obligation."""
    size = len(values)

    def read(address):
        if address >= size:
            raise Pending
        return values[address]

    kind, data = unpair(index)
    value = values[index]
    if kind == MEMBERSHIP:
        return value in (0, 1)
    if kind > FORALL_TEST:
        return value == 0
    if kind in (COMP_TEST, FORALL_TEST):
        if value != 0:
            return False
        payload, number = unpair(data)
    else:
        payload, number = data, None
    code, environment = unpair(payload)
    numbers_code, sets_code = unpair(environment)
    numbers, sets = decode_list(numbers_code), decode_list(sets_code)
    extra = int(kind in (COMPREHENSION, COMP_TEST))
    if not scoped(code, len(numbers) + extra, len(sets)):
        return value == 0
    op, body = unpair(code)

    def truth(child, ns=numbers_code, ss=sets_code):
        return read(truth_address(child, ns, ss))

    def instance(argument):
        if op == EXISTS_N:
            return truth(body, cons(argument, numbers_code), sets_code)
        return truth(body, numbers_code, cons(argument, sets_code))

    if kind == COMPREHENSION:
        return True
    if kind == WITNESS:
        return op in (EXISTS_N, EXISTS_S) or value == 0
    if kind == COMP_TEST:
        row = read(pair(COMPREHENSION, payload))
        return read(membership_address(row, number)) == truth(code, cons(number, numbers_code), sets_code)
    if kind == FORALL_TEST:
        if op not in (EXISTS_N, EXISTS_S) or truth(code) == 1:
            return True
        return instance(number) == 0
    if value not in (0, 1):
        return False
    if op == ZERO:
        return value == int(numbers[body] == 0)
    if op in (EQUAL, SUCC, MEMBER):
        i, j = unpair(body)
        if op == MEMBER:
            expected = read(membership_address(sets[j], numbers[i]))
        elif op == EQUAL:
            expected = int(numbers[i] == numbers[j])
        else:
            expected = int(numbers[i] + 1 == numbers[j])
        return value == expected
    if op in (ADD, MUL):
        i, rest = unpair(body)
        j, k = unpair(rest)
        result = numbers[i] + numbers[j] if op == ADD else numbers[i] * numbers[j]
        return value == int(result == numbers[k])
    if op == NOT:
        return value == 1 - truth(body)
    if op == AND:
        left, right = unpair(body)
        return value == (truth(left) & truth(right))
    if value == 0:
        return True
    return instance(read(pair(WITNESS, payload))) == 1


def table_ok(values):
    """Membership in the concrete tree of finite consistent tables."""
    if any(not isinstance(value, int) or value < 0 for value in values):
        return False
    for index in range(len(values)):
        try:
            if not check_entry(values, index):
                return False
        except Pending:
            pass
    return True
