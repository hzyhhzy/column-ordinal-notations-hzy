"""Bounded checks for the infinite chain proved in ICP-NOT-WELL-FOUNDED.

Uses the original, unchanged ICP kernel. Finite tests supplement the paper
induction; they are not the reason the chain is known to be infinite.
"""

from random import Random
from time import monotonic

from icp import Budget, Pattern, column, counts, display, expand, reflect, seed, validate


STEPS = 100
DEADLINE_SECONDS = 15


def tail(c: int) -> Pattern:
    return (
        ((c, c),),
        ((c + 1, c + 1), (c, c + 1)),
        ((c + 2, c + 1), (c + 1, c + 1), (c, c + 2)),
    )


def predicted_reflection(prefix: Pattern) -> Pattern:
    """Closed formula, independent of lower/reflect/expand."""
    c = len(prefix) - 1
    x = c + 3
    lowered = (
        (c + 2, c + 1), (c + 1, c + 1), (c, c + 1),
        *prefix[-1],
    )
    copied_tail = tail(x)
    # The interpolation replaces the existing root at parent x+1.
    work = ((x + 2, x + 1), (x + 1, x + 3), (x, x + 2))
    return prefix + tail(c)[:2] + (lowered,) + copied_tail + (work,)


def check_renewal(prefix: Pattern) -> Pattern:
    c = len(prefix) - 1
    a = prefix + tail(c)
    validate(a)
    expected = predicted_reflection(prefix)
    validate(expected)
    trace = []
    actual = reflect(a, Budget(), trace)
    assert actual == expected, (c, display(a))
    assert trace == [
        {"origin": c + 1, "start": c + 4, "end": c + 4, "ancestors": []},
        {"origin": c + 2, "start": c + 5, "end": c + 5, "ancestors": []},
        {"origin": c + 3, "start": c + 6, "end": c + 7, "ancestors": [c + 4]},
    ], trace
    b = expand(a, 1, Budget())
    assert b == expected[:-1]
    assert len(b) == len(a) + 3
    assert b < a
    assert b[-3:] == tail(c + 3)
    return b


def main() -> None:
    start = monotonic()

    def deadline() -> None:
        if monotonic() - start > DEADLINE_SECONDS:
            raise RuntimeError("Bounded verification reached its time limit.")

    a = seed(3)
    for n in (1, 1, 0):
        a = expand(a, n, Budget())
    assert a == ((),) + tail(0)
    assert counts(a, Budget()) == (1, 2, 5, 10)
    print("Standard start: Top[3][1][1][0] =", display(a))
    print("Initial counts:", counts(a, Budget()))

    for t in range(STEPS):
        deadline()
        assert len(a) == 3 * t + 4
        assert a[-3:] == tail(3 * t)
        b = check_renewal(a[:-3])
        if t < 3:
            print(f"A_{t + 1}: {len(b)} columns; tail {display(b[-3:])}")
        a = b

    # Prefixes here need only be syntactically valid. The paper lemma is
    # universal in the prefix, whereas the preceding chain is standard.
    rng = Random(20260919)
    prefix_cases = 0
    for c in range(24):
        for _ in range(8):
            deadline()
            prefix = tuple(
                column((p, rng.randrange(j)) for p in range(j) if rng.randrange(3))
                for j in range(c + 1)
            )
            check_renewal(prefix)
            prefix_cases += 1

    print(f"Verified {STEPS} standard-chain steps and {prefix_cases} arbitrary-prefix cases.")
    print(f"Final width: {len(a)}; elapsed: {monotonic() - start:.3f}s.")
    print("The all-step result is the symbolic renewal lemma, not this finite run.")


if __name__ == "__main__":
    main()
