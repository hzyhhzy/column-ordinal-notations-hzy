"""Decode the unique STANDARD SPD with given positive local counts.

This is not an inverse on raw diagrams: raw count collisions are expected.
InvalidCounts means a proved rejection. TimeoutError / OverflowError mean
only that the requested resource allowance was exhausted.
"""
import spd


class InvalidCounts(ValueError):
    """No standard SPD has the supplied count word."""


def column_bound(column):
    """Uniform bound over every legal column, independent of its prefix."""
    return 1 + sum((p + 3) * (p + 1) ** 2 for p in range(column))


def decode_counts(values, *, budget=None, max_width=32, max_d_steps=100000,
                  stats=None):
    """Return canonical integer columns, or raise a distinguished exception.

    The empty word denotes the empty graph. Defaults share one ordinary SPD
    Budget across ALL operations: 15 seconds / 2,000,000 events, plus that
    Budget's allocation limits. There are at most m phases and sum O(j^4)
    frozen local D steps, but this does not assert a practical runtime bound.
    """
    if not isinstance(values, (tuple, list)):
        raise InvalidCounts('Counts must be a list or tuple of positive integers')
    if any(type(n) is not int or n <= 0 for n in values):
        raise InvalidCounts('Each count must be a positive integer, not bool')
    if type(max_width) is not int or max_width < 0:
        raise ValueError('max_width must be a nonnegative integer')
    if type(max_d_steps) is not int or max_d_steps < 0:
        raise ValueError('max_d_steps must be a nonnegative integer')
    m = len(values)
    if m > max_width:
        raise OverflowError('SPD count decoder width allowance exhausted')
    for j, n in enumerate(values):
        if n > column_bound(j):
            raise InvalidCounts(f'Count exceeds every legal column bound at {j}')
    if stats is not None:
        stats.update(width=m, phases=0, local_d_steps=0,
                     theoretical_d_bound=sum(column_bound(j) for j in range(m)))
    if not m:
        return ()
    budget = spd.Budget() if budget is None else budget
    current = spd.seed(m-1, budget)
    steps = phases = 0
    for j, wanted in enumerate(values):
        budget.tick()
        if len(current) <= j:
            raise InvalidCounts(f'No standard extension at count position {j}')
        have = spd.counts(current, budget)[j]
        if have < wanted:
            raise InvalidCounts(f'Count word lies above the remaining standard cone at {j}')
        if have == wanted:
            continue
        current = current[:j+1]  # Exact finite [0] path.
        while have > wanted+1:
            if steps >= max_d_steps:
                raise OverflowError('SPD count decoder local-D allowance exhausted')
            current = spd.fs(current, 1, budget)[:j+1]
            have -= 1
            steps += 1
            if stats is not None:
                stats['local_d_steps'] = steps
        # Each block has at least L+1 columns (seam plus pure source), so
        # this smaller index already reaches m. Its prefix is exactly T_m.
        cut = spd.read(current, budget).control()[1]
        block_minimum = j-cut+1
        index = max(1,(m-j+block_minimum-1)//block_minimum)
        current = spd.fs(current, index, budget)[:m]
        phases += 1
        if stats is not None:
            stats['phases'] = phases
    assert len(current) == m
    assert spd.counts(current, budget) == tuple(values)
    return current


def is_standard(graph, *, budget=None, max_width=32, max_d_steps=100000):
    """Decide raw membership by comparing with its unique standard count twin.

    Illegal graph structure raises ValueError. Resource exceptions propagate;
    False is reserved for a proved nonstandard normalized graph.
    """
    budget = spd.Budget() if budget is None else budget
    canonical = spd.normalize(graph,budget)
    values = spd.counts(canonical,budget)
    try:
        decoded = decode_counts(values,budget=budget,max_width=max_width,
                                max_d_steps=max_d_steps)
    except InvalidCounts:
        return False
    return canonical == decoded


if __name__ == '__main__':
    details = {}
    value = decode_counts((1,3,16), stats=details)
    print({'counts':spd.counts(value),'columns':value,'decoder':details})
