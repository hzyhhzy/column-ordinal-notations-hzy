"""Exact CSD local clocks and jumping; no whole-FS descent loop.

Caller must bound diagram size / integer lengths and supply a tick callback.
The clock formula is in definition.zh-CN.md, section 4; the archived
CSD manuscripts give its finite-workload justification.
"""
from csd import CSD, context_tail


class Clock:
    def __init__(self, prefix, tick=lambda: None):
        self.prefix, self.j, self.tick = prefix, len(prefix), tick
        self.base = self.j + 1
        self.recharge = [0]
        self.resets = []
        for col in prefix:
            tick()
            reset = context_tail(col, self.j)
            self.resets.append(reset)
            self.recharge.append(self.recharge[-1] + self.rank(reset) + 1)
        self.inherited = []
        self.sources = []
        for p, col in enumerate(prefix):
            tick()
            source = tuple((u, tuple(self.j if a == p else a for a in w)) for u, w in col)
            self.sources.append(source)
            self.inherited.append(self.work(source))

    def rank(self, tail):
        value = tail[0]
        for digit in tail[1:]:
            self.tick()
            value = self.base * (value + 1) + digit
        return value

    def unrank(self, value):
        length, offset, power = 1, 0, self.base
        while value >= offset + power:
            self.tick()
            offset += power
            power *= self.base
            length += 1
        value -= offset
        out = [0] * length
        for i in range(length-1, -1, -1):
            self.tick()
            value, out[i] = divmod(value, self.base)
        assert value == 0
        return tuple(out)

    def cost(self, word):
        return self.rank(word[1:]) + 1 + self.recharge[word[0]]

    def work(self, column):
        total = 0
        for p, word in column:
            self.tick()
            total += self.cost(word) * (1 + self.inherited[p])
        return total

    def advance_word(self, word, steps):
        assert 0 <= steps <= self.cost(word)
        head, tail = word[0], word[1:]
        while True:
            self.tick()
            rank = self.rank(tail)
            if steps <= rank:
                return (head, *self.unrank(rank-steps))
            steps -= rank+1
            if head == 0:
                assert steps == 0
                return None
            head -= 1
            tail = self.resets[head]

    def jump(self, column, steps):
        """Return T^steps(column) before empty-column deletion, via cycle skipping."""
        assert 0 <= steps <= self.work(column)
        bottom = list(column)
        while steps:
            self.tick()
            p, word = bottom[-1]
            period = 1 + self.inherited[p]
            total = self.cost(word) * period
            if steps >= total:
                steps -= total
                bottom.pop()
                continue
            cycles, remainder = divmod(steps, period)
            current = self.advance_word(word, cycles)
            if not remainder:
                bottom[-1] = (p, current)
                return tuple(bottom)
            lowered = self.advance_word(current, 1)
            if lowered is None:
                bottom.pop()
            else:
                bottom[-1] = (p, lowered)
            # Consume one control-word action; the remaining fragment is in C_p.
            bottom.extend(self.sources[p])
            steps = remainder-1
        return tuple(bottom)


def canonical_reach(target, tick=lambda: None, expand=lambda g, n: g[n]):
    """Prefix-entry algorithm from A_width; return an exact macro certificate.

    A negative result is a failed canonical entry. Its full mathematical
    completeness argument is separate from this implementation.
    """
    width = len(target.columns)
    current = CSD.seed(width)
    certificate = []
    for j in range(width):
        tick()
        assert current.columns[:j] == target.columns[:j]
        old, wanted = current.columns[j], target.columns[j]
        if old == wanted:
            continue
        clock = Clock(current.columns[:j], tick)
        old_work, target_work = clock.work(old), clock.work(wanted)
        if target_work >= old_work:
            return {'ok': False, 'column': j, 'reason': 'target-clock-not-lower',
                    'old': old, 'target': wanted, 'old_work': old_work,
                    'target_work': target_work, 'certificate': certificate}
        steps = old_work-target_work
        actual = clock.jump(old, steps)
        if actual != wanted:
            return {'ok': False, 'column': j, 'reason': 'target-not-on-local-trace',
                    'old': old, 'target': wanted, 'actual': actual,
                    'old_work': old_work, 'target_work': target_work,
                    'certificate': certificate}
        predecessor = clock.jump(old, steps-1)
        before = CSD((*current.columns[:j], predecessor))
        cut = predecessor[-1][0]
        block = j-cut
        n = max(1, (width-j+block-1)//block)
        after = expand(before, n)
        assert after.columns[j] == wanted
        certificate.append({'column': j, 'truncate_from': len(current.columns),
                            'local_steps': steps, 'last_index': n})
        current = after
    assert current.columns[:width] == target.columns
    return {'ok': True, 'certificate': certificate, 'final_truncations': len(current.columns)-width}
