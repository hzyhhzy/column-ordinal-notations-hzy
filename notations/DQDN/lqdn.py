"""Lambda Query Diagram Notation: native-number comparison backend.

Uses the same column envelope as LCDN, but Q chooses a native number.
Extra data nodes: ('n', k), ('s', i), ('r', zero, step, number).
This is a research kernel, not a completed global root/certificate enumerator.
"""

import lcdn

Budget = lcdn.Budget
ResourceLimit = lcdn.ResourceLimit
OMEGA = lcdn.OMEGA
counts = lcdn.counts
compare = lcdn.compare
decode = lcdn.decode
emit_data = lcdn.emit_data
append_program = lcdn.append_program


class Terms(lcdn.Terms):
    atom_arities = {**lcdn.Terms.atom_arities, "n": 1}
    pointer_arities = {**lcdn.Terms.pointer_arities, "s": 1, "r": 3}

    def numeral(self, n):
        return self.make("n", n)

    def is_redex(self, node):
        tag, *args = self.data[node]
        return (super().is_redex(node) or
                tag == "s" and self.data[args[0]][0] == "n" or
                tag == "r" and self.data[args[2]][0] == "n")

    def contract(self, node, choice):
        tag, *args = self.data[node]
        if tag == "s" and self.data[args[0]][0] == "n":
            return self.numeral(self.data[args[0]][1] + 1)
        if tag == "r" and self.data[args[2]][0] == "n":
            zero, step, number = args
            n = self.data[number][1]
            if n == 0:
                return zero
            previous = self.numeral(n - 1)
            residual = self.make("r", zero, step, previous)
            return self.make("a", self.make("a", step, previous), residual)
        return super().contract(node, choice)


def expand(columns, n, budget=None):
    return lcdn.expand(columns, n, budget, term_type=Terms)


def church_choice(terms):
    """The uniform macro ΛA.λf.λx.rec x (λk.λv.f v) Q.

    Type abstractions erase. This is an ordinary program, not a rewrite rule.
    """
    q = terms.make("q")
    x = terms.make("v", 0)
    f_under_step = terms.make("v", 3)
    step = terms.make("l", terms.make("l", terms.make("a", f_under_step, x)))
    return terms.make("l", terms.make("l", terms.make("r", x, step, q)))


def tower_seed(terms):
    q = church_choice(terms)
    x = terms.make("v", 0)
    identity = terms.make("l", x)
    zero = terms.make("l", identity)
    # q is closed, so placing it under another λ needs no index shift.
    right_q = terms.make("l", terms.make("a", x, q))
    iterator = terms.make("a", terms.make("a", q, right_q), zero)
    return terms.make("a", terms.make("a", iterator, identity), zero)
