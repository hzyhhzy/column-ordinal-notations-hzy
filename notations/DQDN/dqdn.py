"""Demand Query Diagram Notation: deterministic demand, countable queries.

Data: v(k), n(k), lambda(i), app(i,j), succ(i), rec(z,s,n), query(i).
The query node evaluates its index before choosing an arbitrary natural.
All ordinary envelope laws are inherited from the generic LCDN machinery.
This file does not implement the global typed-generator family.
"""

import lcdn
import lqdn

Budget = lcdn.Budget
ResourceLimit = lcdn.ResourceLimit
counts = lcdn.counts
compare = lcdn.compare
decode = lcdn.decode
emit_data = lcdn.emit_data
append_program = lcdn.append_program


class Terms(lqdn.Terms):
    atom_arities = {"v": 1, "n": 1}
    pointer_arities = {"l": 1, "a": 2, "s": 1, "r": 3, "q": 1}

    def demand(self, root):
        """Find the next weak-head demand; never normalize a whole program."""
        node, path = root, []
        while True:
            self.budget.tick()
            tag, *args = self.data[node]
            if tag == "a":
                if self.data[args[0]][0] == "l":
                    return node, path
                side = 0
            elif tag in ("s", "q", "r"):
                side = 2 if tag == "r" else 0
                if self.data[args[side]][0] == "n":
                    return node, path
            else:
                return None
            path.append((node, side))
            node = args[side]

    def reducible(self, root):
        return self.demand(root) is not None

    def redex_count(self, root):
        """There is at most one permitted demand position, not all redexes."""
        return int(self.reducible(root))

    def contract(self, node, choice):
        tag, *args = self.data[node]
        if tag == "q":
            if self.data[args[0]][0] != "n":
                return None
            return self.numeral(choice)
        return super().contract(node, choice)

    def computation_child(self, root, index):
        selected = self.demand(root)
        if selected is None:
            raise ValueError("the source is a demand normal form")
        node, path = selected
        # 0; 0,1; 0,1,2; ... repeats every possible answer infinitely often.
        choice = lcdn.base.fair_index(index)
        child = self.contract(node, choice)
        if child is None:
            raise AssertionError("selected demand is not a redex")
        for parent, side in reversed(path):
            tag, *args = self.data[parent]
            args[side] = child
            child = self.make(tag, *args)
        return child


def expand(columns, n, budget=None):
    return lcdn.expand(columns, n, budget, term_type=Terms)


def primitives(terms):
    """Uniform programs used by the proof examples, not kernel cases."""
    zero = terms.numeral(0)
    q = terms.make("q", zero)
    v0 = terms.make("v", 0)
    identity_step = terms.make("l", terms.make("l", v0))
    # J(x) makes a query before returning the unevaluated x.
    j = terms.make("l", terms.make("r", v0, identity_step, q))
    # F(f)(x) chooses a number and iterates f that many times on x.
    step = terms.make("l", terms.make("l", terms.make("a", terms.make("v", 3), v0)))
    f = terms.make("l", terms.make("l", terms.make("r", v0, step, q)))
    church_zero = terms.make("l", terms.make("l", v0))
    return zero, q, j, f, church_zero


def finite_tower(terms, height):
    zero, _, j, f, _ = primitives(terms)
    if height < 1:
        return terms.make("a", j, zero)
    chain = f
    for _ in range(height - 1):
        chain = terms.make("a", chain, f)
    return terms.make("a", terms.make("a", chain, j), zero)


def epsilon_seed(terms):
    """A warmed-up uniform iteration: the next actual action is a query.

    rec Church0 (lambda k. lambda x. x F) (query 0) J 0.
    Exact epsilon0 is a paper claim in the separate DQDN proof, not a test.
    """
    zero, q, j, f, church_zero = primitives(terms)
    v0 = terms.make("v", 0)
    step = terms.make("l", terms.make("l", terms.make("a", v0, f)))
    iterator = terms.make("r", church_zero, step, q)
    return terms.make("a", terms.make("a", iterator, j), zero)


OMEGA = (("n", 0), ("q", 0), ("run", 1))
