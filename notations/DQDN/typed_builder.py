"""Incremental F-omega typing laboratory for the DQDN global generator.

All stored objects are immutable small DAG nodes.  There is no complete type
normalizer: a conversion command contracts one explicitly addressed beta/eta
redex.  A bad construction ends that branch; it never starts a proof search.

This is a research implementation, not a kernel-verified type checker.
"""

import dqdn


class BadConstruction(ValueError):
    pass


def need(condition, message="inapplicable construction"):
    if not condition:
        raise BadConstruction(message)


def fair_choice(index):
    """Every m first occurs by 2m+1 and occurs infinitely often."""
    shifted = index + 2
    trailing = (shifted & -shifted).bit_length() - 1
    odd_part = shifted >> trailing
    return max(0, (odd_part - 3) // 2)


# Each argument is one independent field, not a packed program number.
RULES = (
    ("kind_arrow", ("kind", "kind")),
    ("kind_context", ("kctx", "kind")),
    ("term_context", ("kctx",)),
    ("extend_context", ("ctx", "type")),
    ("lift_context", ("ctx", "kind")),
    ("nat_type", ("kctx",)),
    ("type_variable", ("kctx", "number")),
    ("type_arrow", ("type", "type")),
    ("type_forall", ("type",)),
    ("type_lambda", ("type",)),
    ("type_application", ("type", "type")),
    ("weaken_type", ("type", "kind")),
    ("variable", ("ctx", "number")),
    ("number", ("ctx", "number")),
    ("lambda", ("term",)),
    ("application", ("term", "term")),
    ("polymorphic", ("term",)),
    ("instantiate", ("term", "type")),
    ("successor", ("term",)),
    ("query", ("term",)),
    ("recursor", ("term", "term", "term")),
    ("type_of", ("term",)),
    ("equality_refl", ("type",)),
    ("equality_sym", ("equal",)),
    ("equality_trans", ("equal", "equal")),
    ("type_beta", ("type", "number")),
    ("type_eta", ("type", "number")),
    ("convert", ("term", "equal")),
)

SORT_TAGS = {
    "kind": {"ks", "kk"}, "kctx": {"ke", "kc"},
    "ctx": {"ct"}, "type": {"tp"}, "term": {"ep"},
    "equal": {"eq"},
}

TOP = (("top",),)


class Terms(dqdn.Terms):
    atom_arities = {**dqdn.Terms.atom_arities,
                    "nil": 0, "ks": 0, "ke": 0, "tn": 0,
                    "tx": 1, "g": 1}
    pointer_arities = {**dqdn.Terms.pointer_arities,
                       "kk": 2, "kc": 2, "ct": 2, "dl": 2,
                       "ta": 2, "tf": 2, "tl": 2, "tt": 2,
                       "tp": 3, "ep": 3, "eq": 2, "li": 2,
                       "bp": 2, "bf": 2, "al": 2, "b": 3}

    def __init__(self, budget):
        super().__init__(budget)
        self.kind_heights = {}
        self.type_walks = {}

    def parts(self, node, tag=None):
        self.budget.tick()
        actual, *args = self.data[node]
        need(tag is None or tag == actual, "wrong object sort")
        return args

    def linked(self, node, tag, end="nil"):
        result = []
        while self.data[node][0] != end:
            value, node = self.parts(node, tag)
            result.append(value)
        return result

    def list_of(self, values, tag):
        result = self.make("nil")
        for value in reversed(values):
            result = self.make(tag, value, result)
        return result

    def kind_height(self, root):
        stack = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node in self.kind_heights:
                continue
            self.budget.tick()
            tag, *args = self.data[node]
            if tag == "ks":
                self.kind_heights[node] = 0
            elif tag == "kk" and not ready:
                stack.append((node, True))
                stack.extend((x, False) for x in args)
            elif tag == "kk":
                self.kind_heights[node] = 1 + max(self.kind_heights[x] for x in args)
            else:
                raise BadConstruction("not a kind")
        return self.kind_heights[root]

    def type_walk(self, root, parameter, substitute=False, depth=0):
        """One capture-avoiding type shift or type substitution, with DAG memo."""
        stack = [(root, depth, False)]
        key0 = (root, parameter, substitute, depth)
        while stack:
            node, level, ready = stack.pop()
            key = (node, parameter, substitute, level)
            if key in self.type_walks:
                continue
            self.budget.tick()
            tag, *args = self.data[node]
            if tag == "tn":
                result = node
            elif tag == "tx":
                index = args[0]
                if substitute and index == level:
                    result = self.type_walk(parameter, level)
                elif substitute:
                    result = self.make("tx", index - (index > level))
                else:
                    need(not (parameter < 0 and level <= index < level - parameter),
                         "type variable escapes its binder")
                    result = self.make("tx", index + parameter if index >= level else index)
            elif tag in ("ta", "tt", "tf", "tl"):
                binder = tag in ("tf", "tl")
                children = [args[1]] if binder else args
                if not ready:
                    stack.append((node, level, True))
                    stack.extend((x, level + binder, False) for x in reversed(children))
                    continue
                translated = [self.type_walks[(x, parameter, substitute, level + binder)]
                              for x in children]
                result = self.make(tag, args[0], translated[0]) if binder else self.make(tag, *translated)
            else:
                raise BadConstruction("not type syntax")
            self.type_walks[key] = result
        return self.type_walks[key0]

    def type_step(self, root, address, eta=False):
        """Address 0 is the root; binders have only a body at child zero."""
        directions = []
        address += 1
        while address > 1:
            self.budget.tick()
            directions.append(address & 1)
            address //= 2
        node, path = root, []
        for side in reversed(directions):
            tag, *args = self.data[node]
            if tag in ("tf", "tl"):
                need(side == 0)
                slot = 1
            else:
                need(tag in ("ta", "tt"))
                slot = side
            path.append((node, slot))
            node = args[slot]
        tag, *args = self.data[node]
        if eta:
            need(tag == "tl")
            function, variable = self.parts(args[1], "tt")
            need(self.data[variable] == ("tx", 0))
            result = self.type_walk(function, -1)
        else:
            need(tag == "tt")
            _, body = self.parts(args[0], "tl")
            result = self.type_walk(body, args[1], True)
        for parent, slot in reversed(path):
            tag, *args = self.data[parent]
            args[slot] = result
            result = self.make(tag, *args)
        return result

    def construct(self, rule, args, level):
        """One local rule. All premises came from this level's valid library."""
        nil, star, nat = self.make("nil"), self.make("ks"), self.make("tn")

        def tp(delta, kind, value):
            return self.make("tp", delta, kind, value)

        def ep(context, typ, value):
            return self.make("ep", context, typ, value)

        def same_context(proofs):
            decoded = [self.parts(x, "ep") for x in proofs]
            need(all(x[0] == decoded[0][0] for x in decoded))
            return decoded

        if rule == "kind_arrow":
            result = self.make("kk", *args)
            need(level > 0 and self.kind_height(result) < level)
            return result
        if rule == "kind_context":
            need(level > 0)
            return self.make("kc", args[1], args[0])
        if rule == "term_context":
            return self.make("ct", args[0], nil)
        if rule in ("extend_context", "lift_context"):
            delta, declarations = self.parts(args[0], "ct")
            if rule == "extend_context":
                delta2, kind, typ = self.parts(args[1], "tp")
                need(delta == delta2 and kind == star)
                declarations = self.make("dl", typ, declarations)
            else:
                need(level > 0)
                delta = self.make("kc", args[1], delta)
                declarations = self.list_of(
                    [self.type_walk(a, 1) for a in self.linked(declarations, "dl")], "dl")
            return self.make("ct", delta, declarations)
        if rule == "nat_type":
            return tp(args[0], star, nat)
        if rule == "type_variable":
            kinds = self.linked(args[0], "kc", "ke")
            index = self.parts(args[1], "n")[0]
            need(index < len(kinds))
            return tp(args[0], kinds[index], self.make("tx", index))
        if rule in ("type_arrow", "type_application"):
            d1, k1, a1 = self.parts(args[0], "tp")
            d2, k2, a2 = self.parts(args[1], "tp")
            need(d1 == d2)
            if rule == "type_arrow":
                need(k1 == k2 == star)
                return tp(d1, star, self.make("ta", a1, a2))
            domain, codomain = self.parts(k1, "kk")
            need(domain == k2)
            return tp(d1, codomain, self.make("tt", a1, a2))
        if rule in ("type_forall", "type_lambda"):
            delta, kind, typ = self.parts(args[0], "tp")
            parameter_kind, parent = self.parts(delta, "kc")
            if rule == "type_forall":
                need(kind == star)
                return tp(parent, star, self.make("tf", parameter_kind, typ))
            result_kind = self.make("kk", parameter_kind, kind)
            need(level > 0 and self.kind_height(result_kind) < level)
            return tp(parent, result_kind, self.make("tl", parameter_kind, typ))
        if rule == "weaken_type":
            need(level > 0)
            delta, kind, typ = self.parts(args[0], "tp")
            return tp(self.make("kc", args[1], delta), kind, self.type_walk(typ, 1))
        if rule in ("variable", "number"):
            delta, declarations = self.parts(args[0], "ct")
            value = self.parts(args[1], "n")[0]
            if rule == "number":
                return ep(args[0], nat, args[1])
            types = self.linked(declarations, "dl")
            need(value < len(types))
            return ep(args[0], types[value], self.make("v", value))
        if rule == "lambda":
            context, typ, value = self.parts(args[0], "ep")
            delta, declarations = self.parts(context, "ct")
            domain, parent = self.parts(declarations, "dl")
            return ep(self.make("ct", delta, parent), self.make("ta", domain, typ),
                      self.make("l", value))
        if rule == "application":
            f, x = same_context(args)
            domain, codomain = self.parts(f[1], "ta")
            need(domain == x[1])
            return ep(f[0], codomain, self.make("a", f[2], x[2]))
        if rule == "polymorphic":
            context, typ, value = self.parts(args[0], "ep")
            delta, declarations = self.parts(context, "ct")
            kind, parent = self.parts(delta, "kc")
            old = self.list_of([self.type_walk(a, -1)
                                for a in self.linked(declarations, "dl")], "dl")
            return ep(self.make("ct", parent, old), self.make("tf", kind, typ), value)
        if rule == "instantiate":
            context, typ, value = self.parts(args[0], "ep")
            kind, body = self.parts(typ, "tf")
            delta, actual_kind, argument = self.parts(args[1], "tp")
            need(delta == self.parts(context, "ct")[0] and kind == actual_kind)
            return ep(context, self.type_walk(body, argument, True), value)
        if rule in ("successor", "query"):
            context, typ, value = self.parts(args[0], "ep")
            need(typ == nat)
            return ep(context, nat, self.make("s" if rule == "successor" else "q", value))
        if rule == "recursor":
            z, s, n = same_context(args)
            need(n[1] == nat and s[1] == self.make("ta", nat, self.make("ta", z[1], z[1])))
            return ep(z[0], z[1], self.make("r", z[2], s[2], n[2]))
        if rule == "type_of":
            context, typ, _ = self.parts(args[0], "ep")
            return tp(self.parts(context, "ct")[0], star, typ)
        if rule == "equality_refl":
            return self.make("eq", args[0], args[0])
        if rule == "equality_sym":
            left, right = self.parts(args[0], "eq")
            return self.make("eq", right, left)
        if rule == "equality_trans":
            left, middle1 = self.parts(args[0], "eq")
            middle2, right = self.parts(args[1], "eq")
            need(middle1 == middle2)
            return self.make("eq", left, right)
        if rule in ("type_beta", "type_eta"):
            delta, kind, typ = self.parts(args[0], "tp")
            address = self.parts(args[1], "n")[0]
            result = self.type_step(typ, address, rule == "type_eta")
            return self.make("eq", args[0], tp(delta, kind, result))
        if rule == "convert":
            context, typ, value = self.parts(args[0], "ep")
            left, right = self.parts(args[1], "eq")
            delta, kind, source = self.parts(left, "tp")
            delta2, kind2, target = self.parts(right, "tp")
            need(delta == delta2 == self.parts(context, "ct")[0]
                 and kind == kind2 == star and typ == source)
            return ep(context, target, value)
        raise BadConstruction("unknown rule")

    def initial_library(self):
        nil, delta, star, nat = (self.make(t) for t in ("nil", "ke", "ks", "tn"))
        context = self.make("ct", delta, nil)
        entries = [star, delta, context, self.make("tp", delta, star, nat),
                   self.make("ep", context, nat, self.numeral(0))]
        result = nil
        for entry in entries:
            result = self.make("li", entry, result)
        return result

    def available(self, library, sort):
        """Facts and their well-formed contexts/kinds, in structural DFS order.

        This order does not depend on incidental hash-cons node numbers or on
        unrelated earlier columns.  Derived contexts need not be re-proved.
        """
        stack, seen, result = [library], set(), []
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            self.budget.tick()
            seen.add(node)
            if self.data[node][0] in SORT_TAGS[sort]:
                result.append(node)
            stack.extend(reversed(self.children(node)))
        return result

    def builder(self, level, fuel, library, pending=None):
        pending = self.make("nil") if pending is None else pending
        return self.make("b", self.numeral(level), self.numeral(fuel),
                         self.make("bf", library, pending))

    def builder_child(self, root, choice):
        if self.data[root][0] == "g":
            return self.builder(self.data[root][1], choice, self.initial_library())
        level_node, fuel_node, frame = self.parts(root, "b")
        level, fuel = self.parts(level_node, "n")[0], self.parts(fuel_node, "n")[0]
        library, pending = self.parts(frame, "bf")
        entries = self.linked(library, "li")
        if fuel == 0:
            for entry in entries:
                if self.data[entry][0] != "ep":
                    continue
                context, typ, value = self.parts(entry, "ep")
                delta, declarations = self.parts(context, "ct")
                if (self.data[delta][0] == "ke" and self.data[declarations][0] == "nil"
                        and self.data[typ][0] == "tn"):
                    return value
            return self.numeral(0)
        if self.data[pending][0] == "nil":
            pending = self.make("bp", self.numeral(choice % len(RULES)), self.make("nil"))
        else:
            rule_node, arguments = self.parts(pending, "bp")
            rule, sorts = RULES[self.parts(rule_node, "n")[0]]
            chosen = list(reversed(self.linked(arguments, "al")))
            if len(chosen) < len(sorts):
                sort = sorts[len(chosen)]
                if sort == "number":
                    argument = self.numeral(choice)
                else:
                    candidates = self.available(library, sort)
                    if not candidates:
                        return self.numeral(0)
                    argument = candidates[choice % len(candidates)]
                pending = self.make("bp", rule_node, self.make("al", argument, arguments))
            else:
                try:
                    entry = self.construct(rule, chosen, level)
                except BadConstruction:
                    return self.numeral(0)
                library = self.make("li", entry, library)
                pending = self.make("nil")
        return self.builder(level, fuel - 1, library, pending)

    def demand(self, root):
        if self.data[root][0] in ("g", "b"):
            return root, []
        return super().demand(root)

    def computation_child(self, root, index):
        choice = fair_choice(index)
        if self.data[root][0] in ("g", "b"):
            return self.builder_child(root, choice)
        selected = self.demand(root)
        if selected is None:
            raise ValueError("the source is a demand normal form")
        node, path = selected
        child = self.contract(node, choice)
        for parent, side in reversed(path):
            tag, *args = self.data[parent]
            args[side] = child
            child = self.make(tag, *args)
        return child


def expand(columns, n, budget=None):
    if type(n) is not int or n < 0:
        raise ValueError("the basic-sequence index must be natural")
    if columns == TOP:
        return () if n == 0 else root(n - 1, budget)
    return dqdn.lcdn.expand(columns, n, budget, term_type=Terms)


def root(level, budget=None):
    if type(level) is not int or level < 0:
        raise ValueError("the level must be a natural number")
    budget = budget or dqdn.Budget()
    result = []
    for k in range(level + 1):
        dqdn.lcdn.base.append_column(result, ("g", k), budget)
        dqdn.lcdn.base.append_column(result, ("run", 2 * k), budget)
    return tuple(result)


def counts(columns):
    return (2,) if columns == TOP else dqdn.counts(columns)


def compare(left, right):
    a, b = counts(left), counts(right)
    return (a > b) - (a < b)


def is_standard(columns, budget=None):
    """Decide the common prefix-root domain; do not merely check raw syntax.

    A resource exception means undecided within the budget, not nonstandard.
    Each successful iteration fixes at least one more column of the candidate.
    """
    budget = budget or dqdn.Budget()
    if columns == TOP:
        return True
    try:
        dqdn.decode(columns, Terms(budget))
    except ValueError:
        return False
    current = root(len(columns), budget)
    for _ in range(len(columns) + 1):
        common = 0
        while common < min(len(current), len(columns)) and current[common] == columns[common]:
            budget.tick()
            common += 1
        if common == len(columns):
            return True
        if common == len(current):
            return False
        if current[common][0] != "run" or columns[common][0] == "run":
            return False
        # More than enough of this node's infinite append stream to decide
        # the candidate's finite prefix. Later columns can always be deleted.
        current = expand(current[:common + 1], len(columns) - common, budget)
    raise AssertionError("standard-domain comparison failed to make progress")
