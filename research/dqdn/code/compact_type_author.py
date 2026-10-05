"""Reuse existing type facts when recording an unchanged source program.

This is a bounded compiler experiment, not a change to DQDN's 28 rules.
Every shortcut is replayed through an existing type_of or weaken_type rule.
"""

import json
import unittest

import check_dqdn_seeds as s
import dqdn
import typed_builder as tb
import ordinal_tree_macros as m
import compact_iteration_seeds as c


def remove_unused_binder(typ, depth=0):
    tag = typ[0]
    if tag == "nat":
        return typ
    if tag == "tv":
        if typ[1] == depth:
            return None
        return tag, typ[1] - (typ[1] > depth)
    if tag == "all":
        body = remove_unused_binder(typ[1], depth + 1)
        return None if body is None else (tag, body)
    left = remove_unused_binder(typ[1], depth)
    right = remove_unused_binder(typ[2], depth)
    return None if left is None or right is None else (tag, left, right)


class TypeReuseAuthor(m.RecordingAuthor):
    def __init__(self, terms, level=1):
        super().__init__(terms, level)
        self.type_nodes = {}
        self.facts = {}
        self.witnesses = {}
        for entry in self.t.available(self.library, "type"):
            self.index_fact(entry)
        for entry in self.t.available(self.library, "term"):
            self.index_fact(entry)

    def index_fact(self, entry):
        tag = self.t.data[entry][0]
        if tag == "tp":
            delta, _, value = self.t.parts(entry, tag)
            self.facts[delta, value] = entry
        elif tag == "ep":
            context, value, _ = self.t.parts(entry, tag)
            delta = self.t.parts(context, "ct")[0]
            self.witnesses[delta, value] = entry

    def do(self, rule, *args):
        entry = super().do(rule, *args)
        self.index_fact(entry)
        return entry

    def node(self, typ):
        if typ not in self.type_nodes:
            tag = typ[0]
            if tag == "nat":
                node = self.t.make("tn")
            elif tag == "tv":
                node = self.t.make("tx", typ[1])
            elif tag == "arr":
                node = self.t.make("ta", self.node(typ[1]), self.node(typ[2]))
            elif tag == "all":
                node = self.t.make("tf", self.t.make("ks"), self.node(typ[1]))
            else:
                raise ValueError("outside the bounded System F type grammar")
            self.type_nodes[typ] = node
        return self.type_nodes[typ]

    def direct_cost(self, typ, delta):
        self.t.budget.tick()
        if (delta, self.node(typ)) in self.facts:
            return 0
        tag = typ[0]
        if tag == "nat":
            return 3
        if tag == "tv":
            return 4
        if tag == "arr":
            return 4 + sum(self.direct_cost(a, delta) for a in typ[1:])
        child = self.t.make("kc", self.t.make("ks"), delta)
        return 3 + self.direct_cost(typ[1], child)

    def typ(self, typ, delta):
        key = typ, delta
        if key in self.type_cache:
            return self.type_cache[key]
        value = self.node(typ)
        entry = self.facts.get((delta, value))
        if entry is None:
            direct = self.direct_cost(typ, delta)
            witness = self.witnesses.get((delta, value))
            if witness is not None and direct >= 3:
                entry = self.do("type_of", witness)
            elif self.t.data[delta][0] == "kc" and direct > 4:
                kind, parent = self.t.parts(delta, "kc")
                earlier = remove_unused_binder(typ)
                premise = None if earlier is None else self.facts.get((parent, self.node(earlier)))
                if premise is not None:
                    entry = self.do("weaken_type", premise, kind)
        if entry is None:
            entry = super().typ(typ, delta)
        assert self.t.parts(entry, "tp")[::2] == [delta, value]
        self.type_cache[key] = entry
        return entry


def inspect(name, source):
    assert s.infer(source) == s.N
    t = tb.Terms(dqdn.Budget(seconds=12, nodes=150000, operations=5000000))
    author = TypeReuseAuthor(t)
    context = t.available(author.library, "ctx")[0]
    proof = author.term(source, context)
    expected = s.erase(source, t)
    assert t.parts(proof, "ep")[2] == expected
    fuel = len(author.choices)
    t.budget = dqdn.Budget(seconds=12, nodes=150000, operations=5000000)
    current = t.builder(1, fuel, t.initial_library())
    for answer in author.choices:
        current = t.builder_child(current, answer)
    assert t.builder_child(current, 0) == expected
    shortcuts = {rule: sum(1 for r, _ in author.actions if r == rule)
                 for rule in ("type_of", "weaken_type")}
    return {"name": name, "fuel": fuel, "carrier": 2*fuel+2,
            "actions": len(author.actions), "shortcuts": shortcuts,
            "literal_source_unchanged": True, "fields_replayed": True}


class ReuseTests(unittest.TestCase):
    def test_binder_removal(self):
        self.assertIsNone(remove_unused_binder(s.A))
        self.assertEqual(remove_unused_binder(("tv", 1)), s.A)
        self.assertEqual(remove_unused_binder(s.CN), s.CN)

    def test_compact_sources(self):
        for name, source, previous in (("epsilon", c.EPSILON_SOURCE, 145),
                ("zeta", c.ZETA_SOURCE, 261), ("Gamma", c.GAMMA_SOURCE, 441)):
            self.assertLessEqual(inspect(name, source)["fuel"], previous)


if __name__ == "__main__":
    import buchholz_tree_macros as b
    samples = [("epsilon", c.EPSILON_SOURCE), ("zeta", c.ZETA_SOURCE),
               ("Gamma", c.GAMMA_SOURCE),
               ("BHO", b.compact_bho_program(inline_once=True))]
    for name, source in samples:
        print(json.dumps(inspect(name, source), ensure_ascii=False), flush=True)
