"""Finite checks of CTN; these are not tests of Church--Kleene strength."""

from itertools import product
import json
import random
from time import perf_counter
import unittest

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notations' / 'CTN'))

import ctn as c
from ctn_table_cases import shallow_table


def parse_skeleton(word):
    """Return completed table entries, final form, and open-block value."""
    if any(digit not in "12" for digit in word):
        raise ValueError("Only digits 1 and 2 are allowed")
    values, offset = [], 0
    kind, opened = "entry", 0
    while offset < len(word):
        if word[offset] == "2":
            if offset + 1 != len(word):
                raise ValueError("Characters after a closing marker")
            kind = "cap"
            break
        offset += 1
        start = offset
        while offset < len(word) and word[offset] == "2":
            offset += 1
        opened = offset - start
        if offset == len(word):
            kind = "gap"
            break
        values.append(opened)
        offset += 1
    return values, kind, opened



def old_standard(word, tree):
    try:
        values, _, _ = parse_skeleton(word)
        return tree(values)
    except ValueError:
        return False


def grammar_standard(word, tree):
    """Independent direct implementation of the five domain families."""
    if old_standard(word, tree):
        return True
    # New expressions must lie on a successor chain from an old predecessor.
    for cut in range(len(word)):
        if not word[cut:] or any(digit != "1" for digit in word[cut:]):
            continue
        prefix = word[:cut]
        if not old_standard(prefix, tree):
            continue
        values, kind, opened = parse_skeleton(prefix)
        if kind == "cap" and values:
            return True
        if kind == "gap" and not tree(values + [opened]):
            return True
    return False


class CTNTests(unittest.TestCase):
    def test_domain_against_independent_grammar(self):
        trees = [
            c.table_tree,
            lambda s: not s,
            lambda s: True,
            lambda s: all(s[i] > s[i + 1] for i in range(len(s) - 1)),
            lambda s: len(s) < 3 and all(x % 2 == 0 for x in s),
        ]
        self.total_terms = 0
        for tree in trees:
            words = [""]
            for length in range(1, 11):
                for digits in product("12", repeat=length):
                    word = "".join(digits)
                    valid = c.is_standard(word, tree)
                    self.assertEqual(valid, grammar_standard(word, tree), word)
                    if valid:
                        words.append(word)
            words.sort()
            self.total_terms += len(words)
            for i, word in enumerate(words):
                for j in range(len(word) + 1):
                    self.assertTrue(c.is_standard(word[:j], tree))
                if not word:
                    continue
                self.assertEqual(c.fundamental(word, 0, tree), word[:-1])
                previous = word[:-1]
                for n in range(1, 13):
                    result = c.fundamental(word, n, tree)
                    self.assertTrue(c.is_standard(result, tree), (word, n, result))
                    self.assertTrue(result.startswith(previous))
                    self.assertTrue(result.startswith(word[:-1]))
                    self.assertLess(result, word)
                    if word.endswith("1"):
                        self.assertEqual(result, word[:-1])
                    else:
                        self.assertGreater(result, previous)
                        self.assertGreaterEqual(len(result), len(word) - 1 + n)
                        self.assertLessEqual(len(result), len(word) + n)
                    previous = result
                self.assertLessEqual(words[i - 1], previous)
                if word.endswith("1"):
                    self.assertEqual(words[i - 1], word[:-1])
        print(json.dumps({"five_tree_domain_and_expansion_checks": True,
                          "total_legal_terms": self.total_terms}))

    def test_padding_collapse_has_ordered_fibres(self):
        words = []
        for length in range(13):
            for digits in product("12", repeat=length):
                word = "".join(digits)
                if c.is_standard(word):
                    words.append(word)
        words.sort()
        previous = ""
        for word in words:
            original = word
            while not old_standard(original, c.table_tree):
                self.assertTrue(original.endswith("1"))
                original = original[:-1]
            self.assertGreaterEqual(original, previous)
            self.assertEqual(word, original + "1" * (len(word) - len(original)))
            previous = original

    def test_fixed_omega(self):
        self.assertEqual(c.OMEGA, "12")
        for n in range(80):
            self.assertTrue(c.is_standard("1" * n))
            self.assertEqual(c.fundamental(c.OMEGA, n), "1" * (1 + n))
        # A first 2 cannot appear later: encoded table entry zero is terminal.
        for count in range(2, 100):
            self.assertFalse(c.is_standard("1" * count + "2"))

    def test_all_three_limit_branches(self):
        expected = {
            "2": ["", "1", "12", "122", "1222"],
            "12": ["1", "11", "111", "1111", "11111"],
            "122": ["12", "1212", "12121", "121211", "1212111"],
        }
        for word, values in expected.items():
            self.assertEqual([c.fundamental(word, n) for n in range(5)], values)
        self.assertFalse(c.is_standard("21"))
        self.assertFalse(c.is_standard("121212"))
        self.assertTrue(c.is_standard("12121111"))

    def test_bounded_target_guided_reachability(self):
        rng = random.Random(20260927)
        words = []
        for length in range(11):
            for digits in product("12", repeat=length):
                word = "".join(digits)
                if c.is_standard(word):
                    words.append(word)
        words.sort()
        pairs = [(c.TOP, b) for b in words if b != c.TOP]
        pairs += [tuple(reversed(sorted(rng.sample(words, 2)))) for _ in range(600)]
        largest_steps = 0
        for initial, target in pairs:
            current = initial
            for steps in range(120):
                if current == target:
                    largest_steps = max(largest_steps, steps)
                    break
                choices = [c.fundamental(current, n) for n in range(14)]
                current = next(x for x in choices if x >= target)
                self.assertLess(current, initial)
            else:
                self.fail((initial, target, current))
        print(json.dumps({"bounded_reachability_pairs": len(pairs),
                          "max_rewrite_steps": largest_steps}))

    def test_large_legal_inputs(self):
        for size in (1000, 5000):
            values = shallow_table(size)
            word = c.encode_table(values, cap=True)
            start = perf_counter()
            self.assertEqual(c.fundamental(word, 10), word[:-1] + "1" + "2" * 9)
            print(json.dumps({"table_entries": size, "columns": len(word),
                              "expand_seconds": perf_counter() - start}))
        self.assertEqual(c.fundamental("1" * 100000, 99), "1" * 99999)


if __name__ == "__main__":
    unittest.main(verbosity=2)
