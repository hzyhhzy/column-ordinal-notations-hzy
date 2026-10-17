"""Bounded, read-only checks for the collected Laver lower-bound package.

No hierarchy value or large Laver table is evaluated. The mathematical
proofs are not certified by this script.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
from time import monotonic
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
START = monotonic()
DEADLINE_SECONDS = 15
MAX_ROWS = 600
MAX_FIELDS = 60_000
MAX_STEPS = 400
MAX_INPUT_INDEX = 7
STEPS = 0
PEAK_ROWS = 0
PEAK_FIELDS = 0
CHECKS = {}


def budget():
    if monotonic() - START > DEADLINE_SECONDS:
        raise RuntimeError("bounded validation time limit")


def count(name, amount=1):
    CHECKS[name] = CHECKS.get(name, 0) + amount


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def check_package():
    manifest = json.loads((ROOT / "SOURCE_MANIFEST.json").read_text(encoding="utf-8"))
    for entry in manifest["items"]:
        budget()
        path = ROOT / entry["package"]
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        assert actual == entry["package_sha256"], entry["package"]
        count("pinned_files")
    forbidden_input = re.compile(r"10\s*(?:\^\s*\{?\s*100\s*\}?|\*\*\s*100)|1[eE]\+?100")
    machine_path = re.compile(r"(?:/C:/|C:[/\\]Users[/\\])")
    for path in sorted(ROOT.rglob("*")):
        budget()
        if path.suffix not in {".md", ".txt", ".py", ".json"}:
            continue
        text = path.read_text(encoding="utf-8-sig")
        if path.name != Path(__file__).name:
            assert not forbidden_input.search(text), f"obsolete prescribed input: {path}"
            assert not machine_path.search(text), f"machine-specific path: {path}"
        if path.suffix != ".md":
            continue
        count("markdown_files")
        assert sum(line.strip() == "$$" for line in text.splitlines()) % 2 == 0, path
        assert len(re.findall(r"^\\\[$", text, re.M)) == len(re.findall(r"^\\\]$", text, re.M)), path
        for match in re.finditer(r"\[[^\]\n]+\]\((<?[^)\n]+>?)\)", text):
            target = match[1].strip("<>")
            if re.match(r"(?:https?://|mailto:|#)", target):
                continue
            target = target.split("#", 1)[0]
            # Do not confuse fundamental-sequence formulas with Markdown links.
            if not re.search(r"\.(?:md|txt|py|js|json|pdf)$", target, re.I):
                continue
            dest = (path.parent / unquote(target)).resolve()
            assert ROOT.resolve() in (dest, *dest.parents), (path, target, "outside package")
            assert dest.is_file(), (path.relative_to(ROOT), target)
            count("local_links")
    return manifest


def syntax_checks():
    ib = load("laver_bounds_original_iblp", ROOT / "code" / "iblp_original.py")

    def bounded(p):
        global PEAK_ROWS, PEAK_FIELDS
        budget()
        rows = len(p.rows) - 1
        fields = sum(map(len, p.rows)) + sum(map(len, p.mask))
        PEAK_ROWS = max(PEAK_ROWS, rows)
        PEAK_FIELDS = max(PEAK_FIELDS, fields)
        assert rows <= MAX_ROWS and fields <= MAX_FIELDS
        assert len(p.rows) == len(p.mask)
        assert len(p.rows[0]) == rows
        for r in range(1, len(p.rows)):
            row = p.rows[r]
            assert row == sorted(set(row)) and row[-1] == r
            assert all(y in row and y < r for y in p.mask[r])
        return p

    def child(p, n):
        global STEPS
        budget()
        assert 0 <= n <= MAX_INPUT_INDEX
        STEPS += 1
        assert STEPS <= MAX_STEPS
        q, _ = ib._apply_number(p, n, silent=True)
        return bounded(q)

    def path(indices):
        p = bounded(ib.Pattern(ib.initial_rows, ib.initial_mask))
        for n in indices:
            p = child(p, n)
        return p

    a = path([0, 1])
    root = path([0, 3, 0])
    assert root.rows == [[1, 1, 2, 1, 2, 1],
                         [0, 1], [0, 1, 2], [0, 1, 2, 3],
                         [2, 3, 4], [2, 3, 4, 5], [4, 5, 6]]
    assert not any(root.mask)
    count("root_identities")
    c = path([0, 3, 0, 0] + [1] * 8)
    assert c.rows == [a.rows[0] + [1]] + a.rows[1:] + [[0, 1, 5]]
    assert not any(c.mask)
    count("root_identities")

    def graft(p):
        def phi(t):
            return 1 if t == 0 else t + 4
        return bounded(ib.Pattern(
            [a.rows[0] + p.rows[0]] + a.rows[1:]
            + [[phi(t) for t in row] for row in p.rows[1:]],
            a.mask + [{phi(t) for t in marks} for marks in p.mask[1:]],
        ))

    expected = a
    for n in range(2, 8):
        expected = graft(expected)
        actual = child(c, n)
        assert actual.rows == expected.rows and actual.mask == expected.mask
        assert len(actual.rows) - 1 == 4 * n
        count("exact_tower_terms")

    for k in range(2, 7):
        first = child(root, k)
        for n in range(2, 7):
            p = child(first, n)
            for r in range(1, len(p.rows)):
                row, step = p.rows[r], p.rows[0][r - 1]
                pivot, first_image = row[-step - 1], row[-step]
                if len(row) <= 2 * step:
                    assert p.rows[first_image][-2] <= pivot
                for y in p.mask[r]:
                    trace = ib._tr(p, r, row.index(y) + 1)
                    assert trace and len(trace) == 2 and trace[-1] >= 1
                    count("direct_positive_marks")
            count("small_two_step_entries")


def bms_checks():
    mod = load("laver_bounds_parent_bms", ROOT / "code" / "anchored_parent_bms.py")
    ParentBMS = mod.ParentBMS

    def words(prefix=()):
        yield prefix
        if len(prefix) < 3:
            for depth in range((prefix[-1] + 2) if prefix else 1):
                yield from words(prefix + (depth,))

    def parents(word):
        stack, result = [], []
        for j, depth in enumerate(word):
            stack = stack[:depth]
            result.append((stack[-1],) if stack else ())
            stack.append(j)
        return tuple(result)

    def forest_value(word, base):
        stack, total = [], 0
        def close():
            nonlocal total
            value = base ** stack.pop()
            assert value.bit_length() <= 128
            if stack:
                stack[-1] += value
            else:
                total += value
        for depth in word:
            while len(stack) > depth:
                close()
            stack.append(0)
        while stack:
            close()
        return total

    for word in words():
        for original_index in (1, 2):
            budget()
            current = ParentBMS(parents(word))
            zero_deletions = 0
            for _ in range(300):
                if not current.columns:
                    break
                zero_deletions += not current.columns[-1]
                # Parent display [2] is original BM4 [1].
                current = current[original_index + 1]
                assert len(current.columns) <= 300
                budget()
            else:
                raise AssertionError("unexpected small one-row resource limit")
            assert zero_deletions == forest_value(word, original_index + 1)
            count("one_row_forest_and_index_checks")


def main():
    manifest = check_package()
    syntax_checks()
    bms_checks()
    print(json.dumps({
        "status": "PASS", "proof_certification": False,
        "scope": "hashes, portable links, literal source identities, bounded mark invariants, one-row index convention",
        "checks": CHECKS, "basic_steps": STEPS, "peak_rows": PEAK_ROWS,
        "peak_fields": PEAK_FIELDS, "seconds": round(monotonic() - START, 6),
        "limits": {"seconds": DEADLINE_SECONDS, "basic_steps": MAX_STEPS,
                   "rows": MAX_ROWS, "fields": MAX_FIELDS, "largest_index": MAX_INPUT_INDEX,
                   "bms_steps_per_small_case": 300, "forest_integer_bits": 128},
        "proof_manuscripts": sum(e["package"].startswith("proofs/") for e in manifest["items"]),
        "large_hierarchy_evaluations": 0, "laver_tables_constructed": 0,
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
