"""Validated public frontend for the TOP-standard DQDN domain.

The neighbouring dqdn/typed_builder modules are the unchanged research kernels.
Their raw graph helpers deliberately accept more than the public notation.
This wrapper does not change expansion rules or interpret budget exhaustion as
nonstandardness. Only Python's standard library is required.
"""

import argparse
import json
import re

import dqdn
import typed_builder as builder

TOP = builder.TOP
Budget = dqdn.Budget
ResourceLimit = dqdn.ResourceLimit


def require_standard(columns, budget=None):
    if not builder.is_standard(columns, budget):
        raise ValueError("not a TOP-standard DQDN expression")
    return columns


def from_path(path, budget=None):
    """Replay a literal TOP[n]... path, not arbitrary Python code."""
    if not isinstance(path, str) or len(path) > 8192:
        raise ValueError("expected a TOP path of at most 8192 characters")
    if re.fullmatch(r"TOP(?:\[[0-9]+\])*", path) is None:
        raise ValueError("expected TOP followed by natural-number indices")
    budget = budget or Budget()
    current = TOP
    for item in re.findall(r"\[([0-9]+)\]", path):
        budget.tick()
        current = builder.expand(current, int(item), budget)
    return current


def expand(columns, index, budget=None):
    budget = budget or Budget()
    require_standard(columns, budget)
    return builder.expand(columns, index, budget)


def counts(columns, budget=None):
    require_standard(columns, budget)
    return builder.counts(columns)


def compare(left, right, budget=None):
    budget = budget or Budget()
    require_standard(left, budget)
    require_standard(right, budget)
    return builder.compare(left, right)


def is_limit(columns, budget=None):
    require_standard(columns, budget)
    return columns == TOP or bool(columns and columns[-1][0] == "run")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", default="TOP[1][1]")
    parser.add_argument("--expand", type=int, help="take one more fundamental-sequence term")
    parser.add_argument("--list", action="store_true", help="also emit all tagged columns")
    args = parser.parse_args()
    try:
        columns = from_path(args.path)
        if args.expand is not None:
            columns = expand(columns, args.expand)
        result = {"length": len(columns), "counts": counts(columns),
                  "is_limit": is_limit(columns)}
        if args.list:
            result["columns"] = columns
        print(json.dumps(result, ensure_ascii=False))
    except (ValueError, ResourceLimit) as error:
        parser.exit(2, f"DQDN: {error}\n")


if __name__ == "__main__":
    main()
