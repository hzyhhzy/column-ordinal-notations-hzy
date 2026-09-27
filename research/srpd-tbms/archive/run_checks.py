"""Replay current bounded cases without changing the historical receipts.

stdout is a JSON receipt; stderr reports progress. Children run sequentially,
with a 512 MiB Node heap and a 30-second outer timeout. The original simulator
retains its own width, step, time and RSS checks. A known width guard is reported
as guarded, never as a successfully completed source path.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import sys
import time

from verify_archive import ARCHIVE, ROOT, sha256_lf, verify

RESEARCH = ARCHIVE / "output/tbms-e0mn-bridge-20260925"
TIMEOUT_SECONDS = 30
WIDTH_GUARD = "recursive row allocation width guard"
RUNTIME_FIELDS = {"elapsedMs", "rssMiB", "stack"}


def stable(value):
    """Exclude timing, process RSS and machine-specific exception stacks only."""
    if isinstance(value, dict):
        return {key: stable(item) for key, item in value.items()
                if key not in RUNTIME_FIELDS}
    if isinstance(value, list):
        return [stable(item) for item in value]
    return value


def digest(value):
    raw = json.dumps(value, ensure_ascii=False, sort_keys=True,
                     separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def cases(suite):
    weak = json.loads((RESEARCH / "WEAK-ARCHIVE-VERIFICATION.json").read_text(encoding="utf-8"))
    epsilon = json.loads((RESEARCH / "EPSILON-FIXED-BANK-VERIFICATION.json").read_text(encoding="utf-8"))
    weak_ids = [str(i) for i in range(14)] + ["local"]
    epsilon_ids = [str(i) for i in range(12)]
    if suite == "smoke":
        weak_ids, epsilon_ids = ["0", "1", "local"], ["0", "5"]
    for item in weak["cases"]:
        case_id = str(item["caseIndex"])
        if case_id in weak_ids:
            # The historical receipt deduplicated these shared fields at its
            # top level. Restore them before comparing, rather than dropping
            # them from the newly returned state.
            item.setdefault("interfacePatches", weak["interfacePatches"])
            item["seedAudit"].setdefault("stages", weak["seedStages"])
            yield "weak:" + case_id, "check-weak-archive-case.cjs", [case_id], 0, item
    yield "weak:common-gate", "check-weak-archive-gate.cjs", [], 0, weak["commonGate"]
    for item in epsilon["cases"]:
        if item["id"] in epsilon_ids:
            yield "epsilon:" + item["id"], "check-epsilon-fixed-bank.cjs", [item["id"]], item["exitCode"], item["result"]


def run_case(node, spec):
    name, script, arguments, expected_exit, old = spec
    relative = (RESEARCH / script).relative_to(ROOT).as_posix()
    command = [node, "--max-old-space-size=512", relative, *arguments]
    start = time.monotonic()
    child = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, encoding="utf-8")
    timed_out = False
    try:
        stdout, stderr = child.communicate(timeout=TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        timed_out = True
        child.kill()
        stdout, stderr = child.communicate()
    finally:
        if child.poll() is None:
            child.kill()
            child.communicate()
    entry = {
        "id": name, "command": ["node", *command[1:]],
        "exit_code": child.returncode,
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "timed_out": timed_out, "process_exited": child.poll() is not None,
    }
    if timed_out:
        return {**entry, "status": "failed", "reason": "outer timeout"}
    try:
        result = json.loads(stdout)
    except json.JSONDecodeError:
        # Do not copy private exception stacks into a shareable receipt.
        return {**entry, "status": "failed", "reason": "child did not return JSON",
                "stdout_characters": len(stdout), "stderr_characters": len(stderr)}
    error = (result.get("error") or {}).get("message")
    comparison, baseline = stable(result), stable(old)
    matching = comparison == baseline
    # Accept only the two specifically recorded width guards. No generic
    # assertion, timeout or memory guard may become a successful replay.
    known_guard = name in {"epsilon:3", "epsilon:8"}
    expected_outcome = (
        child.returncode == expected_exit
        and (error == WIDTH_GUARD if known_guard else error is None)
        and not stderr.strip()
    )
    status = ("guarded" if known_guard else "passed") if matching and expected_outcome else "failed"
    entry.update({
        "status": status, "error_message": error,
        "historical_semantics_match": matching,
        "semantic_sha256": digest(comparison),
        "historical_semantic_sha256": digest(baseline),
        "source_steps": result.get("stats", {}).get("sourceSteps", 0),
        "rss_mib": result.get("rssMiB"),
    })
    if not matching:
        entry["different_top_level_fields"] = sorted(
            key for key in comparison.keys() | baseline.keys()
            if comparison.get(key) != baseline.get(key))
    if not expected_outcome:
        entry["reason"] = "unexpected exit, diagnostic or guard"
    return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=("smoke", "current"), default="smoke")
    args = parser.parse_args()
    integrity, _ = verify()
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node.js is required; nothing was installed or run.")
    runs = []
    for spec in cases(args.suite):
        result = run_case(node, spec)
        runs.append(result)
        print(f'{result["id"]}: {result["status"]} ({result["elapsed_seconds"]} s)',
              file=sys.stderr, flush=True)
        if result["status"] == "failed":
            break
    counts = Counter(result["status"] for result in runs)
    expected_cases = 28 if args.suite == "current" else 6
    complete = len(runs) == expected_cases and not counts["failed"]
    receipt = {
        "schema_version": 1,
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "suite": args.suite,
        "status": "bounded archive replay reproduced" if complete else "failed or incomplete",
        "universal_proof": False,
        "independent_mathematical_review": False,
        "integrity": integrity,
        "checked_tools": [{"file": path.relative_to(ROOT).as_posix(), "sha256_lf": sha256_lf(path)}
                          for path in (ARCHIVE / "verify_archive.py", ARCHIVE / "run_checks.py")],
        "limits": {"node_heap_mib": 512, "outer_timeout_seconds": TIMEOUT_SECONDS,
                   "max_concurrent_children": 1, "original_simulator_guards_retained": True},
        "comparison_excludes_only": sorted(RUNTIME_FIELDS),
        "historical_shared_fields_expanded": ["weak.interfacePatches", "weak.seedStages"],
        "counts": dict(counts),
        "cases": len(runs), "expected_cases": expected_cases,
        "max_reported_rss_mib": max((r.get("rss_mib") or 0 for r in runs), default=0),
        "all_children_exited": all(r["process_exited"] for r in runs),
        "runs": runs,
    }
    print(json.dumps(receipt, ensure_ascii=False, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    raise SystemExit(main())
