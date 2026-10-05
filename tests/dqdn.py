"""Portable, bounded DQDN replay suite. Run from any working directory.

Each child has a 45-second wall-clock timeout. Python's shared Budget ticks
also enforce 40 seconds / 768 MiB peak RSS; Node has a 512-MiB heap cap.
Each test has fixed sample/step/DAG bounds. No descent search or background
worker is launched. Captured fixture output is limited to 16 MiB.
"""
from pathlib import Path
import ctypes
import json
import os
import subprocess
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / "notations/DQDN"
CODE = ROOT / "research/dqdn/code"
OUTPUT_LIMIT = 16 * 1024 * 1024


def peak_mib():
    if sys.platform != "win32":
        import resource
        peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return peak / (1048576 if sys.platform == "darwin" else 1024)
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_ = [("cb", wintypes.DWORD), ("faults", wintypes.DWORD)] + [
            (name, ctypes.c_size_t) for name in (
                "peak", "working", "peak_paged", "paged", "peak_nonpaged",
                "nonpaged", "pagefile", "peak_pagefile")]
    data = Counters()
    data.cb = ctypes.sizeof(data)
    current = ctypes.windll.kernel32.GetCurrentProcess
    current.restype = wintypes.HANDLE
    query = ctypes.windll.psapi.GetProcessMemoryInfo
    query.argtypes = (wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD)
    query.restype = wintypes.BOOL
    if not query(current(), ctypes.byref(data), data.cb):
        raise OSError("cannot read DQDN test memory usage")
    return data.peak / 1048576


def child(suite):
    sys.dont_write_bytecode = True
    sys.path[:0] = [str(KERNEL), str(CODE)]
    import lambda_columns
    started = time.monotonic()
    original = lambda_columns.Budget.tick
    events = 0
    def tick(budget):
        nonlocal events
        events += 1
        if events % 2048 == 0:
            if time.monotonic() - started > 40:
                raise TimeoutError("40-second DQDN test budget")
            if peak_mib() > 768:
                raise MemoryError("768-MiB DQDN test budget")
        return original(budget)
    lambda_columns.Budget.tick = tick
    if suite == "fixtures":
        import ner_test_vectors
        ner_test_vectors.main()
        return
    names = {
        "core": ["test_dqdn", "test_lqdn", "test_lcdn", "test_typed_builder",
                 "audit_wellfounded_boundary", "test_standard_frontend"],
        "research": ["test_ordinal_tree_macros", "test_buchholz_tree_macros",
                     "test_system_f_oracle_bridge", "small_generator_ranks",
                     "locate_requested_powers", "compact_iteration_seeds",
                     "compact_type_author"],
    }[suite]
    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromNames(names))
    print(json.dumps({"suite": suite, "tests": result.testsRun,
                      "peak_mib": round(peak_mib(), 2),
                      "budget_ticks": events}))
    if not result.wasSuccessful():
        raise SystemExit(1)


def run(command, data=None):
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", PYTHONUTF8="1")
    started = time.monotonic()
    # communicate(timeout=...) kills and waits for this child on timeout through
    # subprocess.run; no child in this suite launches grandchildren.
    result = subprocess.run(command, cwd=ROOT, env=environment, input=data,
                            capture_output=True, timeout=45)
    if len(result.stdout) + len(result.stderr) > OUTPUT_LIMIT:
        raise RuntimeError("16-MiB DQDN output budget exceeded")
    if result.returncode:
        raise RuntimeError((result.stdout + result.stderr).decode("utf-8", "replace")[-12000:])
    return result.stdout, {"exit_code": result.returncode,
        "seconds": round(time.monotonic() - started, 3),
        "stdout": result.stdout.decode("utf-8").strip(),
        "stderr": result.stderr.decode("utf-8").strip()}


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--child":
        child(sys.argv[2])
        return
    if len(sys.argv) != 1:
        raise SystemExit("usage: python -B tests/dqdn.py")
    checks = []
    for group in ("core", "research"):
        _, report = run([sys.executable, "-B", "-X", "utf8", __file__, "--child", group])
        checks.append(dict(id=group, **report))
    fixture, report = run([sys.executable, "-B", "-X", "utf8", __file__, "--child", "fixtures"])
    report["stdout"] = f"{len(fixture)} fixture bytes; not copied into this receipt"
    checks.append(dict(id="fixtures", **report))
    for name in ("test_dqdn_ner.cjs", "test_dqdn_minimal_path.cjs",
                 "test_requested_powers.cjs", "exact_node_views.cjs"):
        output, report = run(["node", "--max-old-space-size=512", str(CODE / name)],
                             fixture if name == "test_dqdn_ner.cjs" else None)
        if name == "exact_node_views.cjs":
            table = json.loads(output)
            report["stdout"] = json.dumps({"main": len(table["main"]),
                "early": len(table["early"]), "note": table["note"]})
        checks.append(dict(id=name, **report))
    print(json.dumps({"notation": "DQDN", "universal_proof": False,
        "lean_build": False, "browser_click_test": False,
        "all_test_commands_exited": True, "runs": checks}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
