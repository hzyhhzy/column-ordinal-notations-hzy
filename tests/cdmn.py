"""Run isolated, bounded CDMN checks; --record writes a finite-test receipt."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CHECKED = [
    "notations/CDMN/cdmn-core.cjs", "notations/CDMN/cdmn-ner-wrapper.js",
    "notations/CDMN/CDMN.ne-rewritten.js", "notations/CDMN/cdmn.py",
    "notations/CDMN/build-ner.cjs", "notations/CDMN/fixtures/regressions.json",
    "research/cdmn/dilation.cjs", "tests/cdmn.py", "tests/cdmn.cjs", "tests/cdmn_counts.cjs",
    "tests/cdmn_python.py", "tests/cdmn_vectors.cjs", "tests/cdmn_support.cjs",
]


def main():
    args = argparse.ArgumentParser()
    args.add_argument("--record", action="store_true")
    options = args.parse_args()
    runs = []

    def run(name, command, *, input_text=None, timeout=35, save_output=True):
        actual = [sys.executable if command[0] == "python" else command[0], *command[1:]]
        started = time.monotonic()
        result = subprocess.run(actual, cwd=ROOT, input=input_text, capture_output=True,
                                text=True, encoding="utf-8", timeout=timeout)
        if result.returncode:
            raise RuntimeError(name + ": " + result.stdout + result.stderr)
        record = {"id": name, "command": command, "exit_code": result.returncode,
                  "elapsed_seconds": round(time.monotonic() - started, 3),
                  "stderr": result.stderr.strip()}
        if save_output:
            record["stdout"] = result.stdout.strip()
        runs.append(record)
        return result.stdout

    run("bundle", ["node", "notations/CDMN/build-ner.cjs", "--check"])
    run("ner", ["node", "--max-old-space-size=256", "tests/cdmn.cjs"])
    run("counts", ["node", "--max-old-space-size=256", "tests/cdmn_counts.cjs"])
    run("python", ["python", "-B", "tests/cdmn_python.py"])
    vectors = run("vectors", ["node", "--max-old-space-size=256", "tests/cdmn_vectors.cjs"], save_output=False)
    run("cross-language", ["python", "-B", "tests/cdmn_python.py", "--vectors"], input_text=vectors)
    receipt = {
        "schema_version": 1, "notation": "CDMN", "date": "2026-10-10",
        "universal_proof": False, "well_ordering_proved": False,
        "lean_build": False, "browser_click_test": False, "all_test_commands_exited": True,
        "checked_files": [{"file": name, "sha256_lf": hashlib.sha256(
            (ROOT / name).read_bytes().replace(b"\r\n", b"\n")).hexdigest()} for name in CHECKED],
        "runs": runs,
    }
    if options.record:
        (ROOT / "tools/cdmn-validation.json").write_text(
            json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"notation": "CDMN", "completed": [r["id"] for r in runs],
                      "recorded": options.record, "well_ordering_proved": False}))


if __name__ == "__main__":
    main()
