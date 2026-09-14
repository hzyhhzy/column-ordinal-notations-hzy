#!/usr/bin/env python3
"""Bounded, source-closed verification of the six ordinary Lean proofs."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXTERNAL_ROOTS = {"Mathlib", "Batteries", "Aesop", "Qq", "Lean", "Init", "Std"}


def strip_comments(text: str) -> str:
    """Preserve newlines while removing Lean's nested comments."""
    out, pos, depth = [], 0, 0
    while pos < len(text):
        if text[pos:pos + 2] == "/-":
            depth += 1
            pos += 2
        elif depth and text[pos:pos + 2] == "-/":
            depth -= 1
            pos += 2
        elif not depth and text[pos:pos + 2] == "--":
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end
        else:
            out.append("\n" if text[pos] == "\n" else (" " if depth else text[pos]))
            pos += 1
    return "".join(out)


def imports(text: str) -> list[str]:
    result = []
    for match in re.finditer(r"^\s*(?:public\s+)?import\s+([^\n]+)", strip_comments(text), re.M):
        result.extend(match.group(1).split())
    return result


def source_hash(data: bytes) -> str:
    return hashlib.sha256(data.replace(b"\r\n", b"\n")).hexdigest()


def inventory(bms_root: Path, allow_missing_external: bool = False) -> tuple[list[str], dict[str, dict], set[str], dict[str, Path]]:
    manifest = json.loads((ROOT / "sources.json").read_text(encoding="utf-8"))
    records = manifest["modules"]
    found = {".".join(p.relative_to(SRC).with_suffix("").parts): p for p in SRC.rglob("*.lean")}
    bundled = {m for m, r in records.items() if r["origin"] != "BMS"}
    if set(found) != bundled:
        raise ValueError(f"Source/manifest mismatch: {set(found) ^ bundled}")
    for module, record in records.items():
        if record["origin"] == "BMS":
            found[module] = bms_root.joinpath(*module.split(".")).with_suffix(".lean")
    ordered, active, complete, external = [], set(), set(), set()

    def visit(module: str) -> None:
        if module in complete:
            return
        if module not in found:
            if module.split(".")[0] not in EXTERNAL_ROOTS:
                raise ValueError(f"Unresolved local import: {module}")
            external.add(module)
            return
        if module in active:
            raise ValueError(f"Cyclic local import: {module}")
        active.add(module)
        if not found[module].exists():
            if not (allow_missing_external and records[module]["origin"] == "BMS"):
                raise ValueError(f"Missing pinned external BMS source: {module}; run lake update first")
            actual_imports = records[module]["imports"]
            data = None
        else:
            data = found[module].read_bytes()
            actual_imports = imports(data.decode("utf-8-sig"))
        if data is not None and source_hash(data) != records[module]["sha256"]:
            raise ValueError(f"Source hash mismatch: {module}; update the manifest deliberately after editing")
        if actual_imports != records[module]["imports"]:
            raise ValueError(f"Import manifest mismatch: {module}")
        for dependency in actual_imports:
            visit(dependency)
        active.remove(module)
        complete.add(module)
        ordered.append(module)

    visit(manifest["target"])
    if complete != set(records):
        raise ValueError(f"Unused bundled source modules: {set(records) - complete}")
    config = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    lake_roots_match = re.search(r"roots\s*:=\s*#\[([^\]]+)\]", config)
    if not lake_roots_match:
        raise ValueError("Lake library roots not found")
    lake_roots = set(re.findall(r"`([\w.]+)", lake_roots_match.group(1)))
    if any(not any(module == root or module.startswith(root + ".") for root in lake_roots)
           for module in bundled):
        raise ValueError("A bundled source is not owned by the declared Lake library")
    return ordered, records, external, found


def stop_tree(process: subprocess.Popen) -> None:
    if process.poll() is not None:
        return
    if os.name == "nt":
        # This PID was created by this invocation; never match by process name.
        subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
                       creationflags=subprocess.CREATE_NO_WINDOW, timeout=15)
    else:
        os.killpg(process.pid, signal.SIGKILL)
    process.wait(timeout=15)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true", help="Check exact source hashes and transitive closure only")
    parser.add_argument("--lean", default="lean", help="Lean 4.33.1 executable")
    parser.add_argument("--external-path", action="append", default=[], help="Built mathlib/dependency import root; repeatable")
    parser.add_argument("--bms-source", type=Path, default=ROOT / ".lake/packages/YesMetaZFC", help="Pinned BMS checkout; default is Lake's dependency directory")
    parser.add_argument("--seconds", type=int, default=120, help="Per-module wall timeout, 10..600")
    parser.add_argument("--memory-mb", type=int, default=2048, help="Per-compiler memory cap, 512..4096 MiB")
    parser.add_argument("--resume", action="store_true", help="Reuse only artifacts certified by this exact verifier and source closure")
    args = parser.parse_args()
    if not (10 <= args.seconds <= 600 and 512 <= args.memory_mb <= 4096):
        parser.error("Limits must be in the documented range")
    ordered, records, external, sources = inventory(args.bms_source, allow_missing_external=args.check_only)
    print(f"Source closure: {len(ordered)} modules; {len(external)} direct external imports", flush=True)
    if args.check_only:
        present = sum(path.exists() for path in sources.values())
        print(f"Verified source bytes: {present}; pinned external source entries awaiting fetch: {len(ordered) - present}", flush=True)
        return 0
    version = subprocess.check_output([args.lean, "--version"], text=True, timeout=20)
    if not re.search(r"version 4\.33\.1(?:,|\s|$)", version):
        raise ValueError(f"Expected Lean 4.33.1, got {version.strip()}")
    build = ROOT / ".build"
    output, logs = build / "lean", build / "logs"
    output.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    # In a normal checkout use `lake env python build.py`. During offline QA,
    # --external-path can point only at already-built mathlib/package artifacts.
    search = args.external_path or [x for x in os.environ.get("LEAN_PATH", "").split(os.pathsep) if x]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(output)] + search)
    env["LEAN_NUM_THREADS"] = "1"
    receipt_path = build / "verification.json"
    previous = json.loads(receipt_path.read_text(encoding="utf-8")) if args.resume and receipt_path.exists() else {}
    receipt = {"compiler": version.strip(), "modules": {}, "complete": False,
               "limits": {"compiler_threads": 1, "concurrent_compilers": 1,
                          "memory_mb": args.memory_mb, "seconds_per_module": args.seconds},
               "external_artifacts": "Lean and Mathlib/dependency artifacts supplied by the dependency environment"}
    fingerprints, total_reports = {}, 0
    started = time.monotonic()
    for index, module in enumerate(ordered, 1):
        source = sources[module]
        target = output.joinpath(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        fingerprint = hashlib.sha256((records[module]["sha256"] + version + "".join(
            fingerprints.get(dep, dep) for dep in records[module]["imports"])).encode()).hexdigest()
        fingerprints[module] = fingerprint
        old = previous.get("modules", {}).get(module, {})
        if (args.resume and old.get("fingerprint") == fingerprint and target.exists()
                and old.get("olean_sha256") == hashlib.sha256(target.read_bytes()).hexdigest()):
            receipt["modules"][module] = old
            total_reports += old["axiom_reports"]
            print(f"REUSE {index}/{len(ordered)} {module}", flush=True)
            continue
        log = logs / (module + ".log")
        source_root = args.bms_source if records[module]["origin"] == "BMS" else SRC
        command = [args.lean, "-M", str(args.memory_mb), "-j", "1", "-R", str(source_root), "-o", str(target), str(source)]
        options = {"creationflags": subprocess.CREATE_NO_WINDOW} if os.name == "nt" else {"start_new_session": True}
        tick = time.monotonic()
        with log.open("w", encoding="utf-8") as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, **options)
            try:
                code = process.wait(timeout=args.seconds)
            finally:
                stop_tree(process)
        result = log.read_text(encoding="utf-8")
        if code != 0 or "sorryAx" in result or re.search(r"declaration uses .sorry.", result):
            raise RuntimeError(f"Failed {module}; inspect {log.relative_to(ROOT)}\n{result[-5000:]}")
        reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result)
        expected = re.findall(r"^#print axioms ", source.read_text(encoding="utf-8-sig"), re.M)
        if len(reports) != len(expected):
            raise RuntimeError(f"Incomplete axiom reports: {module}")
        for _, report in reports:
            extra = {x.strip() for x in report.split(",") if x.strip()} - ALLOWED_AXIOMS
            if extra:
                raise RuntimeError(f"Additional axioms in {module}: {extra}")
        elapsed = round(time.monotonic() - tick, 3)
        receipt["modules"][module] = {"fingerprint": fingerprint,
            "olean_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
            "axiom_reports": len(reports), "seconds": elapsed}
        total_reports += len(reports)
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
        print(f"PASS {index}/{len(ordered)} {module} ({elapsed:.2f}s, {len(reports)} axiom reports)", flush=True)
    receipt.update(complete=True, axiom_reports=total_reports, wall_seconds=round(time.monotonic() - started, 3))
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"VERIFIED: {len(ordered)} modules; {total_reports} axiom reports; no extra axioms", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
