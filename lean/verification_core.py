"""Shared, bounded verifier for independently source-closed Lean projects.

There is one canonical proof source per module. Project manifests contain exact
import closures; their receipts do not depend on an unrelated global catalog.
External proof binaries from sibling/research projects are never implicit input.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

CORE = Path(__file__).resolve()
POLICY = "independent-lean-v2.1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXTERNAL_ROOTS = {"Mathlib", "Batteries", "Aesop", "Qq", "Lean", "Init", "Std"}
SOURCE_PACKAGES = {"YesMetaZFC"}  # Rebuilt from pinned source, not trusted binaries.
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
AXIOM_REPORT = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
IMPORT_SUFFIXES = (".olean.private", ".olean.server", ".ir.sig", ".olean", ".ir")


def digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=True).encode()).hexdigest()


def file_hash(path: Path, lf=False) -> str:
    if lf:
        return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1048576), b""):
            result.update(chunk)
    return result.hexdigest()


def atomic_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=".verification-", suffix=".json", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            json.dump(value, stream, indent=2, ensure_ascii=True)
            stream.write("\n")
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def strip_comments(text: str) -> str:
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


def requested_reports(text: str) -> list[str]:
    return re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", strip_comments(text), re.M)


def parse_reports(text: str, requested: list[str]) -> list[dict]:
    if "sorryAx" in text or re.search(r"declaration uses .sorry.", text):
        raise ValueError("Reported sorry/extra proof placeholder")
    matches = AXIOM_REPORT.findall(text)
    if len(matches) != len(requested):
        raise ValueError("Incomplete axiom-report count")
    reports = []
    for wanted, (name, axiom_text) in zip(requested, matches):
        clean = wanted.removeprefix("_root_.")
        if name != clean and not name.endswith("." + clean):
            raise ValueError(f"Wrong theorem in axiom log: expected {wanted}, got {name}")
        axioms = sorted({item.strip() for item in axiom_text.split(",") if item.strip()})
        if set(axioms) - ALLOWED_AXIOMS:
            raise ValueError(f"Additional axioms for {name}: {axioms}")
        reports.append({"requested": wanted, "name": name, "axioms": axioms})
    return reports


def scoped_path(root: Path, relative: str) -> Path:
    path = (root / relative).resolve()
    if Path(relative).is_absolute() or not path.is_relative_to(root.resolve()):
        raise ValueError(f"Path leaves its permitted source scope: {relative}")
    return path


def owner_directory(repository: Path, owner: str) -> Path:
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", owner):
        raise ValueError(f"Invalid module owner: {owner}")
    return repository / "lean" if owner == "aggregate" else repository / "lean" / owner


def config_hashes(directory: Path, repository: Path) -> dict[str, str]:
    result = {}
    for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        path = directory / name
        if not path.is_file():
            raise ValueError(f"Missing project configuration: {path}")
        result[path.relative_to(repository).as_posix()] = file_hash(path, lf=True)
    return result


def declared_modules(directory: Path) -> set[str]:
    config = (directory / "lakefile.lean").read_text(encoding="utf-8-sig")
    match = re.search(r"globs\s*:=\s*#\[([^\]]*)\]", strip_comments(config), re.S)
    if not match:
        raise ValueError(f"Missing exact Lake globs in {directory}")
    text = match.group(1)
    modules = re.findall(r"\.one\s+`([\w.]+)", text)
    residue = re.sub(r"\.one\s+`([\w.]+)", "", text)
    if residue.replace(",", "").strip() or len(modules) != len(set(modules)):
        raise ValueError("Lake globs must be distinct explicit .one modules")
    # Namespace roots deliberately stay empty: sibling libraries share namespaces.
    roots = re.search(r"roots\s*:=\s*#\[([^\]]*)\]", strip_comments(config), re.S)
    if not roots or roots.group(1).strip():
        raise ValueError("Independent Lake libraries require empty roots and exact .one globs")
    return set(modules)


def load_plan(directory: Path, bms_source: Path | None = None, allow_missing_bms=True) -> dict:
    directory = directory.resolve()
    manifest_path = directory / "sources.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    if manifest.get("schema_version") != 2:
        raise ValueError("Expected independent-project source schema 2")
    repository = (directory / manifest["repository_root"]).resolve()
    if directory != owner_directory(repository, manifest["project"]).resolve():
        raise ValueError("Project directory / owner / repository_root mismatch")
    records, targets = manifest["modules"], manifest["targets"]
    if not targets or len(targets) != len(set(targets)):
        raise ValueError("Target roots must be a nonempty exact list")
    if manifest.get("target") not in targets:
        raise ValueError("The main target must be one of the exact roots")
    sources, source_roots, requested, owner_inputs = {}, {}, {}, {}
    owned = set()
    for module, record in records.items():
        if not MODULE_NAME.fullmatch(module):
            raise ValueError(f"Invalid Lean module identifier: {module}")
        owner = record["owner"]
        owner_dir = owner_directory(repository, owner)
        if owner not in owner_inputs:
            owner_inputs[owner] = config_hashes(owner_dir, repository)
        relative_module = Path(*module.split(".")).with_suffix(".lean")
        if record.get("origin") == "BMS":
            if owner != "Y" or record.get("external") is not True or "file" in record:
                raise ValueError("BMS must remain Y-owned external pinned source")
            root = bms_source or repository / "lean/Y/.lake/packages/YesMetaZFC"
            source = root / relative_module
        else:
            expected = (owner_dir / "src" / relative_module).resolve()
            source = scoped_path(repository, record["file"])
            if source != expected:
                raise ValueError(f"Module/file/owner mismatch: {module}")
            root = owner_dir / "src"
            if owner == manifest["project"]:
                owned.add(module)
        sources[module], source_roots[module] = source, root
        if not source.is_file():
            if record.get("origin") == "BMS" and allow_missing_bms:
                requested[module] = None
                continue
            raise ValueError(f"Missing source: {module}; BMS needs its pinned source checkout")
        if file_hash(source, lf=True) != record["sha256"]:
            raise ValueError(f"Source hash mismatch: {module}")
        content = source.read_text(encoding="utf-8-sig")
        if imports(content) != record["imports"]:
            raise ValueError(f"Actual imports differ from manifest: {module}")
        requested[module] = requested_reports(content)
    actual_owned = {".".join(path.relative_to(directory / "src").with_suffix("").parts)
                    for path in (directory / "src").rglob("*.lean")}
    if actual_owned != owned or declared_modules(directory) != owned:
        raise ValueError("Owned source files / manifest / Lake globs differ")
    ordered, done, active, external = [], set(), set(), set()
    def visit(module):
        if module in done:
            return
        if module not in records:
            if module.split(".")[0] not in EXTERNAL_ROOTS:
                raise ValueError(f"Unresolved local import: {module}")
            external.add(module)
            return
        if module in active:
            raise ValueError(f"Import cycle: {module}")
        active.add(module)
        for dependency in records[module]["imports"]:
            visit(dependency)
        active.remove(module)
        done.add(module)
        ordered.append(module)
    for target in targets:
        visit(target)
    if done != set(records):
        raise ValueError("Manifest is not the exact target closure; missing/unused records")
    if set(manifest.get("external", [])) != external:
        raise ValueError("Direct external-boundary manifest mismatch")
    inputs = config_hashes(directory, repository)
    for path in (manifest_path, directory / "build.py", CORE):
        inputs[path.relative_to(repository).as_posix()] = file_hash(path, lf=True)
    semantic = {module: {key: record[key] for key in ("owner", "sha256", "imports")}
                for module, record in records.items()}
    return {"directory": directory, "repository": repository, "manifest": manifest,
            "records": records, "targets": targets, "ordered": ordered, "external": external,
            "sources": sources, "source_roots": source_roots, "requested": requested,
            "owner_inputs": owner_inputs, "inputs": inputs,
            "closure_sha256": digest({"targets": targets, "modules": semantic})}


def dependency_revisions(plan) -> list[dict]:
    lock = json.loads((plan["directory"] / "lake-manifest.json").read_text(encoding="utf-8"))
    records = [{key: package.get(key) for key in ("name", "scope", "url", "rev", "subDir")}
               for package in lock["packages"] if package["type"] == "git"
               and package["name"] not in SOURCE_PACKAGES]
    return sorted(records, key=lambda item: item["name"])


def artifact_suffix(path: Path) -> str | None:
    return next((suffix for suffix in IMPORT_SUFFIXES if path.name.endswith(suffix)), None)


def module_artifact(root: Path, module: str, suffix: str) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(suffix)


def module_bundle(root: Path, module: str) -> dict[str, str]:
    return {suffix: file_hash(path) for suffix in IMPORT_SUFFIXES
            if (path := module_artifact(root, module, suffix)).is_file()}


def clear_module_bundle(root: Path, module: str) -> None:
    # Only this named module's generated import artifacts, inside its private output.
    root = root.resolve()
    for suffix in IMPORT_SUFFIXES:
        path = module_artifact(root, module, suffix).resolve()
        if not path.is_relative_to(root):
            raise ValueError("Generated artifact escaped the private output directory")
        if path.is_file():
            path.unlink()


def artifact_tree(path: Path, *, include_runtime=False) -> dict:
    entries, size, oleans, runtime, sidecars = [], 0, 0, 0, 0
    for artifact in sorted(path.rglob("*")):
        if not artifact.is_file():
            continue
        binary = artifact.suffix in {".exe", ".dll", ".so", ".dylib"} or ".so." in artifact.name
        suffix = artifact_suffix(artifact)
        if suffix is None and not (include_runtime and binary):
            continue
        entries.append([artifact.relative_to(path).as_posix(), file_hash(artifact)])
        size += artifact.stat().st_size
        oleans += suffix == ".olean"
        sidecars += suffix is not None and suffix != ".olean"
        runtime += binary
    return {"sha256": digest(entries), "olean_files": oleans, "import_sidecars": sidecars,
            "runtime_binaries": runtime, "bytes": size}


def external_environment(paths: list[Path], plan) -> tuple[list[Path], list[dict]]:
    roots, trees, seen = [], [], set()
    for raw in paths:
        path = raw.resolve()
        if path in seen:
            continue
        seen.add(path)
        if not path.is_dir():
            raise ValueError(f"Missing external artifact directory: {path}")
        # Never allow a sibling/research cache to fill an omitted proof import.
        contaminated = any(module_bundle(path, module) for module in plan["records"])
        if contaminated:
            raise ValueError("A supplied external artifact root contains local proof modules; use --reuse-from explicitly")
        tree = artifact_tree(path, include_runtime=True)
        if not tree["olean_files"]:
            continue
        trees.append(tree)
        roots.append(path)
    if not roots and any(module.startswith("Mathlib.") for module in plan["external"]):
        raise ValueError("Supply built Mathlib/dependency directories using --external-path or lake env")
    return roots, trees


def module_fingerprints(plan, environment: dict) -> dict[str, str]:
    result = {}
    for module in plan["ordered"]:
        record = plan["records"][module]
        dependencies = [[dep, result.get(dep, digest({"external": dep, "environment": environment}))]
                        for dep in record["imports"]]
        result[module] = digest({"module": module, "source": record["sha256"],
                                 "imports": dependencies, "environment": environment,
                                 "owner_inputs": plan["owner_inputs"][record["owner"]]})
    return result


def validate_receipt(plan, receipt: dict, *, artifacts: Path | None = None,
                     logs: Path | None = None, environment: dict | None = None) -> None:
    if receipt.get("schema_version") != 2 or receipt.get("policy") != POLICY:
        raise ValueError("Historical or unsupported receipt; it is not an independent-project success")
    if receipt.get("complete") is not True:
        raise ValueError("Incomplete project verification receipt")
    if receipt.get("project") != plan["manifest"]["project"] or receipt.get("targets") != plan["targets"]:
        raise ValueError("Receipt belongs to another project/target set")
    if receipt.get("inputs") != plan["inputs"] or receipt.get("closure_sha256") != plan["closure_sha256"]:
        raise ValueError("Stale project source/configuration/verifier receipt")
    if receipt.get("owner_inputs") != plan["owner_inputs"]:
        raise ValueError("Stale configuration of an actual dependency owner")
    saved_env = receipt["environment"]
    if saved_env.get("policy") != POLICY or saved_env.get("verifier_sha256_lf") != file_hash(CORE, lf=True):
        raise ValueError("Stale verifier policy/environment")
    if saved_env.get("dependency_revisions") != dependency_revisions(plan):
        raise ValueError("Changed pinned dependency environment")
    for key in ("compiler_executable_sha256", "actual_compiler_sha256"):
        if not re.fullmatch(r"[a-f0-9]{64}", saved_env.get(key, "")):
            raise ValueError("Missing content identity of the actual compiler")
    for tree in [saved_env.get("lean_sysroot_artifacts", {})] + saved_env.get("external_artifact_trees", []):
        if not re.fullmatch(r"[a-f0-9]{64}", tree.get("sha256", "")) or not tree.get("olean_files") or "import_sidecars" not in tree:
            raise ValueError("Missing complete import-artifact environment identity")
    version = saved_env.get("compiler_version_output", "")
    if not re.search(r"version 4\.33\.1(?:,|\s|$)", version) or receipt.get("compiler") != version.strip():
        raise ValueError("Missing/inconsistent compiler identity")
    if environment is not None and saved_env != environment:
        raise ValueError("Actual external/compiler environment differs from the saved run")
    records = receipt.get("modules", {})
    if set(records) != set(plan["records"]):
        raise ValueError("Receipt module set is not the exact current closure")
    fingerprints = module_fingerprints(plan, saved_env)
    reports, fresh, reused = 0, 0, 0
    for module, record in records.items():
        if record.get("fingerprint") != fingerprints[module]:
            raise ValueError(f"Stale transitive source/environment fingerprint: {module}")
        observed = record.get("reports", [])
        wanted = plan["requested"][module]
        if wanted is not None and [report["requested"] for report in observed] != wanted:
            raise ValueError(f"Wrong requested-theorem list in receipt: {module}")
        for report in observed:
            if set(report["axioms"]) - ALLOWED_AXIOMS:
                raise ValueError(f"Unexpected axiom in receipt: {module}")
            clean = report["requested"].removeprefix("_root_.")
            if report["name"] != clean and not report["name"].endswith("." + clean):
                raise ValueError(f"Wrong reported theorem: {module}")
        if record.get("axiom_reports") != len(observed):
            raise ValueError(f"Inconsistent axiom report count: {module}")
        bundle = record.get("artifact_bundle", {})
        if not bundle.get(".olean") or bundle.get(".olean") != record.get("olean_sha256") or set(bundle) - set(IMPORT_SUFFIXES):
            raise ValueError(f"Incomplete import-artifact certification: {module}")
        if any(not re.fullmatch(r"[a-f0-9]{64}", value) for value in bundle.values()):
            raise ValueError(f"Malformed artifact hash: {module}")
        if record.get("certification") == "fresh-source-compilation":
            fresh += 1
        elif record.get("certification") == "reused-current-schema-2" and record.get("reused_from"):
            reused += 1
        else:
            raise ValueError(f"Missing fresh/reused certification: {module}")
        if artifacts is not None:
            if module_bundle(artifacts, module) != bundle:
                raise ValueError(f"Missing/changed compiled artifact: {module}")
        if logs is not None:
            log = logs / (module + ".log")
            if not log.is_file() or file_hash(log, lf=True) != record.get("log_sha256_lf"):
                raise ValueError(f"Missing/changed build log: {module}")
            if parse_reports(log.read_text(encoding="utf-8"), [r["requested"] for r in observed]) != observed:
                raise ValueError(f"Actual axiom log differs from receipt: {module}")
        reports += len(observed)
    if receipt.get("total_proof_modules") != len(records) or receipt.get("axiom_reports") != reports:
        raise ValueError("Inconsistent project module/report total")
    if receipt.get("fresh_modules") != fresh or receipt.get("reused_modules") != reused:
        raise ValueError("Inconsistent fresh/reused module accounting")
    for module, record in receipt.get("final_logs", {}).items():
        if module not in records:
            raise ValueError("Final log is outside the current source closure")
        log = scoped_path(plan["directory"], record["path"])
        if not log.is_relative_to((plan["directory"] / "verification").resolve()) or not log.is_file():
            raise ValueError("Final log path is missing or outside verification/")
        if file_hash(log, lf=True) != records[module]["log_sha256_lf"] or record["sha256_lf"] != records[module]["log_sha256_lf"]:
            raise ValueError(f"Changed published final log: {module}")
        if record.get("axiom_reports") != records[module]["axiom_reports"]:
            raise ValueError(f"Incorrect published final log count: {module}")
        if parse_reports(log.read_text(encoding="utf-8"), [r["requested"] for r in records[module]["reports"]]) != records[module]["reports"]:
            raise ValueError(f"Incorrect published final axiom reports: {module}")
    if "final_logs" in receipt and not set(plan["targets"]) <= set(receipt["final_logs"]):
        raise ValueError("Published receipt is missing a target log")


def stop_tree(process: subprocess.Popen) -> None:
    if process.poll() is not None:
        return
    if os.name == "nt":
        subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       creationflags=subprocess.CREATE_NO_WINDOW, timeout=15, check=False)
    else:
        os.killpg(process.pid, signal.SIGKILL)
    process.wait(timeout=15)


def publish(plan, receipt, logs):
    published = dict(receipt)
    published["final_logs"] = {}
    selected = set(plan["targets"]) | {module for module in plan["records"]
        if module.endswith(("DefinitionFidelity", "Compression", "SemanticWellFounded"))}
    for module in sorted(selected):
        path = plan["directory"] / "verification" / (module + ".log")
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(logs / (module + ".log"), path)
        published["final_logs"][module] = {"path": path.relative_to(plan["directory"]).as_posix(),
            "sha256_lf": receipt["modules"][module]["log_sha256_lf"],
            "axiom_reports": receipt["modules"][module]["axiom_reports"]}
    validate_receipt(plan, published)
    atomic_json(plan["directory"] / "VERIFICATION.json", published)


def main(project_root: Path, argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--check-receipt", action="store_true", help="Validate the published current-project receipt; no kernel run")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--external-path", action="append", default=[])
    parser.add_argument("--bms-source", type=Path)
    parser.add_argument("--seconds", type=int, default=120)
    parser.add_argument("--memory-mb", type=int, default=2048)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--publish", action="store_true")
    parser.add_argument("--reuse-from", type=Path, action="append", default=[],
                        help="Explicitly reuse artifacts/logs from an independently current schema-2 project; never claimed fresh")
    args = parser.parse_args(argv)
    if not (10 <= args.seconds <= 600 and 512 <= args.memory_mb <= 4096):
        parser.error("Require 10..600 seconds/module and 512..4096 MiB/compiler")
    plan = load_plan(project_root, args.bms_source, allow_missing_bms=args.check_only or args.check_receipt)
    project = plan["manifest"]["project"]
    print(f"{project}: exact closure {len(plan['ordered'])}; external boundary {len(plan['external'])}", flush=True)
    if args.check_receipt:
        receipt = json.loads((plan["directory"] / "VERIFICATION.json").read_text(encoding="utf-8"))
        validate_receipt(plan, receipt)
        print("CURRENT PUBLISHED RECEIPT (record check, not a new kernel run)")
        return 0
    if args.check_only:
        absent = sum(not path.is_file() for path in plan["sources"].values())
        print(f"SOURCE CHECK PASSED; {absent} pinned BMS source entries awaiting fetch")
        return 0
    executable = Path(shutil.which(args.lean) or args.lean).resolve()
    version = subprocess.check_output([str(executable), "--version"], text=True, timeout=20)
    if not re.search(r"version 4\.33\.1(?:,|\s|$)", version):
        raise ValueError(f"Expected Lean 4.33.1, got {version.strip()}")
    search = [Path(path) for path in (args.external_path or os.environ.get("LEAN_PATH", "").split(os.pathsep)) if path]
    if not args.external_path:
        # Lake env supplies its own project artifacts too. Remove those rather
        # than accepting them as trusted external dependencies.
        search = [path for path in search if not any(
            path.joinpath(*module.split(".")).with_suffix(".olean").is_file() for module in plan["records"])]
    print("Hashing external import bundles and compiler sysroot (no dependency compilation)", flush=True)
    search, trees = external_environment(search, plan)
    prefix = Path(subprocess.check_output([str(executable), "--print-prefix"], text=True, timeout=20).strip()).resolve()
    if not (prefix / "lib/lean/Init.olean").is_file():
        raise ValueError("Cannot resolve the compiler's actual Lean sysroot")
    actual_compiler = prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    if not actual_compiler.is_file():
        raise ValueError("Cannot identify the actual compiler behind its launcher")
    sysroot_tree = artifact_tree(prefix, include_runtime=True)
    environment = {"policy": POLICY, "verifier_sha256_lf": file_hash(CORE, lf=True),
                   "compiler_version_output": version, "compiler_executable_sha256": file_hash(executable),
                   "actual_compiler_sha256": file_hash(actual_compiler),
                   "lean_sysroot_artifacts": sysroot_tree,
                   "dependency_revisions": dependency_revisions(plan), "external_artifact_trees": trees}
    fingerprints = module_fingerprints(plan, environment)
    build = plan["directory"] / ".build"
    output, logs = build / "lean", build / "logs"
    output.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    # The first search root must not shadow a hashed external/sysroot module.
    present = {".".join(path.relative_to(output).parts)[:-len(suffix)]
               for path in output.rglob("*") if path.is_file()
               and (suffix := artifact_suffix(path)) is not None}
    if present - set(plan["records"]):
        raise ValueError("Out-of-closure artifacts in project output; use a clean output tree: "
                         + ", ".join(sorted(present - set(plan["records"]))))
    receipt_path = build / "verification.json"
    candidates = []
    if args.resume and receipt_path.is_file():
        previous = json.loads(receipt_path.read_text(encoding="utf-8"))
        try:
            validate_receipt(plan, previous, artifacts=output, logs=logs, environment=environment)
            candidates.append((plan, previous, output, logs))
        except (ValueError, KeyError, OSError) as error:
            print(f"RESUME NOT CURRENT; rebuilding: {error}", flush=True)
    for directory in args.reuse_from:
        other = load_plan(directory, args.bms_source, allow_missing_bms=False)
        if other["repository"] != plan["repository"]:
            raise ValueError("Artifact reuse must come from another project in this source repository")
        previous = json.loads((other["directory"] / ".build/verification.json").read_text(encoding="utf-8"))
        other_output, other_logs = other["directory"] / ".build/lean", other["directory"] / ".build/logs"
        validate_receipt(other, previous, artifacts=other_output, logs=other_logs, environment=environment)
        candidates.append((other, previous, other_output, other_logs))
    receipt = {"schema_version": 2, "policy": POLICY, "project": project, "targets": plan["targets"],
               "compiler": version.strip(), "environment": environment, "inputs": plan["inputs"],
               "owner_inputs": plan["owner_inputs"], "closure_sha256": plan["closure_sha256"],
               "complete": False, "modules": {}, "verified_on": time.strftime("%Y-%m-%d"),
               "fresh_modules": 0, "reused_modules": 0,
               "limits": {"concurrent_compilers": 1, "compiler_threads": 1,
                          "memory_mb": args.memory_mb, "seconds_per_module": args.seconds},
               "scope": "Ordinary Lean, not an internal KP derivation; no order-type comparison or VM verification.",
               "mathlib_rebuilt_from_source": False, "network_bootstrap_tested": False}
    # Before the first compiler starts, invalidate the current attempt on disk.
    atomic_json(receipt_path, receipt)
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(output)] + [str(path) for path in search])
    env["LEAN_NUM_THREADS"] = "1"
    started = time.monotonic()
    try:
        for index, module in enumerate(plan["ordered"], 1):
            target = output.joinpath(*module.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            log = logs / (module + ".log")
            reused = None
            for other, prior, prior_output, prior_logs in candidates:
                record = prior["modules"].get(module)
                if record and record["fingerprint"] == fingerprints[module]:
                    old_target = module_artifact(prior_output, module, ".olean")
                    if old_target.resolve() != target.resolve():
                        clear_module_bundle(output, module)
                        for suffix in record["artifact_bundle"]:
                            shutil.copyfile(module_artifact(prior_output, module, suffix),
                                            module_artifact(output, module, suffix))
                    old_log = prior_logs / (module + ".log")
                    if old_log.resolve() != log.resolve():
                        shutil.copyfile(old_log, log)
                    reused = dict(record)
                    reused["certification"] = "reused-current-schema-2"
                    reused["reused_from"] = other["manifest"]["project"]
                    break
            if reused is not None:
                receipt["modules"][module] = reused
                receipt["reused_modules"] += 1
                print(f"REUSE {index}/{len(plan['ordered'])} {module}", flush=True)
            else:
                clear_module_bundle(output, module)
                command = [str(executable), "-M", str(args.memory_mb), "-j", "1", "-R",
                           str(plan["source_roots"][module]), "-o", str(target), str(plan["sources"][module])]
                options = {"creationflags": subprocess.CREATE_NO_WINDOW} if os.name == "nt" else {"start_new_session": True}
                tick = time.monotonic()
                with log.open("w", encoding="utf-8") as stream:
                    process = subprocess.Popen(command, cwd=plan["directory"], env=env,
                                               stdout=stream, stderr=subprocess.STDOUT, **options)
                    try:
                        code = process.wait(timeout=args.seconds)
                    finally:
                        stop_tree(process)
                content = log.read_text(encoding="utf-8")
                if code != 0:
                    raise RuntimeError(f"Compiler failed for {module}:\n{content[-5000:]}")
                reports = parse_reports(content, plan["requested"][module])
                record = {"fingerprint": fingerprints[module], "olean_sha256": file_hash(target),
                          "artifact_bundle": module_bundle(output, module),
                          "log_sha256_lf": file_hash(log, lf=True), "reports": reports,
                          "axiom_reports": len(reports), "seconds": round(time.monotonic() - tick, 3),
                          "certification": "fresh-source-compilation"}
                receipt["modules"][module] = record
                receipt["fresh_modules"] += 1
                print(f"PASS {index}/{len(plan['ordered'])} {module} ({record['seconds']}s)", flush=True)
            atomic_json(receipt_path, receipt)
        receipt.update(complete=True, total_proof_modules=len(plan["ordered"]),
                       axiom_reports=sum(record["axiom_reports"] for record in receipt["modules"].values()),
                       wall_seconds=round(time.monotonic() - started, 3),
                       verification_kind="fresh complete scope" if not receipt["reused_modules"] else "source-checked scope with explicitly certified artifact reuse")
        validate_receipt(plan, receipt, artifacts=output, logs=logs, environment=environment)
        atomic_json(receipt_path, receipt)
        if args.publish:
            publish(plan, receipt, logs)
        print(f"VERIFIED {project}: {len(plan['ordered'])} modules, {receipt['axiom_reports']} reports; "
              f"fresh={receipt['fresh_modules']}, reused={receipt['reused_modules']}", flush=True)
        return 0
    except BaseException as error:
        receipt.update(complete=False, failure_type=type(error).__name__,
                       wall_seconds=round(time.monotonic() - started, 3))
        atomic_json(receipt_path, receipt)
        raise


@contextmanager
def project_lock(project_root: Path):
    directory = project_root.resolve() / ".build"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "verification.lock"
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        raise ValueError("This scope is locked by another verifier or interrupted run; inspect .build/verification.lock before removing it") from None
    try:
        with os.fdopen(descriptor, "w", encoding="ascii") as stream:
            stream.write(str(os.getpid()) + "\n")
        yield
    finally:
        path.unlink()


def entry(project_root: Path) -> int:
    try:
        if any(arg in sys.argv for arg in ("--check-only", "--check-receipt", "--help", "-h")):
            return main(project_root)
        with project_lock(project_root):
            return main(project_root)
    except (ValueError, RuntimeError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        return 1


def check_release_receipts(repository: Path) -> None:
    """Aggregate source/receipt check, with no proof compilation or downloads."""
    lean = repository / "lean"
    layout = json.loads((lean / "layout.json").read_text(encoding="utf-8"))
    projects = layout["projects"]
    plans, receipts = {}, {}
    for name, item in projects.items():
        directory = scoped_path(repository, item["directory"])
        plan = load_plan(directory, allow_missing_bms=True)
        if plan["manifest"]["project"] != name:
            raise ValueError("Layout/project identity mismatch")
        receipt = json.loads((directory / "VERIFICATION.json").read_text(encoding="utf-8"))
        validate_receipt(plan, receipt)
        plans[name], receipts[name] = plan, receipt
    aggregate = plans["aggregate"]
    actual = {}
    for name, plan in plans.items():
        for module, record in plan["records"].items():
            if record["owner"] == name:
                actual[module] = {"owner": name, **({"file": record["file"]} if "file" in record
                                                    else {"external": True})}
    if actual != layout["modules"] or set(actual) != set(aggregate["records"]):
        raise ValueError("Aggregate catalog/layout does not exactly cover uniquely owned modules")
    aggregate_records = receipts["aggregate"]["modules"]
    for name, receipt in receipts.items():
        for module, record in receipt["modules"].items():
            expected = aggregate_records[module]
            if record["fingerprint"] != expected["fingerprint"]:
                raise ValueError(f"Cross-project dependency/environment disagreement: {name}/{module}")
    print(f"Independent Lean receipts current: {len(plans)} scopes, {len(actual)} distinct modules")
