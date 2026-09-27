"""Verify the exact imported archive inventory and LF-normalized hashes.

Standard library only; no expansions, installation, or file writes.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path

ARCHIVE = Path(__file__).resolve().parent
ROOT = ARCHIVE.parents[2]
MANIFEST = ARCHIVE / "manifest.json"


def sha256_lf(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def verify():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise ValueError("Unsupported archive manifest")
    if manifest.get("not_a_new_proof_or_lean_certificate") is not True:
        raise ValueError("Archive proof-status boundary missing")
    records = manifest["files"]
    if len(records) != 73:
        raise ValueError("Final-route inventory must contain exactly 73 files")
    imported, manuscripts = set(), set()
    kinds = Counter()
    for record in records:
        relative = record["file"]
        path = (ROOT / relative).resolve()
        if relative in imported or not any(path.is_relative_to(ARCHIVE / part)
                                            for part in ("output", "vendor")):
            raise ValueError("Duplicate or escaping archived file: " + relative)
        imported.add(relative)
        kinds[record["kind"]] += 1
        raw = path.read_bytes().replace(b"\r\n", b"\n")
        if hashlib.sha256(raw).hexdigest() != record["packaged_sha256_lf"]:
            raise ValueError("Changed archived file: " + relative)
        if len(raw) != record["bytes"]:
            raise ValueError("Archived byte-count mismatch: " + relative)
        if record["kind"] == "original-language-manuscript":
            if path.suffix != ".md" or "归档原稿" not in raw.decode("utf-8"):
                raise ValueError("Manuscript status banner missing: " + relative)
            manuscripts.add(relative)
    if len(manuscripts) != 25:
        raise ValueError("Exact final-route manuscript inventory changed")
    actual = {
        path.relative_to(ROOT).as_posix()
        for part in ("output", "vendor")
        for path in (ARCHIVE / part).rglob("*")
        if path.is_file() and "__pycache__" not in path.parts
    }
    allowed_guides = {
        (ARCHIVE / "vendor" / name).relative_to(ROOT).as_posix()
        for name in ("README.md", "README.zh-CN.md")
    }
    if actual - allowed_guides != imported:
        raise ValueError("Unlisted/missing archive files: " + repr(
            sorted((actual - allowed_guides) ^ imported)))
    return {
        "schema_version": 1,
        "status": "hashes and exact imported inventory verified",
        "manifest_sha256_lf": sha256_lf(MANIFEST),
        "imported_files": len(imported),
        "original_language_manuscripts": len(manuscripts),
        "kinds": dict(sorted(kinds.items())),
        "bytes_lf": sum(record["bytes"] for record in records),
        "universal_proof": False,
    }, manuscripts


if __name__ == "__main__":
    result, _ = verify()
    print(json.dumps(result, ensure_ascii=False, indent=2))
