"""Print the exact original-language research-document inventory for review.

Redirecting the output creates no exemption by itself: the repository checker
pins the manifest hash separately. This script does not change any files.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha_lf(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main():
    records = []
    for path in sorted(ROOT.rglob("*.md")):
        partner = path.with_name(
            path.name.replace(".zh-CN.md", ".md")
            if path.name.endswith(".zh-CN.md") else path.stem + ".zh-CN.md")
        if partner.is_file():
            continue
        rel = path.relative_to(ROOT).as_posix()
        records.append({
            "path": rel, "sha256_lf": sha_lf(path),
            "kind": "original-language-proof-reading-edition"
            if rel.startswith("proofs/") else "research-publication-or-guide",
        })
    print(json.dumps({
        "schema_version": 1, "collection": "laver-table-lower-bounds",
        "source_manifest_sha256_lf": sha_lf(ROOT / "SOURCE_MANIFEST.json"),
        "monolingual_markdown": records,
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
