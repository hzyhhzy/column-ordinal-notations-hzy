"""Check bilingual entry points, relative links, selected scripts, and Lean closure.

Uses only the standard library. It does not install packages or run expansions.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {'.build', '.lake', 'tmp', '__pycache__', 'node_modules', '.git'}
NER_HASHES = {
    'notations/RPD/RPD-mountain.ne-rewritten.js': 'a679d2a0e081729f628cebc694379925233acab4c96bfb6d05ea8f83f1c1c24b',
    'notations/LRD/LRD.ne-rewritten.js': '394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1',
    'notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js': 'fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab',
}


def release_files(folder=ROOT):
    for child in sorted(folder.iterdir()):
        if child.is_dir():
            if child.name not in IGNORED:
                yield from release_files(child)
        else:
            yield child


def main():
    files = list(release_files())
    problems, links = [], 0
    markdown = [p for p in files if p.suffix.lower() == '.md']
    pdfs = [p for p in files if p.suffix.lower() == '.pdf']
    for path in markdown:
        zh = path.name.endswith('.zh-CN.md')
        partner = path.with_name(path.name.replace('.zh-CN.md', '.md') if zh else path.stem+'.zh-CN.md')
        if not partner.is_file():
            problems.append(f'Missing language counterpart: {path.relative_to(ROOT)}')
        content = path.read_text(encoding='utf-8-sig')
        first = content.splitlines()[0]
        if not first.startswith('# ') or f']({partner.name})' not in first:
            problems.append(f'H1 missing language link: {path.relative_to(ROOT)}')
        if re.search(r'^\s*\$\s*$', content, re.M):
            problems.append(f'Broken single-dollar display delimiter: {path.relative_to(ROOT)}')
        content = re.sub(r'```.*?```', '', content, flags=re.S)
        content = re.sub(r'`[^`]*`', '', content)
        for match in re.finditer(r'\[[^\]\n]+\]\(([^)\s]+)\)', content):
            target = match.group(1).strip('<>')
            parsed = urlsplit(target)
            if parsed.scheme or not parsed.path:
                continue
            links += 1
            destination = (path.parent / unquote(parsed.path)).resolve()
            if not destination.is_relative_to(ROOT.resolve()):
                problems.append(f'Link escapes package: {path.relative_to(ROOT)} -> {target}')
            elif not destination.exists():
                problems.append(f'Broken link: {path.relative_to(ROOT)} -> {target}')
    expected_pdfs = {
        f'notations/{notation}/definition{lang}.pdf'
        for notation in ('RPD','LRD','Omega-LRD3') for lang in ('','.zh-CN')
    } | {f'proofs/paper/well-ordering{lang}.pdf' for lang in ('','.zh-CN')}
    actual_pdfs = {p.relative_to(ROOT).as_posix() for p in pdfs}
    if actual_pdfs != expected_pdfs:
        problems.append(f'PDF inventory mismatch: {actual_pdfs ^ expected_pdfs}')
    for path in pdfs:
        if not path.with_suffix('.md').is_file() or path.stat().st_size < 1000:
            problems.append(f'Invalid PDF/source pair: {path.relative_to(ROOT)}')
    if {p.name for p in (ROOT/'notations').iterdir() if p.is_dir()} != {'RPD','LRD','Omega-LRD3'}:
        problems.append('Unexpected notation directory')
    for relative, expected in NER_HASHES.items():
        actual = hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()
        if actual != expected:
            problems.append(f'NER snapshot changed: {relative}')
    for path in files:
        if path.suffix in ('.olean', '.ilean', '.o', '.exe', '.dll', '.pyc'):
            problems.append(f'Generated binary in release inventory: {path.relative_to(ROOT)}')
        if path.suffix in ('.md','.py','.js','.cjs','.json','.lean') and path != Path(__file__).resolve():
            content = path.read_text(encoding='utf-8-sig')
            if re.search(r'(?:[A-Z]:[\\/]+Users[\\/]|/Users/|/home/[^/]+/|Tencent Files)', content):
                problems.append(f'Private absolute path: {path.relative_to(ROOT)}')
    report_file = ROOT/'tools/pdf-build-report.json'
    if report_file.exists():
        for record in json.loads(report_file.read_text(encoding='utf-8')):
            path = ROOT/record['pdf'].replace('\\','/')
            if hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
                problems.append(f'Stale PDF report hash: {record["pdf"]}')
    result = subprocess.run([sys.executable, '-B', str(ROOT/'lean/build.py'), '--check-only'],
                            text=True, encoding='utf-8', capture_output=True, timeout=40)
    if result.returncode:
        problems.append('Lean closure check failed: '+result.stdout+result.stderr)
    else:
        print(result.stdout.strip())
    if problems:
        print('\n'.join(problems))
        raise SystemExit(1)
    print(f'PASS: {len(markdown)} bilingual Markdown files, {len(pdfs)} PDFs, {links} local links, '
          f'3 unchanged NER scripts; {len(files)} release files, {sum(p.stat().st_size for p in files):,} bytes.')


if __name__ == '__main__':
    main()
