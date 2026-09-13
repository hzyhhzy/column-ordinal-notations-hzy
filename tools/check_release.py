"""Check bilingual files, links, snapshots, Lean closure, and verification receipts.

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
    'notations/RPD/RPD-mountain.ne-rewritten.js': '447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026',
    'notations/LRD/LRD.ne-rewritten.js': '394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1',
    'notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js': 'fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab',
    'notations/ARD/ARD-arcs.ne-rewritten.js': 'ab4f05ef1fb65b6308e710cbbc98c173310f9c3073ce3a57082863af708841d6',
}


def release_files(folder=ROOT):
    for child in sorted(folder.iterdir()):
        if child.is_dir():
            if child.name not in IGNORED:
                yield from release_files(child)
        else:
            yield child


def sha256_lf(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def check_lean_receipt(problems):
    """Reject a successful but stale build record; this does not rerun Lean."""
    folder = ROOT/'lean'
    manifest = json.loads((folder/'sources.json').read_text(encoding='utf-8'))
    receipt = json.loads((folder/'VERIFICATION.json').read_text(encoding='utf-8'))
    modules = receipt.get('modules', {})
    expected = manifest['modules']
    if receipt.get('complete') is not True:
        problems.append('Lean verification receipt is incomplete')
    if set(modules) != set(expected):
        problems.append('Lean verification receipt does not cover the current source closure')
    if receipt.get('total_proof_modules') != len(expected):
        problems.append('Lean verification receipt has a stale module count')
    if receipt.get('axiom_reports') != sum(record['axiom_reports'] for record in modules.values()):
        problems.append('Lean verification receipt has an inconsistent axiom-report total')
    version = receipt.get('compiler_version_output', '')
    if not version or version.strip() != receipt.get('compiler'):
        problems.append('Lean verification receipt lacks consistent raw compiler-version output')
    fingerprints, visiting = {}, set()

    def fingerprint(module):
        if module not in expected:
            return module
        if module in fingerprints:
            return fingerprints[module]
        if module in visiting:
            raise ValueError(f'Cycle in Lean verification manifest: {module}')
        visiting.add(module)
        record = expected[module]
        value = hashlib.sha256((record['sha256'] + version + ''.join(
            fingerprint(dep) for dep in record['imports'])).encode()).hexdigest()
        visiting.remove(module)
        fingerprints[module] = value
        return value

    for module in expected:
        if fingerprint(module) != modules.get(module, {}).get('fingerprint'):
            problems.append(f'Stale Lean module/dependency fingerprint: {module}')
    for relative, field in (
        ('sources.json', 'sources_manifest_sha256_lf'),
        ('build.py', 'build_script_sha256_lf'),
        ('lakefile.lean', 'lakefile_sha256_lf'),
        ('lake-manifest.json', 'lake_manifest_sha256_lf'),
    ):
        if sha256_lf(folder/relative) != receipt.get(field):
            problems.append(f'Stale Lean verification input hash: {relative}')
    logs = receipt.get('final_logs', {})
    required = {'FiniteDemandYFinal', 'FiniteDemandRPDFinal', 'FiniteDemandLRDFinal',
                'OmegaLRD3Final', 'ARDFinal', manifest['target']}
    if not required <= set(logs):
        problems.append('Lean verification receipt is missing current final theorem logs')
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    for module, record in logs.items():
        path = (folder/record['path']).resolve()
        if not path.is_relative_to((folder/'verification').resolve()) or not path.is_file():
            problems.append(f'Invalid Lean final-log path: {module}')
            continue
        if sha256_lf(path) != record['sha256_lf']:
            problems.append(f'Stale Lean final-log hash: {module}')
        content = path.read_text(encoding='utf-8')
        reports = re.findall(
            r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", content)
        if (len(reports) != record['axiom_reports'] or
                len(reports) != modules.get(module, {}).get('axiom_reports')):
            problems.append(f'Incomplete Lean final-log axiom reports: {module}')
        for _, report in reports:
            if {item.strip() for item in report.split(',') if item.strip()} - allowed_axioms:
                problems.append(f'Unexpected axiom in Lean final log: {module}')


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
        for notation in ('RPD','LRD','Omega-LRD3','ARD') for lang in ('','.zh-CN')
    } | {f'proofs/paper/{paper}{lang}.pdf'
         for paper in ('well-ordering','ard-well-ordering') for lang in ('','.zh-CN')}
    actual_pdfs = {p.relative_to(ROOT).as_posix() for p in pdfs}
    if actual_pdfs != expected_pdfs:
        problems.append(f'PDF inventory mismatch: {actual_pdfs ^ expected_pdfs}')
    for path in pdfs:
        if not path.with_suffix('.md').is_file() or path.stat().st_size < 1000:
            problems.append(f'Invalid PDF/source pair: {path.relative_to(ROOT)}')
    if {p.name for p in (ROOT/'notations').iterdir() if p.is_dir()} != {'RPD','LRD','Omega-LRD3','ARD'}:
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
        records = json.loads(report_file.read_text(encoding='utf-8'))
        if {record['pdf'].replace('\\','/') for record in records} != expected_pdfs:
            problems.append('PDF build report does not cover the current PDF inventory')
        for record in records:
            path = ROOT/record['pdf'].replace('\\','/')
            if hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
                problems.append(f'Stale PDF report hash: {record["pdf"]}')
    else:
        problems.append('Missing PDF build report')
    check_lean_receipt(problems)
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
          f'{len(NER_HASHES)} pinned NER snapshots; {len(files)} release files, {sum(p.stat().st_size for p in files):,} bytes.')


if __name__ == '__main__':
    main()
