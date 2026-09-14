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
# Exact pre-existing historical drafts, verified tracked and unchanged at the
# SPD integration baseline. Only counterpart/H1-language-link checks are
# waived; headings, formula delimiters, links and all other checks still run.
# Do not replace this inventory with directory-level or suffix-based rules.
MONOLINGUAL_ARCHIVES = frozenset({
    'notations/RPD/y-lower-bound/algorithm.zh-CN.md',
    'notations/RPD/y-lower-bound/BMS-SEED-LOWER-BOUND.zh-CN.md',
    'notations/RPD/y-lower-bound/DILATED-GEOMETRIC-Y.zh-CN.md',
    'notations/RPD/y-lower-bound/DILATION-AND-STAR-BOUNDS.zh-CN.md',
    'notations/RPD/y-lower-bound/GENERAL-PROTECTED-Y-COMPILER.zh-CN.md',
    'notations/RPD/y-lower-bound/PROTECTED-SUBSTITUTION.zh-CN.md',
    'notations/RPD/y-lower-bound/SOURCES.md',
    'research/ordinal-comparisons-20260914/01-bounds-and-y-rpd.zh-CN.md',
    'research/ordinal-comparisons-20260914/02-ard2-vs-ipd.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/ard2-ipd-bound/full-context-strength.md',
    'research/ordinal-comparisons-20260914/archive/ard2-ipd-bound/HOUR-REPORT.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/ard2-ipd-bound/REPORT.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/ARD-TPD-tightening.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/IPD-upper-bounds.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/RPD-Y-wY-tightening.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/STATUS.md',
    'research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/TEST-REPORT.md',
    'research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/Y-le-RPD-proof.zh-CN.md',
    'research/ordinal-comparisons-20260914/archive/README.zh-CN.md',
    'research/ordinal-comparisons-20260914/README.zh-CN.md',
    'research/README.md',
})
NER_HASHES = {
    'notations/RPD/RPD-mountain.ne-rewritten.js': '447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026',
    'notations/LRD/LRD.ne-rewritten.js': '394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1',
    'notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js': 'fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab',
    'notations/ARD/ARD-arcs.ne-rewritten.js': 'ab4f05ef1fb65b6308e710cbbc98c173310f9c3073ce3a57082863af708841d6',
    'notations/IPD/IPD.ne-rewritten.js': 'acc1a1c2ae260da9be7d13e14ac17d84a92679f82efe97aa85cd0e3b072f6011',
    'notations/ARD2/ARD2.ne-rewritten.js': 'e0d4eb14056ee54a6d4a8d2475241469ba33f07d38c406cfa9b20c648407380d',
    'notations/SPD/SPD.ne-rewritten.js': 'd693c23564a766ecbbe3072cd200632c49b490d47d18428e1310ea438e85f266',
}
LEAN_ROOTS = {
    # SPD has a paper manuscript, but no Lean certificate. Its addition must
    # neither relabel the existing seven proofs nor weaken their receipt checks.
    'Y': ['FiniteDemandYFinal'],
    'RPD': ['FiniteDemandRPDFinal'],
    'LRD': ['FiniteDemandLRDFinal'],
    'Omega-LRD3': ['OmegaLRD3Final'],
    'ARD': ['ARDFinal', 'ARDCompression'],
    'IPD': ['IPDStandardOrder', 'IPDTreeCompare'],
    'ARD2': ['ARD2Final', 'ARD2Compression'],
    'shared': ['ARDPrefixOrder', 'FiniteDemandColumnWellFounded',
               'OrdinalFormal.ColumnMap', 'OrdinalFormal.ColumnReachability',
               'OrdinalFormal.GeneratedColumnDecrease', 'OrdinalFormal.RPDFiniteUnion'],
    'aggregate': ['SevenNotationFinalAudit'],
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


def load_release_lean_plans(repository):
    """Check the exact nine-scope catalog without requiring completed receipts."""
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(repository / 'lean'))
    from verification_core import load_plan
    layout = json.loads((repository / 'lean/layout.json').read_text(encoding='utf-8'))
    if layout.get('schema_version') != 1 or layout.get('file_base') != 'repository':
        raise ValueError('Unsupported source-ownership layout')
    projects = layout['projects']
    if set(projects) != set(LEAN_ROOTS):
        raise ValueError('Layout must contain exactly seven notations, shared, and aggregate')
    plans = {}
    for name, roots in LEAN_ROOTS.items():
        item = projects[name]
        directory = 'lean' if name == 'aggregate' else 'lean/' + name
        if item.get('directory') != directory or item.get('manifest') != directory + '/sources.json':
            raise ValueError(f'Unexpected project directory/manifest: {name}')
        plan = load_plan(repository / directory, allow_missing_bms=True)
        if plan['repository'] != repository.resolve() or plan['manifest']['project'] != name:
            raise ValueError(f'Layout/project/repository identity mismatch: {name}')
        if plan['targets'] != roots or item.get('targets') != roots:
            raise ValueError(f'Missing or changed final/bridge roots: {name}')
        expected_owned = sorted(module for module, record in plan['records'].items()
                                if record['owner'] == name and record.get('origin') != 'BMS')
        expected_external = sorted(module for module, record in plan['records'].items()
                                   if record.get('origin') == 'BMS')
        for field, expected in (
            ('owned_modules', expected_owned), ('external_modules', expected_external),
            ('closure_modules', sorted(plan['records'])), ('external', sorted(plan['external'])),
        ):
            if item.get(field) != expected:
                raise ValueError(f'Layout {field} differs from actual exact scope: {name}')
        if expected_external and name not in ('Y', 'aggregate'):
            raise ValueError(f'External BMS unexpectedly required outside Y: {name}')
        plans[name] = plan
    canonical = plans['aggregate']['records']
    owned = {}
    for name, plan in plans.items():
        for module, record in plan['records'].items():
            if module not in canonical or record != canonical[module]:
                raise ValueError(f'Conflicting per-project source record: {name}/{module}')
            if record['owner'] not in plans:
                raise ValueError(f'Unknown source owner: {module}')
            if record.get('origin') != 'BMS' and record.get('external'):
                raise ValueError(f'Bundled source incorrectly marked external: {module}')
            if record['owner'] == name:
                if module in owned:
                    raise ValueError(f'Duplicate physical source ownership: {module}')
                owned[module] = {'owner': name, **(
                    {'external': True} if record.get('origin') == 'BMS' else {'file': record['file']})}
    if owned != layout['modules'] or set(owned) != set(canonical):
        raise ValueError('Aggregate/layout does not exactly cover uniquely owned sources and external BMS')
    leaf_union = set().union(*(set(plan['records']) for name, plan in plans.items()
                              if name not in ('shared', 'aggregate')))
    joint = {module for module, record in canonical.items() if record['owner'] == 'aggregate'}
    if leaf_union | joint != set(canonical) or leaf_union & joint:
        raise ValueError('Aggregate must be precisely the seven leaf closures plus joint audit entries')
    return plans


def check_lean_receipt(problems):
    """Require current public receipts for all exact scopes; never use archives."""
    try:
        plans = load_release_lean_plans(ROOT)
    except (ValueError, KeyError, OSError) as error:
        problems.append('Independent Lean layout check failed: ' + str(error))
        return
    from verification_core import validate_receipt
    receipts = {}
    for name, plan in plans.items():
        try:
            path = plan['directory'] / 'VERIFICATION.json'
            if not path.is_file():
                raise ValueError('Missing current public VERIFICATION.json (historical receipts do not count)')
            receipt = json.loads(path.read_text(encoding='utf-8'))
            if not isinstance(receipt.get('final_logs'), dict):
                raise ValueError('Public receipt lacks its final/bridge logs')
            validate_receipt(plan, receipt)
            receipts[name] = receipt
        except (ValueError, KeyError, OSError) as error:
            problems.append(f'Independent Lean receipt check failed ({name}): {error}')
    if len(receipts) != len(plans):
        return
    aggregate = receipts['aggregate']['modules']
    for name, receipt in receipts.items():
        for module, record in receipt['modules'].items():
            if record['fingerprint'] != aggregate[module]['fingerprint']:
                problems.append(f'Cross-project source/environment disagreement: {name}/{module}')
    if not problems:
        print(f'Independent Lean receipts current: {len(plans)} scopes, {len(aggregate)} distinct modules')


def main():
    files = list(release_files())
    problems, links = [], 0
    markdown = [p for p in files if p.suffix.lower() == '.md']
    pdfs = [p for p in files if p.suffix.lower() == '.pdf']
    for relative in sorted(MONOLINGUAL_ARCHIVES):
        if not (ROOT / relative).is_file():
            problems.append(f'Missing monolingual archive: {relative}')
    archive_count = sum(p.relative_to(ROOT).as_posix() in MONOLINGUAL_ARCHIVES for p in markdown)
    for path in markdown:
        archive = path.relative_to(ROOT).as_posix() in MONOLINGUAL_ARCHIVES
        zh = path.name.endswith('.zh-CN.md')
        partner = path.with_name(path.name.replace('.zh-CN.md', '.md') if zh else path.stem+'.zh-CN.md')
        if not archive and not partner.is_file():
            problems.append(f'Missing language counterpart: {path.relative_to(ROOT)}')
        content = path.read_text(encoding='utf-8-sig')
        first = content.splitlines()[0] if content else ''
        if not first.startswith('# '):
            problems.append(f"H1 must start with '# ': {path.relative_to(ROOT)}")
        if not archive and f']({partner.name})' not in first:
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
        for notation in ('RPD','LRD','Omega-LRD3','ARD','IPD','ARD2','SPD') for lang in ('','.zh-CN')
    } | {f'proofs/paper/{paper}{lang}.pdf'
         for paper in ('well-ordering','ard-well-ordering','ipd-well-ordering','ard2-well-ordering','spd-well-ordering') for lang in ('','.zh-CN')}
    actual_pdfs = {p.relative_to(ROOT).as_posix() for p in pdfs}
    if actual_pdfs != expected_pdfs:
        problems.append(f'PDF inventory mismatch: {actual_pdfs ^ expected_pdfs}')
    for path in pdfs:
        if not path.with_suffix('.md').is_file() or path.stat().st_size < 1000:
            problems.append(f'Invalid PDF/source pair: {path.relative_to(ROOT)}')
    if {p.name for p in (ROOT/'notations').iterdir() if p.is_dir()} != {'RPD','LRD','Omega-LRD3','ARD','IPD','ARD2','SPD'}:
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
    print(f'PASS: {len(markdown)} Markdown files total '
          f'({len(markdown)-archive_count} bilingual, {archive_count} monolingual archives), '
          f'{len(pdfs)} PDFs, {links} local links, '
          f'{len(NER_HASHES)} pinned NER snapshots; {len(files)} release files, {sum(p.stat().st_size for p in files):,} bytes.')


if __name__ == '__main__':
    main()
