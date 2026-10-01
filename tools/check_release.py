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
# The 2026-09-20 manuscripts below are individually included at the user's
# explicit request to preserve proof drafts without bilingual duplication.
MONOLINGUAL_ARCHIVES = frozenset({
    'notations/ICP/non-well-founded.zh-CN.md',
    'research/order-comparisons/proofs/rpd-e0mn-tighter-20260917/RPD-le-e0MN-13132.zh-CN.md',
    'research/order-comparisons/proofs/ard-e0mn-cover-20260917/ARD-le-e0MN.zh-CN.md',
    'research/order-comparisons/proofs/ard2-e0mn-cover-20260917/ARD2-le-e0MN.zh-CN.md',
    'research/order-comparisons/proofs/cwy2-e0mn-cover-20260917/CWY2-wY-le-e0MN.zh-CN.md',
    'research/order-comparisons/proofs/ipd-e0mn-20260917/README.zh-CN.md',
    'research/order-comparisons/proofs/e0mn13-rpd12-20260919/README.zh-CN.md',
    'research/order-comparisons/proofs/strong-e0mn-counting-20260919/RPD-12-correspondence.zh-CN.md',
    'research/order-comparisons/proofs/e0mn-ard-embedding-20260917/README.zh-CN.md',
    'research/order-comparisons/proofs/ipd14-e0mn-20260917/e0MN-13-equals-IPD-12.zh-CN.md',
    'research/order-comparisons/proofs/substantive-wy-20260914/SKYLINE-WORDS.zh-CN.md',
    'research/order-comparisons/proofs/substantive-wy-20260914/GLOBAL-COVER-BRIDGE.md',
    'research/order-comparisons/proofs/substantive-wy-20260914/LOWERBOUND-INDEPENDENT-AUDIT.md',
    'research/order-comparisons/proofs/substantive-wy-20260914/SKYLINE-UPPERBOUND-AUDIT.md',
    'research/order-comparisons/proofs/substantive-wy-20260914/SKYLINE-NOSKIP-PROOF.md',
    'research/order-comparisons/proofs/substantive-wy-20260914/STANDARD-DOMAIN-AUDIT.md',
    'research/order-comparisons/proofs/new-notation-20260918/ACD-123595-equals-BMS.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260918/ACD-RPD-embedding-progress.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260918/ACD-BMS-lower-bound.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260918/ACD-finite-BMS-bound.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260918/ACD-smaller-BMS-bound.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260918/ACD-strict-BMS-bound.zh-CN.md',
    'research/order-comparisons/proofs/csd-20260917/BMS-small-bound.zh-CN.md',
    'research/order-comparisons/proofs/csd-20260917/BMS-embedding.zh-CN.md',
    'research/order-comparisons/proofs/icp-candidate-20260919/RPD-zero-row-sector-below-ICP-124.zh-CN.md',
    'research/order-comparisons/proofs/icp-candidate-20260919/RPD-ICP-flat-correspondence.zh-CN.md',
    'research/order-comparisons/proofs/icp-candidate-20260919/BMS-below-11242.zh-CN.md',
    'research/order-comparisons/proofs/iblp-bms-20260918/IBLP-01-BMS-lower-bound.zh-CN.md',
    'research/order-comparisons/proofs/rpd-to-e0mn-20260917/RPD-le-e0MN-14.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260918/BMS-nonstandard-row-bound.zh-CN.md',
    'research/order-comparisons/proofs/wy-linear-20260914/exact-copy-audit.md',
    'research/order-comparisons/proofs/new-notation-20260914/IPD-KP-WELL-ORDERING.zh-CN.md',
    'research/order-comparisons/proofs/new-notation-20260914/KP-LPO-RANK-LEMMA.zh-CN.md',
    'research/order-comparisons/proofs/csd-20260917/well-ordering-progress.zh-CN.md',
    'research/order-comparisons/proofs/csd-20260917/definition.zh-CN.md',
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
    'notations/CTN/CTN.ne-rewritten.js': 'bf86d434760bb904886783fca76a2c7e5808e245eb4561068c78881ac30b104b',
    'notations/SRPD/SRPD.ne-rewritten.js': 'fdbd0d0788afe0cd6949cb280ffea4c85813bbd6d5e47d04e6a078e00bbee85a',
    'notations/FMP/FMP.ne-rewritten.js': '199fd418a9ac5a684d8e5232971f98552c8cb6607b1262668f11f80cbdbbda22',
    'notations/ACD/ACD.ne-rewritten.js': '1ee4a75ddab26088163219bd78d0cdd326cf0312840a5e0adb0006bd54a7609e',
    'notations/CSD/CSD.ne-rewritten.js': '5384de992dc01caedff7efeac73dbfbf671182b97b691f3dd122d7a7acf1e247',
    'notations/ICP/ICP.ne-rewritten.js': '4c8b52c9af4d54a30783b63aa99bdad495e68833ca01d9b56352166b6809a49e',
    'external/e0MN/e0MN-fast-counting.ne-rewritten.js': '250a84c6a193eb95ade501f9e977f09ba2b599a3e3c873c9a8fc2ddaca53fdec',
    'external/strong-e0MN/strong-e0MN-fast-counting.ne-rewritten.js': '45a80dc3219ee3c2d3cc29fceca46f93464ba6ff1aa4f5649f611a97fc2311cf',
    'notations/ARD2-legacy/ARD2-legacy.ne-rewritten.js': 'e977cb008dfcd0d1738dfabd77ad137b662f8da2dbf191a10842d5a10503dfea',
    'notations/CWY/wY-CWY.ne-rewritten.js': 'c2c1c3c9f83d7b69588e95b53503e6d42c86c092aac170c2db6ffce2d5ca61f5',
    'notations/CWY2/CWY2.ne-rewritten.js': '02b4f334f4c84d5c088a740d0f0a33fee1e1821105bb1dc8baf9228ca0a1a3ee',
    'notations/Omega-CWY/Omega-CWY.ne-rewritten.js': '4750912d8fb926c05f49476ba5408bb7a51e444849509411bf4e377423429414',
    'notations/RPD/RPD-mountain.ne-rewritten.js': '447eaed4e88604a29ba4ccef329b05c57ef30d935b0a31166ff519805e352026',
    'notations/LRD/LRD.ne-rewritten.js': '394fe4763e82708a99d66c2d88d3926c86c4be92ec35174b9205a292550740b1',
    'notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js': 'fe33b1a35891e9efb9eb5932ab94456053769b6b58df41ea9f36eb57a262f3ab',
    'notations/ARD/ARD.ne-rewritten.js': '7cf745079c90e0f127b06c50c8082f81c16600aa9a76fb712f50cfa8d2b955b0',
    'notations/ARD-legacy/ARD-arcs.ne-rewritten.js': '1b80215f80c7797c1891e0c197c4ca8470cd43e9ed86d68cfb7b2b760e8d7930',
    'notations/IPD/IPD.ne-rewritten.js': 'acc1a1c2ae260da9be7d13e14ac17d84a92679f82efe97aa85cd0e3b072f6011',
    'notations/ARD2/ARD2.ne-rewritten.js': '0b50ff720cd33874f2401ea24ef2fc951ba5df21d81935b73d5bfde1aab7a562',
    'notations/SPD/SPD.ne-rewritten.js': 'd693c23564a766ecbbe3072cd200632c49b490d47d18428e1310ea438e85f266',
}
SRPD_ARCHIVE_MANIFEST_SHA256 = '41e9b307324156545e05ce64735681aa7014c1da916608f8e4163a78c2329033'
LEAN_ROOTS = {
    # SPD and FMP have paper manuscripts, but no Lean certificates. Their addition must
    # neither relabel the existing seven proofs nor weaken their receipt checks.
    'Y': ['FiniteDemandYFinal'],
    'RPD': ['FiniteDemandRPDFinal'],
    'LRD': ['FiniteDemandLRDFinal'],
    'Omega-LRD3': ['OmegaLRD3Final'],
    'ARD': ['ARDSkylineFinal'],
    'ARD-legacy': ['ARDFinal', 'ARDCompression'],
    'IPD': ['IPDStandardOrder', 'IPDTreeCompare'],
    'ARD2': ['ARD2SkylineFinal'],
    'ARD2-legacy': ['ARD2Final', 'ARD2Compression'],
    'shared': ['ARDPrefixOrder', 'FiniteDemandColumnWellFounded',
               'OrdinalFormal.ColumnMap', 'OrdinalFormal.ColumnReachability',
               'OrdinalFormal.GeneratedColumnDecrease', 'OrdinalFormal.RPDFiniteUnion'],
    'aggregate': ['ARD2RevisionFinalAudit'],
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


def check_srpd_archive():
    """Allow only the 25 individually pinned original-language manuscripts."""
    directory = ROOT / 'research/srpd-tbms/archive'
    if sha256_lf(directory / 'manifest.json') != SRPD_ARCHIVE_MANIFEST_SHA256:
        raise ValueError('SRPD archive manifest changed without explicit review')
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(directory))
    from verify_archive import verify
    integrity, manuscripts = verify()
    receipt = json.loads((directory / 'ARCHIVE-VALIDATION.json').read_text(encoding='utf-8'))
    if (receipt.get('schema_version') != 1 or receipt.get('suite') != 'current'
            or receipt.get('integrity') != integrity
            or receipt.get('universal_proof') is not False
            or receipt.get('independent_mathematical_review') is not False
            or receipt.get('status') != 'bounded archive replay reproduced'):
        raise ValueError('Stale or incorrectly scoped SRPD archive replay receipt')
    expected_tools = {f'research/srpd-tbms/archive/{name}.py'
                      for name in ('verify_archive', 'run_checks')}
    tools = receipt['checked_tools']
    if len(tools) != 2 or {r['file'] for r in tools} != expected_tools:
        raise ValueError('Archive replay tool inventory changed')
    for record in tools:
        if sha256_lf(ROOT / record['file']) != record['sha256_lf']:
            raise ValueError('Stale archive replay tool: ' + record['file'])
    runs = receipt['runs']
    expected_ids = ({f'weak:{i}' for i in range(14)} | {'weak:local', 'weak:common-gate'}
                    | {f'epsilon:{i}' for i in range(12)})
    if (len(runs) != 28 or {r['id'] for r in runs} != expected_ids
            or receipt.get('counts') != {'passed': 26, 'guarded': 2}
            or receipt.get('all_children_exited') is not True):
        raise ValueError('Archive replay is incomplete or misreports guarded cases')
    for run in runs:
        guarded = run['id'] in {'epsilon:3', 'epsilon:8'}
        if (run['status'] != ('guarded' if guarded else 'passed')
                or run['exit_code'] != (1 if guarded else 0)
                or run['timed_out'] or not run['process_exited']
                or not run['historical_semantics_match']
                or run['semantic_sha256'] != run['historical_semantic_sha256']
                or run['error_message'] != ('recursive row allocation width guard' if guarded else None)):
            raise ValueError('Invalid archive replay case: ' + run['id'])
    print(f'SRPD archive: {integrity["imported_files"]} pinned files; 26 bounded passes, 2 recorded width guards')
    return manuscripts


def load_release_lean_plans(repository):
    """Check the exact eleven-scope catalog without requiring completed receipts."""
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(repository / 'lean'))
    from verification_core import load_plan
    layout = json.loads((repository / 'lean/layout.json').read_text(encoding='utf-8'))
    if layout.get('schema_version') != 1 or layout.get('file_base') != 'repository':
        raise ValueError('Unsupported source-ownership layout')
    projects = layout['projects']
    if set(projects) != set(LEAN_ROOTS):
        raise ValueError('Layout must contain seven notations, both legacy backends, shared, and aggregate')
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
        raise ValueError('Aggregate must be precisely the declared leaf closures plus joint audit entries')
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
    archives = set(MONOLINGUAL_ARCHIVES)
    try:
        archives.update(check_srpd_archive())
    except (ValueError, KeyError, OSError) as error:
        problems.append('SRPD final-route archive: ' + str(error))
    markdown = [p for p in files if p.suffix.lower() == '.md']
    pdfs = [p for p in files if p.suffix.lower() == '.pdf']
    for relative in sorted(archives):
        if not (ROOT / relative).is_file():
            problems.append(f'Missing monolingual archive: {relative}')
    archive_count = sum(p.relative_to(ROOT).as_posix() in archives for p in markdown)
    for path in markdown:
        archive = path.relative_to(ROOT).as_posix() in archives
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
        for notation in ('RPD','LRD','Omega-LRD3','ARD','ARD-legacy','IPD','ARD2','ARD2-legacy','SPD','CWY','CWY2','Omega-CWY','FMP') for lang in ('','.zh-CN')
    } | {f'proofs/paper/{paper}{lang}.pdf'
         for paper in ('well-ordering','ard-well-ordering', 'ard-legacy-well-ordering', 'rpd-le-ard-a2','ard-le-ard2-13','ipd-well-ordering','ard2-well-ordering','ard2-legacy-well-ordering','spd-well-ordering','cwy2-equivalence','fmp-well-ordering','bms-le-fmp-12242444') for lang in ('','.zh-CN')}
    actual_pdfs = {p.relative_to(ROOT).as_posix() for p in pdfs}
    if actual_pdfs != expected_pdfs:
        problems.append(f'PDF inventory mismatch: {actual_pdfs ^ expected_pdfs}')
    for path in pdfs:
        if not path.with_suffix('.md').is_file() or path.stat().st_size < 1000:
            problems.append(f'Invalid PDF/source pair: {path.relative_to(ROOT)}')
    if {p.name for p in (ROOT/'notations').iterdir() if p.is_dir()} != {'SRPD','RPD','LRD','Omega-LRD3','ARD','ARD-legacy','IPD','ARD2','ARD2-legacy','SPD','CWY','CWY2','Omega-CWY','ACD','CSD','ICP','FMP','CTN'}:
        problems.append('Unexpected notation directory')
    for relative, expected in NER_HASHES.items():
        actual = hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()
        if actual != expected:
            problems.append(f'NER snapshot changed: {relative}')
    # CTN is the former CTN2 frontend, not a new whole-system Lean theorem.
    # Pin its renamed implementation and sparse artifact; do not revive old CTN.
    try:
        directory = ROOT / 'notations/CTN'
        manifest = json.loads((directory / 'provenance.json').read_text(encoding='utf-8'))
        if (manifest.get('schema_version') != 1 or manifest.get('notation') != 'CTN'
                or manifest.get('previous_research_name') != 'CTN2'
                or manifest.get('mathematical_rules_changed') is not False):
            raise ValueError('Unexpected CTN provenance identity/scope')
        expected = {'CTN.ne-rewritten.js', 'ctn.py', 'ctn_table.py', 'ctn_sparse.py',
                    'locate_omega_omega.py', 'fixtures/omega-omega.sparse.json'}
        records = manifest['files']
        if len(records) != len(expected) or {r['file'] for r in records} != expected:
            raise ValueError('Unexpected CTN implementation/fixture inventory')
        for record in records:
            if sha256_lf(directory / record['file']) != record['packaged_sha256']:
                raise ValueError('CTN provenance hash mismatch: ' + record['file'])
        fixture = json.loads((directory / 'fixtures/omega-omega.sparse.json').read_text(encoding='utf-8'))
        if (fixture.get('table_length') != 23191452 or fixture.get('raw_columns') != 69593927
                or len(fixture.get('nonzero_values', [])) != 4352):
            raise ValueError('CTN sparse certificate dimensions changed')
        receipt = json.loads((ROOT / 'tools/ctn-validation.json').read_text(encoding='utf-8'))
        if (receipt.get('schema_version') != 1 or receipt.get('notation') != 'CTN'
                or receipt.get('universal_proof') is not False
                or receipt.get('lean_build') is not False
                or receipt.get('browser_click_test') is not False
                or receipt.get('all_test_commands_exited') is not True):
            raise ValueError('Unexpected CTN finite-validation scope')
        expected_checks = {'notations/CTN/' + name for name in expected} | {
            'tests/ctn.cjs', 'tests/ctn_table_cases.py', 'tests/ctn_rules.py',
            'tests/ctn_small_ordinals.py', 'tests/ctn_omega_omega.py'}
        checks = receipt['checked_files']
        if len(checks) != len(expected_checks) or {r['file'] for r in checks} != expected_checks:
            raise ValueError('Unexpected CTN finite-validation inventory')
        for record in checks:
            if sha256_lf(ROOT / record['file']) != record['sha256_lf']:
                raise ValueError('Stale CTN finite-validation record: ' + record['file'])
        runs = receipt['runs']
        if len(runs) != 2 or {r['id'] for r in runs} != {'python', 'ner'} or any(r['exit_code'] != 0 for r in runs):
            raise ValueError('CTN finite-validation runs did not complete')
    except (ValueError, KeyError, OSError) as error:
        problems.append('CTN import/finite-validation manifest: ' + str(error))
    # Keep FMP's imported implementation provenance separate from proof status.
    try:
        directory = ROOT / 'notations/FMP'
        manifest = json.loads((directory / 'provenance.json').read_text(encoding='utf-8'))
        if manifest.get('schema_version') != 1 or manifest.get('notation') != 'FMP':
            raise ValueError('Unexpected FMP provenance schema/identity')
        records = manifest['files']
        if len(records) != 3 or {r['file'] for r in records} != {
                'fmp.py', 'fmp_tools.py', 'FMP.ne-rewritten.js'}:
            raise ValueError('FMP provenance must pin exactly its three implementation files')
        for record in records:
            if sha256_lf(directory / record['file']) != record['packaged_sha256']:
                raise ValueError('FMP provenance hash mismatch: ' + record['file'])
            if record['file'].endswith('.py') and record['original_sha256'] != record['packaged_sha256']:
                raise ValueError('FMP Python core is no longer the unchanged imported snapshot')
    except (ValueError, KeyError, OSError) as error:
        problems.append('FMP import manifest: ' + str(error))
    # SRPD is a separate implicit-root presentation, not an eighth Lean proof.
    # Pin its exact implementation/fixture set without waiving other checks.
    try:
        directory = ROOT / 'notations/SRPD'
        manifest = json.loads((directory / 'provenance.json').read_text(encoding='utf-8'))
        if manifest.get('schema_version') != 1 or manifest.get('notation') != 'SRPD':
            raise ValueError('Unexpected SRPD provenance schema/identity')
        expected = {'SRPD.ne-rewritten.js', 'srpd.py',
                    'fixtures/height-naive-counterexample.json',
                    'fixtures/completion-counterexample.json'}
        records = manifest['files']
        if len(records) != len(expected) or {r['file'] for r in records} != expected:
            raise ValueError('SRPD provenance must pin exactly two implementations and two fixtures')
        for record in records:
            if sha256_lf(directory / record['file']) != record['packaged_sha256']:
                raise ValueError('SRPD provenance hash mismatch: ' + record['file'])
            if record['original_sha256'] != record['packaged_sha256']:
                raise ValueError('SRPD is no longer the unchanged imported snapshot')
        receipt = json.loads((ROOT / 'tools/srpd-validation.json').read_text(encoding='utf-8'))
        if receipt.get('schema_version') != 1 or receipt.get('universal_proof') is not False:
            raise ValueError('Unexpected SRPD finite-validation schema/scope')
        expected_checks = {'notations/SRPD/' + name for name in expected} | {
            'tests/srpd.cjs', 'tests/srpd_python.py', 'tests/srpd_tbms_bounds.cjs'}
        checks = receipt['checked_files']
        if len(checks) != len(expected_checks) or {r['file'] for r in checks} != expected_checks:
            raise ValueError('SRPD receipt has an unexpected implementation/test inventory')
        for record in checks:
            if sha256_lf(ROOT / record['file']) != record['sha256_lf']:
                raise ValueError('Stale SRPD finite-validation receipt: ' + record['file'])
        if len(receipt['runs']) != 3 or any(r['exit_code'] != 0 for r in receipt['runs']):
            raise ValueError('SRPD receipt must record all three completed bounded tests')
    except (ValueError, KeyError, OSError) as error:
        problems.append('SRPD import/finite-validation manifest: ' + str(error))
    # Explicit provenance inventory: do not silently treat all files in the
    # comparison directory as untranslated historical manuscripts.
    import_path = ROOT / 'research/order-comparisons/import-manifest.json'
    try:
        imports = json.loads(import_path.read_text(encoding='utf-8'))
        if imports.get('schema_version') != 1:
            raise ValueError('Unsupported import manifest schema')
        imported_paths = set()
        for record in imports['files']:
            relative = record['file']
            destination = (ROOT / relative).resolve()
            if relative in imported_paths or not destination.is_relative_to(ROOT.resolve()):
                raise ValueError(f'Duplicate or escaping import: {relative}')
            imported_paths.add(relative)
            if sha256_lf(destination) != record['packaged_sha256']:
                raise ValueError(f'Imported snapshot changed: {relative}')
            if record['kind'] == 'original-language-manuscript' and relative not in MONOLINGUAL_ARCHIVES:
                raise ValueError(f'Manuscript absent from exact archive inventory: {relative}')
    except (ValueError, KeyError, OSError) as error:
        problems.append('Comparison import manifest: ' + str(error))
    for path in files:
        if path.suffix in ('.olean', '.ilean', '.o', '.exe', '.dll', '.pyc'):
            problems.append(f'Generated binary in release inventory: {path.relative_to(ROOT)}')
        if path.suffix in ('.md','.py','.js','.cjs','.mjs','.json','.lean') and path != Path(__file__).resolve():
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
            if not path.is_file():
                problems.append(f'Missing reported PDF: {record["pdf"]}')
                continue
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
