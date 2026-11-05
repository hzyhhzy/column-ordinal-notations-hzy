"""Check the published Lean receipt against this package without recompiling.

Receipt integrity is separate from Lean kernel compilation; build.py performs
the latter. This script does not evaluate any hierarchy or table.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def verify():
    spec = importlib.util.spec_from_file_location('laver_lower_bound_builder', ROOT / 'build.py')
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    expected = builder.closure()
    receipt = json.loads((ROOT / 'verification/VERIFICATION.json').read_text(encoding='utf-8'))
    if (receipt.get('schema_version') != 1 or receipt.get('status') != 'PASS'
            or receipt.get('lean') != '4.33.1'
            or receipt.get('full_import_closure_rebuilt') is not True
            or receipt.get('I3_assumed') is not False
            or receipt.get('object_language_ZFC_derivation') is not False):
        raise ValueError('Unexpected verification identity or scope')
    modules = receipt['modules']
    if (receipt['compiled_modules'] != len(expected)
            or [r['path'] for r in modules] != [n + '.lean' for n in expected]):
        raise ValueError('Receipt does not cover the exact current import closure')
    for item in modules:
        path = (ROOT / item['path']).resolve()
        if (not path.is_relative_to(ROOT) or item['module'] != item['path'][:-5].replace('/', '.')
                or digest(path) != item['sha256_lf']):
            raise ValueError('Changed or invalid compiled module: ' + item['path'])
    axioms = receipt['final_theorem_axioms']
    if set(axioms) != set(builder.FINAL) or any(set(v) != builder.ALLOWED for v in axioms.values()):
        raise ValueError('Final theorem axiom audit changed')
    log = (ROOT / 'verification/build.txt').read_text(encoding='utf-8')
    if re.findall(r'^PASS (\S+)\s*$', log, re.M) != expected:
        raise ValueError('Build log does not match the exact import closure')
    if re.search(r'\berror:|sorryAx|declaration uses .sorry.', log):
        raise ValueError('Build log contains an error or placeholder')
    for name, values in axioms.items():
        report = re.search(re.escape("'" + name + "'") + r' depends on axioms:\s*\[([^\]]*)\]', log)
        if not report or set(v.strip() for v in report[1].split(',')) != set(values):
            raise ValueError('Missing final axiom log: ' + name)
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text(encoding='utf-8'))
    for item in provenance['files']:
        path = (ROOT / item['path']).resolve()
        if not path.is_relative_to(ROOT) or digest(path) != item['package_sha256_lf']:
            raise ValueError('Changed imported source/configuration: ' + item['path'])
    return {'status': 'PASS', 'compiled_modules': len(expected),
            'pinned_import_files': len(provenance['files']),
            'scope': 'published Lean source/log/axiom receipt integrity; no recompilation'}


if __name__ == '__main__':
    print(json.dumps(verify(), ensure_ascii=False, indent=2))
