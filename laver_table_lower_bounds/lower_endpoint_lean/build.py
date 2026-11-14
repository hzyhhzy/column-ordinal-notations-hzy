"""Rebuild the lower-endpoint extension and all shared source dependencies.

This verifies the K11 BMS+1 bound and eta's finite-table geometry.
It does NOT verify the paper's six-type BMS lower bound for eta.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from time import monotonic

ROOT = Path(__file__).resolve().parent
SHARED = ROOT.parent / 'lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FINAL = (
    'LaverLowerBounds.FiniteTable.k11_undefined_or_large',
    'LaverLowerBounds.FiniteTable.k11_nonzero_bms_successor_bound',
    'LaverLowerBounds.FiniteTable.LowerEndpoint.Word.index_stable',
    'LaverLowerBounds.FiniteTable.LowerEndpoint.q5_critical_index_chain',
)


def sha256_lf(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def find_source(module):
    for root in [ROOT, SHARED]:
        path = root / (module.replace('.', '/') + '.lean')
        if path.is_file():
            return root, path
    return None


def closure():
    seen, active, ordered = set(), set(), []

    def visit(module):
        if module in seen:
            return
        if module in active:
            raise RuntimeError('Import cycle: ' + module)
        found = find_source(module)
        if found is None:
            if module in ('Init', 'Std', 'Lean') or module.startswith(('Init.', 'Std.', 'Lean.')):
                return
            raise RuntimeError('Missing source: ' + module)
        active.add(module)
        root, source = found
        for dep in re.findall(r'^import\s+([\w.]+)', source.read_text(encoding='utf-8'), re.M):
            visit(dep)
        active.remove(module)
        seen.add(module)
        ordered.append((module, root, source))

    visit('LowerEndpoints')
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--record', action='store_true')
    args = parser.parse_args()
    exe = 'lean.exe' if os.name == 'nt' else 'lean'
    lean = str((args.lean_bin / exe).resolve()) if args.lean_bin else shutil.which(exe)
    if not lean or not Path(lean).is_file():
        parser.error('Lean 4.33.1 is required; pass --lean-bin or put it on PATH')
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    version = subprocess.run([lean, '--version'], check=True, capture_output=True,
                             text=True, timeout=15).stdout.strip()
    expected = (ROOT / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[1]
    if not re.search(r'\bversion ' + re.escape(expected) + r'(?:,|\s)', version):
        raise RuntimeError('Wrong Lean version: ' + version)
    out = ROOT / '.build' / 'lean'
    logs = ROOT / '.build' / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    out.mkdir(parents=True, exist_ok=True)
    env['LEAN_PATH'] = str(out)
    records, audits, transcript = [], {}, [version]
    modules = closure()
    start = monotonic()
    for index, (module, root, source) in enumerate(modules, 1):
        digest = sha256_lf(source)
        target = out / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, '-M', '2048', '-j', '1', '-R', str(root),
                   '-o', str(target), str(source)]
        options = {'creationflags': subprocess.CREATE_NO_WINDOW} if os.name == 'nt' else {}
        # subprocess.run kills and waits for this compiler on timeout.
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                text=True, encoding='utf-8', errors='replace',
                                timeout=60, **options)
        text = result.stdout + result.stderr
        portable = text.replace(str(ROOT), '.').replace(str(SHARED), '../lean')
        (logs / (module.replace('.', '_') + '.txt')).write_text(portable, encoding='utf-8')
        if result.returncode or 'sorryAx' in text or re.search(r'declaration uses .sorry.', text):
            raise RuntimeError('Compilation failed: ' + module + '\n' + portable)
        if sha256_lf(source) != digest:
            raise RuntimeError('Source changed during build: ' + module)
        for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
            axioms = sorted(v.strip() for v in values.split(',') if v.strip())
            if set(axioms) - ALLOWED:
                raise RuntimeError('Unexpected axiom: ' + name + ': ' + repr(axioms))
            audits[name] = axioms
        records.append({'module': module, 'path': os.path.relpath(source, ROOT).replace('\\', '/'),
                        'sha256_lf': digest})
        transcript.append(portable + '\nPASS ' + module)
        print(f'PASS {index}/{len(modules)} {module}', flush=True)
    if any(name not in audits for name in FINAL):
        raise RuntimeError('Missing final theorem audit')
    receipt = {
        'schema_version': 1, 'status': 'PASS', 'lean': expected,
        'full_import_closure_rebuilt': True, 'compiled_modules': len(modules),
        'verified': ['K11 index absent or greater than F_(Lambda+1)(120)',
                     'Exact eta application word, projection, index stability and uniqueness',
                     'q5 exists implies eta index exists and eta < k11 < k10 < k9 < kappa4'],
        'not_verified': ['BMS lower bound at eta', 'Six-type BMS tower bound',
                         'eta < J13(gamma16)', 'Object-language ZFC or I3 interpretation'],
        'final_theorem_axioms': {name: audits[name] for name in FINAL},
        'limits': {'compiler_threads': 1, 'compiler_memory_mb': 2048, 'seconds_per_module': 60},
        'seconds': round(monotonic() - start, 3), 'modules': records,
    }
    if args.record:
        destination = ROOT / 'verification'
        destination.mkdir(exist_ok=True)
        (destination / 'build.txt').write_text('\n'.join(transcript) + '\n', encoding='utf-8')
        (destination / 'VERIFICATION.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(f'PASS complete: {len(modules)} modules. Eta BMS bound remains open.', flush=True)


if __name__ == '__main__':
    main()
