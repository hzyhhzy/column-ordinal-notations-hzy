"""Sequential, resource-bounded Lean build and axiom audit (Python stdlib only).

This rebuilds the complete local import closure; it does not trust cached
project oleans. --record publishes a portable log and source-hash receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
from time import monotonic

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FINAL = (
    'LaverLowerBounds.FiniteTable.threshold_original_bms_bound',
    'LaverLowerBounds.FiniteTable.q5_original_bms_bound',
    'LaverLowerBounds.FiniteTable.q5_above_original_bms_value',
)


def sha256_lf(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def closure():
    ordered, seen, active = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in active:
            raise RuntimeError('Import cycle: ' + name)
        active.add(name)
        path = ROOT / (name + '.lean')
        source = path.read_text(encoding='utf-8-sig')
        for dep in re.findall(r'^import\s+([A-Za-z0-9_.]+)', source, re.M):
            local = dep.replace('.', '/')
            if (ROOT / (local + '.lean')).is_file():
                visit(local)
            elif not (dep == 'Std' or dep.startswith(('Std.', 'Lean.', 'Init.'))):
                raise RuntimeError('Unbundled import: ' + dep)
        active.remove(name)
        seen.add(name)
        ordered.append(name)

    visit('LaverLowerBounds')
    return ordered


def stop_tree(process):
    if process.poll() is not None:
        return
    if os.name == 'nt':
        subprocess.run(['taskkill', '/PID', str(process.pid), '/T', '/F'],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=10, creationflags=subprocess.CREATE_NO_WINDOW)
    else:
        os.killpg(process.pid, signal.SIGKILL)
    if process.poll() is None:
        process.kill()
    process.wait(timeout=10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path, help='Lean 4.33.1 bin directory; otherwise use PATH')
    parser.add_argument('--timeout', type=int, default=60, help='Seconds per module (10..600)')
    parser.add_argument('--record', action='store_true', help='Write verification/build.txt and VERIFICATION.json')
    args = parser.parse_args()
    if not 10 <= args.timeout <= 600:
        parser.error('--timeout must be between 10 and 600')
    executable = 'lean.exe' if os.name == 'nt' else 'lean'
    lean = str((args.lean_bin / executable).resolve()) if args.lean_bin else shutil.which('lean')
    if not lean or not Path(lean).is_file():
        parser.error('Lean is unavailable; install the pinned toolchain or pass --lean-bin')
    env = os.environ.copy()
    env['PATH'] = str(Path(lean).parent) + os.pathsep + env.get('PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    version = subprocess.run([lean, '--version'], cwd=ROOT, env=env, check=True,
                             capture_output=True, text=True, timeout=15).stdout.strip()
    expected = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip().rsplit(':v', 1)[1]
    if not re.search(r'\bversion ' + re.escape(expected) + r'(?:,|\s)', version):
        raise RuntimeError(f'Expected Lean {expected}; got {version}')
    output = ROOT / '.build' / 'lean'
    logs = ROOT / '.build' / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    env['LEAN_PATH'] = str(output)
    modules = closure()
    records, axiom_records, transcript = [], {}, [version + '\n']
    start = monotonic()
    for index, module in enumerate(modules, 1):
        source = ROOT / (module + '.lean')
        before = sha256_lf(source)
        target = output / (module + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        key = module.replace('/', '_')
        stdout, stderr = logs / (key + '.stdout.txt'), logs / (key + '.stderr.txt')
        command = [lean, '-M', '2048', '-j', '1', '-R', str(ROOT),
                   '-o', str(target), str(source)]
        options = ({'creationflags': subprocess.CREATE_NO_WINDOW | subprocess.CREATE_NEW_PROCESS_GROUP}
                   if os.name == 'nt' else {'start_new_session': True})
        with stdout.open('wb') as out, stderr.open('wb') as err:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=out, stderr=err, **options)
            try:
                code = process.wait(timeout=args.timeout)
            finally:
                stop_tree(process)
        text = stdout.read_text(encoding='utf-8') + stderr.read_text(encoding='utf-8')
        portable = text.replace(str(ROOT), '.').replace(ROOT.as_posix(), '.')
        if code or 'sorryAx' in text or re.search(r'declaration uses .sorry.', text):
            raise RuntimeError(f'Compile or placeholder audit failed: {module}\n{portable}')
        if sha256_lf(source) != before:
            raise RuntimeError('Source changed during compilation: ' + module)
        for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
            axioms = sorted(v.strip() for v in values.split(',') if v.strip())
            if set(axioms) - ALLOWED:
                raise RuntimeError('Unexpected axioms: ' + name + ': ' + ', '.join(axioms))
            axiom_records[name] = axioms
        transcript.append(portable + f'\nPASS {module}\n')
        records.append({'module': module.replace('/', '.'), 'path': module + '.lean',
                        'sha256_lf': before})
        print(f'PASS {index}/{len(modules)} {module}', flush=True)
    if not all(name in axiom_records for name in FINAL):
        raise RuntimeError('Final-theorem axiom output is missing')
    receipt = {
        'schema_version': 1, 'status': 'PASS', 'lean': expected,
        'full_import_closure_rebuilt': True, 'compiled_modules': len(modules),
        'target': 'q(5) exists implies q(5) > F_(lim(BMS)+omega+1)(3)',
        'numeric_BM4_fidelity': 'Every ValidArray, every expansion index; finite FGH evaluation equivalence',
        'final_theorem_axioms': {name: axiom_records[name] for name in FINAL},
        'I3_assumed': False, 'object_language_ZFC_derivation': False,
        'scope': 'Direct Lean theorem for every BinaryFamily satisfying the finite-table defining equations',
        'limits': {'compiler_threads': 1, 'compiler_memory_mb': 2048,
                   'seconds_per_module': args.timeout},
        'seconds': round(monotonic() - start, 3), 'modules': records,
    }
    full_text = '\n'.join(transcript)
    (ROOT / '.build' / 'full-build.txt').write_text(full_text, encoding='utf-8', newline='\n')
    if args.record:
        published = ROOT / 'verification'
        published.mkdir(exist_ok=True)
        (published / 'build.txt').write_text(full_text, encoding='utf-8', newline='\n')
        (published / 'VERIFICATION.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2)
                                                   + '\n', encoding='utf-8', newline='\n')
    print(f'PASS complete: {len(modules)} modules; final theorem axioms audited', flush=True)


if __name__ == '__main__':
    main()
