"""Bounded IPD mathematical checks and optional Python/NER correspondence.

No dependency on the research workspace or a NER checkout. Every child process
has a wall timeout; Node's old-generation heap is limited to 512 MiB. The
reference's local count loops are capped, not unbounded whole-diagram descents.
"""
from pathlib import Path
import json
import os
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'notations' / 'IPD'))
from ipd import IPD, TOP


def bounded(command, seconds, input_text=None):
    options = ({'creationflags': subprocess.CREATE_NO_WINDOW} if os.name == 'nt'
               else {'start_new_session': True})
    process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, encoding='utf-8', **options)
    try:
        output, error = process.communicate(input_text, timeout=seconds)
        if process.returncode:
            raise RuntimeError(error + output)
        return output
    finally:
        if process.poll() is None:
            if os.name == 'nt':
                subprocess.run(['taskkill', '/PID', str(process.pid), '/T', '/F'],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                               creationflags=subprocess.CREATE_NO_WINDOW, timeout=15)
            else:
                os.killpg(process.pid, signal.SIGKILL)
            process.wait(timeout=15)


def main():
    started = time.monotonic()
    for n in range(16):
        seed = IPD.seed(n)
        assert TOP.fs(n) == seed
        assert IPD.seed(n + 1).fs(1) == seed
        assert seed.fs(0) == IPD(((),))
        assert seed.fs(1) < seed
    for bad in (-1, 1.5, True):
        try:
            IPD.seed(bad)
        except ValueError:
            pass
        else:
            raise AssertionError('Invalid seed index accepted')
    assert str(IPD.seed(2).fs(3)) == '[][0:1/.][1:1/^][2:1/^(.)]'
    data_text = bounded([sys.executable, '-B', str(ROOT/'tests/ipd_vectors.py')], 30)
    data = json.loads(data_text)
    assert len(data['records']) >= 100, 'Insufficient bounded reference sample'
    assert len(data['comparisons']) == 500
    assert len(data['countRecords']) >= 30
    node = os.environ.get('NOTATION_NODE') or shutil.which('node')
    if not node:
        print('SKIP: Node unavailable; Python reference vectors and seed checks passed.')
        return
    result = json.loads(bounded(
        [node, '--max-old-space-size=512', str(ROOT/'tests/ipd_ner.cjs')], 55, data_text))
    assert result['ok'] and result['expansions'] == 4 * len(data['records'])
    assert result['comparisons'] == 500
    result['python_seed_checks'] = 16
    result['total_seconds'] = round(time.monotonic() - started, 3)
    print(json.dumps(result, ensure_ascii=False))


if __name__ == '__main__':
    main()
