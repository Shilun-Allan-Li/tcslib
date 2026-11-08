"""Recheck only the corrected OneWay module; retain failed attempt01 verbatim."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

PREP = Path(__file__).resolve().parent
OUT = PREP / 'partial-r1/native-fixes-r1'
WORK = Path('/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4')
TREE = WORK / '.lake/ps-maintainer/cleanup-partial-fixes-20261108-r1/oleans'
MODULE = 'TCSlib/Cryptography/Asymptotic/OneWayLemmas'
EXPECTED = '9cf33d741e376f1f0beeebfb92d733fa6a08d99126ffbc8c50411328d8ed8636'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    rows = [json.loads(line) for line in (OUT / 'attempts.jsonl').read_text().splitlines()]
    failed = rows[-1]
    assert failed['module'] == MODULE and not failed['passed']
    assert sha(OUT / failed['log']) == failed['log_sha256']
    passed = {row['module']: row for row in rows if row['passed']}
    assert len(passed) == 87
    for module, digest in failed['direct_prerequisites'].items():
        assert module in passed and sha(TREE / (module + '.olean')) == digest
        assert sha(WORK / (module + '.lean')) == passed[module]['source_sha256']
    source = WORK / (MODULE + '.lean')
    assert sha(source) == EXPECTED
    with (OUT / 'oneway-attempt02-runner.pid').open('x') as pid:
        pid.write(str(os.getpid()) + '\n')
    while True:
        busy = {}
        for process in ['lean', 'lake']:
            response = subprocess.run(['pgrep', '-x', process], capture_output=True, text=True)
            assert response.returncode in [0, 1]
            if response.returncode == 0:
                busy[process] = response.stdout.strip().splitlines()
        if not busy:
            break
        print(json.dumps({'waiting_for_host': busy}), flush=True)
        time.sleep(10)
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env.pop('LEAN_PATH', None)
    env['TCSLIB_OLEANS'] = str(TREE)
    log_path = OUT / 'evidence/logs/087-TCSlib_Cryptography_Asymptotic_OneWayLemmas.attempt02.log'
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t0 = time.monotonic()
    command = ['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', MODULE]
    with log_path.open('xb') as log:
        log.write((json.dumps({'event': 'START', 'utc': start, 'module': MODULE,
                              'source_sha256': EXPECTED, 'command': command,
                              'runner_sha256': sha(Path(__file__)),
                              'prerequisites': failed['direct_prerequisites']}) + '\n').encode())
        log.flush()
        process = subprocess.Popen(command, cwd=WORK, env=env, stdin=subprocess.DEVNULL,
                                   stdout=log, stderr=subprocess.STDOUT)
        (OUT / 'oneway-attempt02-active.json').write_text(json.dumps({
            'wrapper_pid': process.pid, 'runner_pid': os.getpid(), 'module': MODULE,
            'start_utc': start}, indent=2) + '\n')
        rc = process.wait()
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        elapsed = time.monotonic() - t0
        log.write((json.dumps({'event': 'END', 'utc': end, 'rc': rc,
                              'elapsed_seconds': elapsed}) + '\n').encode())
    raw = log_path.read_text()
    obj = TREE / (MODULE + '.olean')
    nonempty = obj.is_file() and obj.stat().st_size > 0
    errors = len(re.findall(r'\berror(?:\([^)]*\))?:', raw))
    rss = re.search(r'^\s*(\d+)\s+maximum resident set size\s*$', raw, re.M)
    record = {'module': MODULE, 'attempt_number': 2, 'source_sha256': EXPECTED,
              'start_utc': start, 'end_utc': end, 'rc': rc, 'elapsed_seconds': elapsed,
              'passed': rc == 0 and errors == 0 and nonempty and sha(source) == EXPECTED,
              'error_diagnostics': errors, 'fresh_nonempty_object': nonempty,
              'source_unchanged': sha(source) == EXPECTED,
              'direct_prerequisites': failed['direct_prerequisites'],
              'object_sha256': sha(obj) if nonempty else None,
              'log': str(log_path.relative_to(OUT)), 'log_sha256': sha(log_path),
              'max_rss_bytes': int(rss[1]) if rss else None}
    with (OUT / 'attempts.jsonl').open('a') as stream:
        stream.write(json.dumps(record) + '\n')
    (OUT / 'oneway-attempt02-result.json').write_text(json.dumps(record, indent=2) + '\n')
    (OUT / 'oneway-attempt02-active.json').unlink()
    print(json.dumps(record, indent=2), flush=True)
    assert record['passed'], 'Retain attempt02 and skip dependent checks'


if __name__ == '__main__':
    main()
