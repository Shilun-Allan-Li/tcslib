"""Own same-phase resumption; preserve and verify four successful prefix checks."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

PREP = Path(__file__).resolve().parent
OUT = PREP / 'partial-r1/native-fixes-r1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def idle(require_stable=False):
    stable_since = None
    previous = None
    while True:
        busy = {}
        for name in ['lean', 'lake']:
            result = subprocess.run(['pgrep', '-x', name], capture_output=True, text=True)
            assert result.returncode in [0, 1], result.stderr
            if result.returncode == 0:
                busy[name] = result.stdout.strip().splitlines()
        if busy:
            require_stable = True
            stable_since = None
            if busy != previous:
                row = {'utc': now(), 'event': 'WAIT_SHARED_HOST', 'pids': busy}
                with (OUT / 'host-waits-resume-02.jsonl').open('a') as log:
                    log.write(json.dumps(row) + '\n')
                print(json.dumps(row), flush=True)
                previous = busy
        elif not require_stable:
            return
        elif stable_since is None:
            stable_since = time.monotonic()
        elif time.monotonic() - stable_since >= 20:
            return
        time.sleep(10)


def main():
    with (OUT / 'resume-02-runner.pid').open('x') as pid_file:
        pid_file.write(str(os.getpid()) + '\n')
    assert not (OUT / 'preflight-resume-02.json').exists()
    config = json.loads((OUT / 'config-revision02.json').read_text())
    work = Path(config['worktree'])
    tree = Path(config['tree'])
    def git(*args):
        return subprocess.check_output(['git', '-C', str(work), *args])
    assert git('branch', '--show-current').decode().strip() == config['branch']
    assert git('rev-parse', 'HEAD').decode().strip() == config['head_before_repairs_committed']
    assert not git('diff', '--cached', '--name-only').strip()
    assert hashlib.sha256(git('diff', '--binary')).hexdigest() == config['working_source_diff_sha256']
    assert sha(OUT / 'modules-revision02.json') == config['modules_sha256']
    assert sha(OUT / 'order.txt') == config['order_sha256']
    modules = json.loads((OUT / 'modules-revision02.json').read_text())
    assert len(modules) == config['module_count']
    assert (OUT / 'order.txt').read_text().splitlines() == [row['module'] for row in modules]
    for row in modules:
        assert sha(work / (row['module'] + '.lean')) == row['source_sha256']
    assert not (work / '.lake/build/lib/lean').exists(), 'No second TCSlib classpath tree'
    checker = work / 'scripts/lean_check_tree.sh'
    assert sha(checker) == config['checker_sha256']
    assert (work / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.25.0'
    idle(require_stable=True)
    preflight = []
    def record_command(args):
        result = subprocess.run(args, capture_output=True, text=True)
        preflight.append({'command': args, 'rc': result.returncode,
                          'stdout': result.stdout, 'stderr': result.stderr})
        assert result.returncode == 0, args
        return result.stdout
    cpus = record_command(['sysctl', '-n', 'hw.logicalcpu'])
    memory = int(record_command(['sysctl', '-n', 'hw.memsize']).strip())
    record_command(['vm_stat'])
    pressure = record_command(['memory_pressure', '-Q'])
    percent = int(re.search(r'memory free percentage:\s*(\d+)%', pressure)[1])
    # Conservative one-percentage-point margin for the rounded macOS reading.
    headroom = memory * max(percent - 1, 0) // 100
    free = shutil.disk_usage(work).free
    record_command(['df', '-k', str(work), str(OUT), '/private/tmp'])
    package_rows = []
    for pkg in json.loads((work / 'lake-manifest.json').read_text())['packages']:
        path = work / '.lake/packages' / pkg['name']
        row = {'name': pkg['name'], 'present': path.exists()}
        if path.exists():
            url = subprocess.check_output(['git', '-C', str(path), 'remote', 'get-url', 'origin'], text=True).strip()
            rev = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain'], text=True)
            row.update({'url': url, 'revision': rev, 'matches': url == pkg['url'] and rev == pkg['rev'],
                        'dirty': bool(dirty)})
            assert row['matches'] and not dirty, row
        package_rows.append(row)
    (OUT / 'preflight-resume-02.json').write_text(json.dumps({
        'utc': now(), 'commands': preflight, 'packages': package_rows,
        'physical_memory_bytes': memory, 'conservative_headroom_bytes': headroom,
        'disk_free_bytes': free, 'logical_cpus': int(cpus),
        'pinned_package_cache': str((work / '.lake/packages').resolve()),
    }, indent=2) + '\n')
    assert headroom >= 4 * 1024**3 and free >= 12 * 1024**3, 'E-RES: resource floor failed'
    assert tree.is_dir(), 'Resume only the same phase tree, never copy/reuse another tree'
    logs = OUT / 'evidence/logs'
    assert logs.is_dir()
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env.pop('LEAN_PATH', None)
    env['TCSLIB_OLEANS'] = str(tree)
    runner_sha = sha(Path(__file__))
    all_prior_rows = [json.loads(line) for line in (OUT / 'attempts.jsonl').read_text().splitlines()]
    latest = {row['module']: row for row in all_prior_rows}
    previous_rows = [row for row in latest.values() if row['passed']]
    failed_rows = [row for row in all_prior_rows if not row['passed']]
    assert len(failed_rows) == 1 and failed_rows[0]['module'] == 'TCSlib/Cryptography/Asymptotic/OneWayLemmas'
    for row in failed_rows:
        assert sha(OUT / row['log']) == row['log_sha256']
    expected_prefix = ['.lake/ps-maintainer/cleanup-partial-fixes-20261108-r1/CacheProbe'] + [row['module'] for row in modules]
    assert [row['module'] for row in previous_rows] == expected_prefix[:len(previous_rows)]
    assert len(previous_rows) == 88 and (OUT / 'STOP.json').exists()
    records = {}
    for row in previous_rows:
        assert row['passed'] and row['rc'] == 0 and row['error_diagnostics'] == 0
        assert sha(work / (row['module'] + '.lean')) == row['source_sha256']
        assert sha(tree / (row['module'] + '.olean')) == row['object_sha256']
        assert sha(OUT / row['log']) == row['log_sha256']
        for dep, digest in row['direct_prerequisites'].items():
            assert dep in records and records[dep]['object_sha256'] == digest
        records[row['module']] = row
    assert {str(path.relative_to(tree))[:-6] for path in tree.rglob('*.olean')} == set(records)
    (OUT / 'resume-02-prefix-reconciliation.json').write_text(json.dumps({
        'utc': now(), 'verified_prefix_records': len(records),
        'prefix_modules': list(records), 'same_phase_same_sources_objects_logs': True,
        'source_diff_sha256': config['working_source_diff_sha256'],
        'new_runner_sha256': runner_sha,
    }, indent=2) + '\n')
    attempts = (OUT / 'attempts.jsonl').open('a')

    def check(module, source_sha, deps, number):
        for dep in deps:
            assert dep in records, ('Missing checked prerequisite', module, dep)
            assert sha(tree / (dep + '.olean')) == records[dep]['object_sha256']
            assert sha(work / (dep + '.lean')) == records[dep]['source_sha256']
        source = work / (module + '.lean')
        assert sha(source) == source_sha and sha(checker) == config['checker_sha256']
        idle()
        start = now()
        t0 = time.monotonic()
        command = ['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module]
        path = logs / f'{number:03d}-{module.replace("/", "_")}.attempt01.log'
        header = {'event': 'START', 'utc': start, 'module': module,
                  'source_sha256': source_sha, 'command': command,
                  'runner_sha256': runner_sha, 'checker_sha256': config['checker_sha256'],
                  'prerequisites': {dep: records[dep]['object_sha256'] for dep in deps}}
        with path.open('xb') as log:
            log.write((json.dumps(header) + '\n').encode())
            log.flush()
            process = subprocess.Popen(command, cwd=work, env=env, stdin=subprocess.DEVNULL,
                                       stdout=log, stderr=subprocess.STDOUT)
            (OUT / 'active-native.json').write_text(json.dumps({
                'module': module, 'wrapper_pid': process.pid, 'start_utc': start,
                'runner_pid': os.getpid(), 'log': str(path)}, indent=2) + '\n')
            rc = process.wait()
            elapsed = time.monotonic() - t0
            end = now()
            log.write((json.dumps({'event': 'END', 'utc': end, 'rc': rc,
                                   'elapsed_seconds': elapsed}) + '\n').encode())
        raw = path.read_text()
        obj = tree / (module + '.olean')
        nonempty = obj.is_file() and obj.stat().st_size > 0
        errors = len(re.findall(r'\berror(?:\([^)]*\))?:', raw))
        unchanged = sha(source) == source_sha
        rss = re.search(r'^\s*(\d+)\s+maximum resident set size\s*$', raw, re.M)
        passed = rc == 0 and errors == 0 and nonempty and unchanged
        row = {'module': module, 'source_sha256': source_sha,
               'start_utc': start, 'end_utc': end, 'rc': rc, 'elapsed_seconds': elapsed,
               'passed': passed, 'error_diagnostics': errors, 'fresh_nonempty_object': nonempty,
               'source_unchanged': unchanged, 'direct_prerequisites': header['prerequisites'],
               'object_sha256': sha(obj) if nonempty else None,
               'log': str(path.relative_to(OUT)), 'log_sha256': sha(path),
               'max_rss_bytes': int(rss[1]) if rss else None}
        attempts.write(json.dumps(row) + '\n')
        attempts.flush()
        (OUT / 'active-native.json').unlink()
        print(json.dumps({'checked': number, 'module': module, 'passed': passed,
                          'elapsed_seconds': round(elapsed, 2), 'rc': rc}), flush=True)
        if not passed:
            (OUT / 'STOP.json').write_text(json.dumps(row, indent=2) + '\n')
            raise RuntimeError('Preserve failed attempt; skip every dependent')
        records[module] = row

    probe_module = '.lake/ps-maintainer/cleanup-partial-fixes-20261108-r1/CacheProbe'
    probe = work / (probe_module + '.lean')
    assert probe.exists()
    roots = (OUT / 'mathlib-roots.txt').read_text().splitlines()
    assert roots and all(name.startswith('Mathlib.') for name in roots)
    assert probe.read_text() == ''.join('import ' + name + '\n' for name in roots)
    assert probe_module in records and sha(probe) == records[probe_module]['source_sha256']
    for number, row in enumerate(modules, start=1):
        if row['module'] not in records:
            check(row['module'], row['source_sha256'], row['local_imports'], number)
    for row in modules:
        module = row['module']
        assert sha(work / (module + '.lean')) == row['source_sha256']
        assert sha(tree / (module + '.olean')) == records[module]['object_sha256']
    assert hashlib.sha256(git('diff', '--binary')).hexdigest() == config['working_source_diff_sha256']
    attempts.close()
    (OUT / 'RESULT.json').write_text(json.dumps({
        **config, 'all_passed': True, 'finished_utc': now(),
        'checked_local_modules': len(modules), 'cache_probe_passed': True,
        'all_sources_objects_reconciled': True, 'runner_sha256': runner_sha,
        'attempts_sha256': sha(OUT / 'attempts.jsonl'), 'no_TCSlib_object_copy_or_reuse': True, 'resumed_after_host_defer': True, 'historical_failed_attempts': 1, 'source_revision': 2,
    }, indent=2) + '\n')
    print(json.dumps({'all_passed': True, 'checked_local_modules': len(modules),
                      'tree': str(tree)}, indent=2), flush=True)


if __name__ == '__main__':
    main()
