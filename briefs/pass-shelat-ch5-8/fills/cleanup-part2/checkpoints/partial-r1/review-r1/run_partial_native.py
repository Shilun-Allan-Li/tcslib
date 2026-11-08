"""Own serial checker for a frozen bounded local-repair plan."""
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


def idle():
    for name in ['lean', 'lake']:
        result = subprocess.run(['pgrep', '-x', name], capture_output=True, text=True)
        assert result.returncode == 1, ('Host native process already present', name, result.stdout, result.stderr)


def main():
    config = json.loads((OUT / 'config.json').read_text())
    work = Path(config['worktree'])
    tree = Path(config['tree'])
    def git(*args):
        return subprocess.check_output(['git', '-C', str(work), *args])
    assert git('branch', '--show-current').decode().strip() == config['branch']
    assert git('rev-parse', 'HEAD').decode().strip() == config['head_before_repairs_committed']
    assert not git('diff', '--cached', '--name-only').strip()
    assert hashlib.sha256(git('diff', '--binary')).hexdigest() == config['working_source_diff_sha256']
    assert sha(OUT / 'modules.json') == config['modules_sha256']
    assert sha(OUT / 'order.txt') == config['order_sha256']
    modules = json.loads((OUT / 'modules.json').read_text())
    assert len(modules) == config['module_count']
    assert (OUT / 'order.txt').read_text().splitlines() == [row['module'] for row in modules]
    for row in modules:
        assert sha(work / (row['module'] + '.lean')) == row['source_sha256']
    assert not (work / '.lake/build/lib/lean').exists(), 'No second TCSlib classpath tree'
    checker = work / 'scripts/lean_check_tree.sh'
    assert sha(checker) == config['checker_sha256']
    assert (work / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.25.0'
    idle()
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
    (OUT / 'preflight.json').write_text(json.dumps({
        'utc': now(), 'commands': preflight, 'packages': package_rows,
        'physical_memory_bytes': memory, 'conservative_headroom_bytes': headroom,
        'disk_free_bytes': free, 'logical_cpus': int(cpus),
        'pinned_package_cache': str((work / '.lake/packages').resolve()),
    }, indent=2) + '\n')
    assert headroom >= 4 * 1024**3 and free >= 12 * 1024**3, 'E-RES: resource floor failed'
    assert not tree.exists(), 'Fresh empty TCSlib tree required'
    tree.mkdir(parents=True)
    logs = OUT / 'evidence/logs'
    logs.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env.pop('LEAN_PATH', None)
    env['TCSLIB_OLEANS'] = str(tree)
    runner_sha = sha(Path(__file__))
    records = {}
    attempts = (OUT / 'attempts.jsonl').open('x')

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
    assert not probe.exists()
    roots = (OUT / 'mathlib-roots.txt').read_text().splitlines()
    assert roots and all(name.startswith('Mathlib.') for name in roots)
    probe.write_text(''.join('import ' + name + '\n' for name in roots))
    check(probe_module, sha(probe), [], 0)
    for number, row in enumerate(modules, start=1):
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
        'attempts_sha256': sha(OUT / 'attempts.jsonl'), 'no_TCSlib_object_copy_or_reuse': True,
    }, indent=2) + '\n')
    print(json.dumps({'all_passed': True, 'checked_local_modules': len(modules),
                      'tree': str(tree)}, indent=2), flush=True)


if __name__ == '__main__':
    main()
