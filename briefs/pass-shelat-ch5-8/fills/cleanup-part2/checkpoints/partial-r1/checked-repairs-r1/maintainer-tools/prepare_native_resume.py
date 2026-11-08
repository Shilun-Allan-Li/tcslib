"""Derive a same-phase resumable runner from the own preserved serial runner."""
from pathlib import Path
import ast
import hashlib

PREP = Path(__file__).resolve().parent
source = (PREP / 'run_partial_native.py').read_text()
recorded = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/fills/cleanup-part2/checkpoints/partial-r1/review-r1/run_partial_native.py')
assert recorded.read_text() == source


def replace(old, new):
    global source
    assert source.count(old) == 1, old
    source = source.replace(old, new, 1)


start = source.index('def idle():')
end = source.index('\n\ndef main():', start)
source = source[:start] + '''def idle(require_stable=False):
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
                with (OUT / 'host-waits-resume-01.jsonl').open('a') as log:
                    log.write(json.dumps(row) + '\\n')
                print(json.dumps(row), flush=True)
                previous = busy
        elif not require_stable:
            return
        elif stable_since is None:
            stable_since = time.monotonic()
        elif time.monotonic() - stable_since >= 20:
            return
        time.sleep(10)
''' + source[end:]
replace('    idle()\n    preflight = []', '    idle(require_stable=True)\n    preflight = []')
replace("def main():\n    config = json.loads((OUT / 'config.json').read_text())", '''def main():
    with (OUT / 'resume-01-runner.pid').open('x') as pid_file:
        pid_file.write(str(os.getpid()) + '\\n')
    assert not (OUT / 'preflight-resume-01.json').exists()
    config = json.loads((OUT / 'config.json').read_text())''')
replace("(OUT / 'preflight.json').write_text", "(OUT / 'preflight-resume-01.json').write_text")
replace("    assert not tree.exists(), 'Fresh empty TCSlib tree required'\n    tree.mkdir(parents=True)",
        "    assert tree.is_dir(), 'Resume only the same phase tree, never copy/reuse another tree'")
replace("    logs.mkdir(parents=True, exist_ok=False)", "    assert logs.is_dir()")
replace("    records = {}\n    attempts = (OUT / 'attempts.jsonl').open('x')", '''    previous_rows = [json.loads(line) for line in (OUT / 'attempts.jsonl').read_text().splitlines()]
    expected_prefix = ['.lake/ps-maintainer/cleanup-partial-fixes-20261108-r1/CacheProbe'] + [row['module'] for row in modules]
    assert [row['module'] for row in previous_rows] == expected_prefix[:len(previous_rows)]
    assert len(previous_rows) == 4 and not (OUT / 'STOP.json').exists()
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
    (OUT / 'resume-01-prefix-reconciliation.json').write_text(json.dumps({
        'utc': now(), 'verified_prefix_records': len(records),
        'prefix_modules': list(records), 'same_phase_same_sources_objects_logs': True,
        'source_diff_sha256': config['working_source_diff_sha256'],
        'new_runner_sha256': runner_sha,
    }, indent=2) + '\\n')
    attempts = (OUT / 'attempts.jsonl').open('a')''')
replace('    assert not probe.exists()', '    assert probe.exists()')
replace("    probe.write_text(''.join('import ' + name + '\\n' for name in roots))",
        "    assert probe.read_text() == ''.join('import ' + name + '\\n' for name in roots)")
replace('    check(probe_module, sha(probe), [], 0)',
        "    assert probe_module in records and sha(probe) == records[probe_module]['source_sha256']")
replace("        check(row['module'], row['source_sha256'], row['local_imports'], number)",
        "        if row['module'] not in records:\n            check(row['module'], row['source_sha256'], row['local_imports'], number)")
replace("'no_TCSlib_object_copy_or_reuse': True,", "'no_TCSlib_object_copy_or_reuse': True, 'resumed_after_host_defer': True,")
source = source.replace('Own serial checker for a frozen bounded local-repair plan.',
                        'Own same-phase resumption; preserve and verify four successful prefix checks.')
ast.parse(source)
target = PREP / 'run_partial_native_resume.py'
assert not target.exists()
target.write_text(source)
print({'runner': str(target), 'sha256': hashlib.sha256(target.read_bytes()).hexdigest(), 'AST_valid': True})
