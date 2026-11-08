from pathlib import Path
import datetime, hashlib, json, os, resource, subprocess, sys, time

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
capture = json.loads((OUT / 'capture.json').read_text())
tool = ROOT / 'scripts/copy-text-screen-v3.py'
assert hashlib.sha256(tool.read_bytes()).hexdigest() == capture['tools']['scripts/copy-text-screen-v3.py']
lock = Path(os.environ['TCSLIB_SCRATCH']) / 'locks/screen'
held = False
owner_pid = None

def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()

def event(kind, **fields):
    with (OUT / 'lock-events.jsonl').open('a') as f:
        f.write(json.dumps(dict(utc=now(), event=kind, **fields)) + '\n')

def active_screens():
    rows = subprocess.run(['ps', '-Ao', 'pid=,command='], stdout=subprocess.PIPE,
                          check=True).stdout.decode().splitlines()
    return [r for r in rows if 'copy-text-screen-v3.py' in r and 'ps -Ao' not in r]

try:
    event('waiting', lock=str(lock))
    while not held:
        try:
            lock.mkdir(); held = True; owner_pid = os.getpid()
            (lock / 'pid').write_text(str(owner_pid) + '\n')
        except FileExistsError:
            pf = lock / 'pid'; value = pf.read_text().strip() if pf.exists() else ''
            alive = False
            if value.isdigit():
                try: os.kill(int(value), 0); alive = True
                except ProcessLookupError: pass
            old = time.time() - lock.stat().st_mtime > 60
            if not alive and (value or old) and not active_screens():
                assert set(p.name for p in lock.iterdir()) <= {'pid'}
                pf.unlink(missing_ok=True); lock.rmdir(); event('reclaimed_stale', old_pid=value)
            else:
                time.sleep(2)
    event('acquired', pid=owner_pid)
    print('Shared screen lock acquired; one fresh full25 HEAD starts; BASE is adopted.', flush=True)
    for side in ['head']:
        output = OUT / (side + '.out'); receipt = OUT / (side + '-run.json')
        assert not output.exists() and not receipt.exists()
        tree = Path(capture['temporary_trees'][side])
        for row in capture['sides'][side]['files']:
            assert hashlib.sha256((tree / row['path']).read_bytes()).hexdigest() == row['sha256']
        command = ['nice', '-n', '10', 'python3', '-I', str(tool), str(tree), *capture['population']]
        row = dict(side=side, command=command, start_utc=now(), orchestrator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), python_version=sys.version, script_sha256=hashlib.sha256(tool.read_bytes()).hexdigest(),
                   full_population=len(capture['population']), lock=str(lock))
        (OUT / (side + '-request.json')).write_text(json.dumps(row, indent=2) + '\n')
        start = time.time(); before = resource.getrusage(resource.RUSAGE_CHILDREN)
        print('Starting ' + side + ' at ' + row['start_utc'], flush=True)
        with output.open('wb') as f:
            process = subprocess.Popen(command, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
            owner_pid = process.pid; (lock / 'pid').write_text(str(owner_pid) + '\n')
            code = process.wait()
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        data = output.read_bytes()
        row.update(pid=owner_pid, end_utc=now(), seconds=time.time()-start, exit=code,
                   output_sha256=hashlib.sha256(data).hexdigest(), bytes=len(data),
                   user_cpu_seconds=after.ru_utime-before.ru_utime, system_cpu_seconds=after.ru_stime-before.ru_stime,
                   child_maxrss=after.ru_maxrss, first_line=data.decode(errors='replace').splitlines()[0] if data else '')
        receipt.write_text(json.dumps(row, indent=2) + '\n')
        owner_pid = os.getpid(); (lock / 'pid').write_text(str(owner_pid) + '\n')
        print(json.dumps(row), flush=True)
        if code: raise RuntimeError('screen failed: ' + side)
finally:
    if held:
        pf = lock / 'pid'
        assert pf.read_text().strip() == str(owner_pid)
        pf.unlink(); lock.rmdir(); event('released', pid=owner_pid)
        print('Shared screen lock released.', flush=True)
