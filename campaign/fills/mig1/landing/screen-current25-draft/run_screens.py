"""Run the unmodified v3 screen serially on captured sources, under the shared lock."""
from pathlib import Path
import datetime, hashlib, json, os, signal, subprocess, sys, tempfile, time

out = Path(__file__).resolve().parent
root = out.parents[4]
scratch = Path(os.environ['TCSLIB_SCRATCH'])
capture = json.loads((out / 'capture.json').read_text())
paths = [row['path'] for row in capture['files']]
assert len(paths) == len(set(paths)) == 25
screen = root / 'scripts/copy-text-screen-v3.py'
pairdiff = root / 'devtools/seyoon/pairdiff.py'
sha = lambda data: hashlib.sha256(data).hexdigest()
screen_data, pairdiff_data = screen.read_bytes(), pairdiff.read_bytes()
(out / 'copy-text-screen-v3.py.txt').write_bytes(screen_data)
(out / 'pairdiff.py.txt').write_bytes(pairdiff_data)
temp = Path(tempfile.mkdtemp(prefix='tcslib-mig-current25-screen-', dir='/private/tmp'))
for label in ['base', 'head']:
    for row in capture['files']:
        data = (out / 'inputs' / label / (row['path'] + '.txt')).read_bytes()
        assert sha(data) == row[label + '_sha256']
        target = temp / label / row['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
(out / 'trees.json').write_text(json.dumps({'temporary_root': str(temp), 'count_per_tree': 25}, indent=2)+'\n')
lock = scratch / 'locks/screen'
events = out / 'lock-events.jsonl'
def event(action, **details):
    with events.open('a') as f:
        f.write(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            'action': action, 'pid': os.getpid(), **details}) + '\n')
def acquire(label):
    waiting = False
    while True:
        try:
            lock.mkdir()
            (lock / 'pid').write_text(str(os.getpid()) + '\n')
            event('acquired', label=label)
            return
        except FileExistsError:
            if not waiting:
                event('waiting', label=label)
                waiting = True
            try:
                inode = lock.stat().st_ino
                text = (lock / 'pid').read_text().strip() if (lock / 'pid').exists() else ''
                alive = False
                if text:
                    pid = int(text)
                    try:
                        os.kill(pid, 0)
                        alive = True
                    except PermissionError:
                        alive = True
                    except ProcessLookupError:
                        pass
                if alive or (not text and time.time() - lock.stat().st_mtime <= 60):
                    time.sleep(2)
                    continue
                if lock.stat().st_ino != inode:
                    continue
                if (lock / 'pid').exists() and (lock / 'pid').read_text().strip() != text:
                    continue
                if (lock / 'pid').exists():
                    (lock / 'pid').unlink()
                lock.rmdir()
                event('reclaimed-stale-lock', label=label, old_pid=text)
            except (FileNotFoundError, FileExistsError):
                continue
def release(label):
    if (lock / 'pid').read_text().strip() != str(os.getpid()):
        raise RuntimeError('shared screen lock ownership changed')
    (lock / 'pid').unlink()
    lock.rmdir()
    event('released', label=label)

child = None
def stop(signum, frame):
    if child is not None and child.poll() is None:
        child.terminate()
        child.wait()
    raise SystemExit(128 + signum)
signal.signal(signal.SIGTERM, stop)
signal.signal(signal.SIGINT, stop)

for label in ['base', 'head']:
    assert not (out / (label + '.out')).exists()
    command = ['nice', '-n', '10', sys.executable, '-I', str(screen), str(temp / label), *paths]
    acquire(label)
    started = time.time()
    try:
        with (out / (label + '.out')).open('wb') as f:
            child = subprocess.Popen(command, cwd=root, stdout=f, stderr=subprocess.STDOUT)
            code = child.wait()
        assert screen.read_bytes() == screen_data, 'screen source changed during execution'
        receipt = {'label': label, 'command': command, 'exit': code,
                   'elapsed_seconds': time.time()-started,
                   'screen_sha256': sha(screen_data), 'output_sha256': sha((out/(label+'.out')).read_bytes()),
                   'source_count': len(paths), 'shared_lock': str(lock), 'lock_owner_pid': os.getpid(),
                   'input_hashes_verified': True, 'draft_pre_comment_capture': True}
        (out / (label + '.json')).write_text(json.dumps(receipt, indent=2)+'\n')
        print(json.dumps(receipt), flush=True)
        assert code == 0, f'{label} screen failed'
    finally:
        if child is not None and child.poll() is None:
            child.terminate()
            child.wait()
        child = None
        release(label)

assert pairdiff.read_bytes() == pairdiff_data
command = [sys.executable, '-I', str(pairdiff), str(out/'head.out'), str(out/'base.out')]
p = subprocess.run(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out/'pairdiff.out').write_bytes(p.stdout)
(out/'pairdiff.json').write_text(json.dumps({'command': command, 'exit': p.returncode,
    'pairdiff_sha256': sha(pairdiff_data), 'output_sha256': sha(p.stdout)}, indent=2)+'\n')
assert p.returncode == 0
print(p.stdout.decode().splitlines()[0], flush=True)
