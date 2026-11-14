import datetime
import fcntl
import hashlib
import pathlib
import subprocess
import sys
import time

module, label = sys.argv[1:]
repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
log = ev / 'logs' / (label + '.log')
log.parent.mkdir(parents=True, exist_ok=True)
# A single worker slot accounts conservatively for two active jobs in other
# projects. Before launching, observe the shared three-process host cap.
slots = pathlib.Path('/private/tmp/hash-sign-fill/check-slots')
slots.mkdir(exist_ok=True)
lock = None
while lock is None:
    for index in range(1):
        candidate = (slots / str(index)).open('w')
        try:
            fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
            lock = candidate
            break
        except BlockingIOError:
            candidate.close()
    if lock is None:
        time.sleep(0.25)
while True:
    commands = subprocess.check_output(['ps', '-axo', 'comm'], text=True).splitlines()
    active = [p for p in commands if pathlib.Path(p.strip()).name == 'lean']
    if len(active) < 3:
        break
    time.sleep(0.25)
with log.open('w') as f:
    print('start:', datetime.datetime.now(datetime.timezone.utc).isoformat(), 'module:', module, file=f, flush=True)
    print('source_sha256:', hashlib.sha256((repo / (module + '.lean')).read_bytes()).hexdigest(), file=f, flush=True)
    p = subprocess.run(['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module], cwd=repo, stdout=f, stderr=subprocess.STDOUT)
    print('end:', datetime.datetime.now(datetime.timezone.utc).isoformat(), 'exit:', p.returncode, file=f)
print(log.read_text())
raise SystemExit(p.returncode)
