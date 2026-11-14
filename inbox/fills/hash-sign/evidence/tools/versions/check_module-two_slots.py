import datetime
import fcntl
import pathlib
import subprocess
import sys
import time

module, label = sys.argv[1:]
repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
log = ev / 'logs' / (label + '.log')
# Two checker slots conservatively leave room for a previously launched baseline
# evidence process. Every participating worker uses this same launcher.
slots = pathlib.Path('/private/tmp/hash-sign-fill/check-slots')
slots.mkdir(exist_ok=True)
lock = None
while lock is None:
    for index in range(2):
        candidate = (slots / str(index)).open('w')
        try:
            fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
            lock = candidate
            break
        except BlockingIOError:
            candidate.close()
    if lock is None:
        time.sleep(0.25)
with log.open('w') as f:
    print('start:', datetime.datetime.now(datetime.timezone.utc).isoformat(), 'module:', module, file=f, flush=True)
    p = subprocess.run(['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module], cwd=repo, stdout=f, stderr=subprocess.STDOUT)
    print('end:', datetime.datetime.now(datetime.timezone.utc).isoformat(), 'exit:', p.returncode, file=f)
print(log.read_text())
raise SystemExit(p.returncode)
