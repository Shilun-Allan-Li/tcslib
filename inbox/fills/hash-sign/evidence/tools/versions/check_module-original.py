import datetime
import pathlib
import subprocess
import sys

module, label = sys.argv[1:]
repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
log = ev / 'logs' / (label + '.log')
with log.open('w') as f:
    print('start:', datetime.datetime.now(datetime.timezone.utc).isoformat(), 'module:', module, file=f, flush=True)
    p = subprocess.run(['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module], cwd=repo, stdout=f, stderr=subprocess.STDOUT)
    print('end:', datetime.datetime.now(datetime.timezone.utc).isoformat(), 'exit:', p.returncode, file=f)
print(log.read_text())
raise SystemExit(p.returncode)
