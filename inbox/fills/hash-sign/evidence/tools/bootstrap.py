import datetime
import json
import os
import pathlib
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
order = (ev / 'logs/extended-order.txt').read_text().splitlines()
logs = ev / 'logs/bootstrap'
logs.mkdir(exist_ok=True)
with (ev / 'logs/bootstrap-results.jsonl').open('a') as results:
    for i, module in enumerate(order):
        if module.endswith('/HashAndSign'):
            break
        dest = logs / (module.replace('/', '_') + '.log')
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        with dest.open('w') as f:
            print('start:', start, 'module:', module, file=f, flush=True)
            proc = subprocess.run(['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module], cwd=repo, stdout=f, stderr=subprocess.STDOUT)
            end = datetime.datetime.now(datetime.timezone.utc).isoformat()
            print('end:', end, 'exit:', proc.returncode, file=f, flush=True)
        record = dict(index=i, module=module, start=start, end=end, exit=proc.returncode, log=str(dest.relative_to(ev)))
        print(json.dumps(record), file=results, flush=True)
        print(module, proc.returncode, flush=True)
        if proc.returncode:
            raise SystemExit(proc.returncode)
