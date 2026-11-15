import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

phase, order = sys.argv[1:3]
root = Path.cwd()
out = root / 'evidence/logs' / phase
out.mkdir(parents=True, exist_ok=True)
modules = [m.strip() for m in Path(order).read_text().splitlines() if m.strip()]
env = dict(os.environ, LEAN_SLOT_TAG='derand')
for index, module in enumerate(modules, 1):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    clock = time.monotonic()
    path = out / (module.replace('/', '_') + '.log')
    source = (root / (module + '.lean')).read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    archive = root / 'evidence/sources' / (digest + '.lean')
    archive.parent.mkdir(parents=True, exist_ok=True)
    if not archive.exists():
        archive.write_bytes(source)
    command = ['/private/tmp/derand-worker/lean-slot.sh', '/usr/bin/time', '-l',
               'bash', 'scripts/lean_check_tree.sh', module]
    with path.open('w') as log:
        print(f'START {start}\nCOMMAND {command}', file=log, flush=True)
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, env=env)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print(f'END {end}\nEXIT {result.returncode}', file=log)
    content = path.read_text()
    errors = re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', content, re.M)
    rss = re.search(r'(\d+)\s+maximum resident set size', content)
    row = dict(module=module, index=index, start=start, end=end, exit=result.returncode,
               errors=len(errors), seconds=time.monotonic() - clock, source_sha256=digest,
               max_rss_bytes=int(rss[1]) if rss else None,
               log=str(path.relative_to(root)))
    with (out / 'results.jsonl').open('a') as dest:
        print(json.dumps(row), file=dest)
    print(f'{phase} {index}/{len(modules)} {module} '
          f'exit={result.returncode} errors={len(errors)} '
          f'seconds={row["seconds"]:.1f} rss={row["max_rss_bytes"]}', flush=True)
    if result.returncode or errors:
        print(content[-16000:], flush=True)
        sys.exit(1)
print(f'{phase}: PASS {len(modules)} modules', flush=True)
