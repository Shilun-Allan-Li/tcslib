"""Run every prepared seal serially, recording even expected baseline failures."""
import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

phase = sys.argv[1]
root = Path.cwd()
folder = root / 'evidence/seals' / phase
manifest = json.loads((folder / 'manifest.json').read_text())
results = folder / 'results.jsonl'
env = dict(os.environ, LEAN_SLOT_TAG='derand')
for item in manifest:
    path = Path(item['probe'])
    log = path.with_suffix('.log')
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    clock = time.monotonic()
    command = ['/private/tmp/derand-worker/lean-slot.sh', '/usr/bin/time', '-l',
               'bash', 'scripts/lean_check_tree.sh', str(path.with_suffix(''))]
    with log.open('w') as dest:
        print(f'START {start}\nCOMMAND {command}', file=dest, flush=True)
        proc = subprocess.run(command, stdout=dest, stderr=subprocess.STDOUT, env=env)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print(f'END {end}\nEXIT {proc.returncode}', file=dest)
    raw = log.read_text()
    mapping = json.loads(path.with_suffix('.linemap.json').read_text())
    errors = []
    for match in re.finditer(r'^\S+\.lean:(\d+):(\d+): error[:(].*$', raw, re.M):
        line = int(match[1])
        original = mapping[line - 1] if line <= len(mapping) else None
        errors.append(dict(probe_line=line, source_line=original, diagnostic=match[0]))
    install = re.findall(r'DERAND-INSTALL ' + re.escape(item['label']) + r' requested=(\d+)', raw)
    eof = raw.count('DERAND-EOF ' + item['label'])
    harness = len(install) == 1 and eof == 1 and all(e['source_line'] for e in errors)
    rss = re.search(r'(\d+)\s+maximum resident set size', raw)
    row = dict(item, start=start, end=end, exit=proc.returncode, errors=errors,
               seconds=time.monotonic() - clock, install=len(install), eof=eof,
               requests=int(install[0]) if len(install) == 1 else None,
               harness_valid=harness, max_rss_bytes=int(rss[1]) if rss else None)
    with results.open('a') as dest:
        print(json.dumps(row), file=dest)
    print(f'{path}: exit={proc.returncode} errors={len(errors)} '
          f'harness={harness} requests={row["requests"]}', flush=True)
    if not harness:
        print(raw[-14000:], flush=True)
        sys.exit(2)
print(f'Seals {phase}: completed {len(manifest)} valid probes; failures retained', flush=True)
