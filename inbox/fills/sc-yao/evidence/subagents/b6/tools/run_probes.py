#!/usr/bin/env python3
"""Run one explicit probe at a time through the shared host slot wrapper."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument('manifest')
parser.add_argument('run')
args = parser.parse_args()
root = Path.cwd()
print("DRIVER_PID", os.getpid(), flush=True)
rows = json.loads(Path(args.manifest).read_text())
outdir = root / 'evidence/subagents/b6/probe-runs' / args.run
outdir.mkdir(parents=True, exist_ok=False)
olean = root / '.lake/sc-yao-oleans'
paths = [str(olean)]
if (root / '.lake/build/lib/lean').is_dir():
    paths.append(str(root / '.lake/build/lib/lean'))
paths.extend(str(p) for p in sorted((root / '.lake/packages').glob('*/.lake/build/lib/lean'))
             if p.is_dir())
env = dict(os.environ, LEAN_PATH=':'.join(paths), LEAN_SLOT_TAG='sc-yao-b',
           TCSLIB_OLEANS=str(olean))
error_re = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
with (outdir / 'results.jsonl').open('w') as results:
    for row in rows:
        if 'probe' not in row:
            continue
        probe = Path(row['probe'])
        label = probe.stem
        raw = probe.read_bytes()
        (outdir / (label + '.source.lean')).write_bytes(raw)
        output = olean / probe.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        output.unlink(missing_ok=True)
        cmd = ['/private/tmp/sc-yao-lean-slot.sh', '/usr/bin/time', '-l', 'lean',
               '-DmaxErrors=0', str(probe), '-o', str(output)]
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        stamp = time.monotonic()
        logpath = outdir / (label + '.log')
        with logpath.open('w') as log:
            log.write('START ' + start + '\n')
            log.flush()
            done = subprocess.run(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
            end = datetime.datetime.now(datetime.timezone.utc).isoformat()
            log.write('END ' + end + '\n')
        text = logpath.read_text()
        record = dict(row, start=start, end=end, seconds=time.monotonic()-stamp,
                      exit=done.returncode, errors=len(error_re.findall(text)),
                      fresh_olean=output.is_file() and output.stat().st_size > 0,
                      source_sha256=hashlib.sha256(raw).hexdigest(), log=str(logpath.relative_to(root)))
        results.write(json.dumps(record) + '\n')
        results.flush()
        print(label, record['exit'], record['errors'], flush=True)
