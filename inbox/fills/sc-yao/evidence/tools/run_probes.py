#!/usr/bin/env python3
"""Run one explicit probe at a time through the shared host slot wrapper."""
import argparse
import datetime
import fcntl
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
parser.add_argument('--output-root', help='Independent output-only tree; imports stay in this checkout')
parser.add_argument('--read-only-import-lock', action='store_true',
                    help='Hold a shared lock against root module writers for this entire run')
args = parser.parse_args()
root = Path.cwd()
import_lock = None
if args.read_only_import_lock:
    import_lock = (root / '.lake/sc-yao-driver.lock').open('a+')
    fcntl.flock(import_lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
rows = json.loads(Path(args.manifest).read_text())
outdir = root / 'evidence/probe-runs' / args.run
outdir.mkdir(parents=True, exist_ok=False)
olean = root / '.lake/sc-yao-oleans'
output_root = (root / args.output_root).resolve() if args.output_root else olean
assert output_root.is_relative_to(root / '.lake'), output_root
output_root.mkdir(parents=True, exist_ok=True)
paths = [str(olean)]
if (root / '.lake/build/lib/lean').is_dir():
    paths.append(str(root / '.lake/build/lib/lean'))
paths.extend(str(p) for p in sorted((root / '.lake/packages').glob('*/.lake/build/lib/lean'))
             if p.is_dir())
env = dict(os.environ, LEAN_PATH=':'.join(paths), LEAN_SLOT_TAG='sc-yao',
           TCSLIB_OLEANS=str(output_root))
error_re = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
with (outdir / 'results.jsonl').open('w') as results:
    for row in rows:
        if 'probe' not in row:
            continue
        probe = Path(row['probe'])
        label = hashlib.sha256(str(probe).encode()).hexdigest()[:12] + '__' + probe.stem
        raw = probe.read_bytes()
        (outdir / (label + '.source.lean')).write_bytes(raw)
        output = output_root / probe.with_suffix('.olean')
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
                      generic_errors=len(re.findall(r'^error[:(]', text, re.M)),
                      fresh_olean=output.is_file() and output.stat().st_size > 0,
                      import_tree=str(olean), output_tree=str(output_root),
                      read_only_import_lock=args.read_only_import_lock,
                      source_sha256=hashlib.sha256(raw).hexdigest(), log=str(logpath.relative_to(root)))
        results.write(json.dumps(record) + '\n')
        results.flush()
        print(label, record['exit'], record['errors'], flush=True)
