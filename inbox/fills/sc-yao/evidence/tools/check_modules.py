#!/usr/bin/env python3
"""Run one module per shared-slot invocation, retaining timing and both error forms."""
import argparse
import datetime
import fcntl
import json
import os
from pathlib import Path
import re
import shutil
import hashlib
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--phase', required=True)
parser.add_argument('--order')
parser.add_argument('--continue-on-error', action='store_true')
parser.add_argument('modules', nargs='*')
args = parser.parse_args()
lock_path = Path('.lake/sc-yao-driver.lock')
lock_path.parent.mkdir(parents=True, exist_ok=True)
lock = lock_path.open('a+')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
modules = args.modules
if args.order:
    modules += [m.strip() for m in Path(args.order).read_text().splitlines() if m.strip()]
log_dir = Path('evidence/logs') / args.phase
log_dir.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['LEAN_SLOT_TAG'] = 'sc-yao'
env['TCSLIB_OLEANS'] = str(Path('.lake/sc-yao-oleans').resolve())
failed = False
for module in modules:
    path = log_dir / (module.replace('/', '__') + '.log')
    if path.exists():
        raise RuntimeError(f'Refusing to overwrite raw log {path}; choose a new phase')
    snapshot = path.with_suffix('.source.lean')
    shutil.copyfile(module + '.lean', snapshot)
    source_sha256 = hashlib.sha256(snapshot.read_bytes()).hexdigest()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print('START', start, module, flush=True)
    with path.open('w') as log:
        log.write(f'START {start} {module}\n')
        log.flush()
        result = subprocess.run([
            '/private/tmp/sc-yao-lean-slot.sh', '/usr/bin/time', '-l',
            'bash', 'scripts/lean_check_tree.sh', module,
        ], stdout=log, stderr=subprocess.STDOUT, env=env)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        log.write(f'END {end} EXIT {result.returncode}\n')
    raw = path.read_text()
    errors = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', raw, re.M))
    generic = len(re.findall(r'^error[:(]', raw, re.M))
    fresh = Path(env['TCSLIB_OLEANS'], module + '.olean').is_file()
    record = dict(module=module, phase=args.phase, start=start, end=end,
                  exit=result.returncode, errors=errors, generic_errors=generic,
                  fresh_olean=fresh, source=str(snapshot), source_sha256=source_sha256, sorries=raw.count("declaration uses 'sorry'"), log=str(path))
    with (log_dir / 'results.jsonl').open('a') as out:
        out.write(json.dumps(record) + '\n')
    print('END', module, 'exit', result.returncode, 'errors', errors + generic, flush=True)
    if result.returncode or errors or generic or not fresh:
        failed = True
        print(raw[-8000:], flush=True)
        if not args.continue_on_error:
            break
raise SystemExit(failed)
