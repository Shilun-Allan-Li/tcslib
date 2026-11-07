"""Run one already-reviewed probe via the managed elaborator; retain every attempt."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time

root = Path(__file__).resolve().parents[5]
out = Path(__file__).resolve().parent
source = out / sys.argv[1]
if source.parent != out or not source.name.endswith('.lean.txt'):
    raise SystemExit('probe must be a direct .lean.txt child of this output folder')
stem = source.name.removesuffix('.lean.txt')
log_path = out / (stem + '.out')
receipt_path = out / (stem + '-run.json')
if log_path.exists() or receipt_path.exists():
    raise SystemExit('refusing to overwrite an existing attempt')
data = source.read_bytes()
temp_dir = Path(tempfile.mkdtemp(prefix='tcslib-gate117-seals-', dir='/private/tmp'))
probe = temp_dir / (stem.replace('-', '_') + '.lean')
probe.write_bytes(data)
mode = sys.argv[2]
if mode not in ('base', 'head'):
    raise SystemExit('mode must be base or head')
snapshot = Path(os.environ['TCSLIB_SCRATCH']) / ('oleans-mac3' if mode == 'base' else 'oleans-reading-preflight2')
worktree = Path(os.environ['TCSLIB_SCRATCH']) / ('wt-camp' if mode == 'base' else 'wt-natbits')
wrapper = root / 'devtools/seyoon/leanelab.sh'
command = ['bash', str(wrapper), str(worktree), str(snapshot), str(probe)]
start = time.time()
completed = subprocess.run(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log_path.write_bytes(completed.stdout)
text = completed.stdout.decode(errors='replace')
receipt = {
    'command': command,
    'start_utc': datetime.datetime.fromtimestamp(start, datetime.timezone.utc).isoformat(),
    'seconds': time.time() - start,
    'input_sha256': hashlib.sha256(data).hexdigest(),
    'output_sha256': hashlib.sha256(completed.stdout).hexdigest(),
    'exit': completed.returncode,
    'errors': len(re.findall(r'(?m)^.*:\d+:\d+: error:', text)),
    'temporary_input': str(probe),
    'snapshot': str(snapshot),
    'base': 'e3adffac67377a8b6e23bed74bfdbb44a123dd86',
    'head': '1160c18f03fd318f0dec25738790935fa61379d4',
    'mode': mode,
}
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
if len(text) <= 8000:
    print(text)
else:
    print('Raw output retained:', str(log_path), 'bytes=', len(completed.stdout))
