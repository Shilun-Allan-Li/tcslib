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
temp_dir = Path(tempfile.mkdtemp(prefix='tcslib-zero-space-', dir='/private/tmp'))
probe = temp_dir / (stem.replace('-', '_') + '.lean')
probe.write_bytes(data)
snapshot = Path(os.environ['TCSLIB_SCRATCH']) / 'oleans-mac2'
wrapper = root / 'devtools/seyoon/leanelab.sh'
command = ['bash', str(wrapper), str(root), str(snapshot), str(probe)]
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
    'expected_snapshot_base': '3555163f40d9c101a2ef4e81407c1bda58fe5ca4',
}
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
print(text)
