"""The two specifically authorized small, plain managed metadata probes only."""
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

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
stage = sys.argv[1]
assert stage in ['Base', 'Head']
name = 'Equation' + stage
source = OUT / (name + '.lean.txt')
log = OUT / (name + '.out')
receipt = OUT / (name + '-run.json')
assert not log.exists() and not receipt.exists()
scratch = Path(os.environ['TCSLIB_SCRATCH'])
worktree = scratch / ('wt-natbits' if stage == 'Base' else 'wt-epad')
snapshot = scratch / ('oleans-mra2' if stage == 'Base' else 'oleans-mig1-preflight-current4')
tmp = Path(tempfile.mkdtemp(prefix='tcslib-split-equation-', dir='/private/tmp'))
target = tmp / (name + '.lean')
data = source.read_bytes()
target.write_bytes(data)
command = ['bash', str(ROOT / 'devtools/seyoon/leanelab.sh'), str(worktree), str(snapshot), str(target)]
start = time.time()
row = dict(stage=stage, command=command, input_sha256=hashlib.sha256(data).hexdigest(),
           started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
           local_slots=os.environ.get('TCSLIB_LEAN_SLOTS'), plain_managed=True,
           authority='Parent authorized exactly two small actual function/equation metadata probes; no full census/controls/source mutation.')
(OUT / (name + '-request.json')).write_text(json.dumps(row, indent=2) + '\n')
result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log.write_bytes(result.stdout)
row.update(exit=result.returncode, seconds=time.time() - start,
           errors=len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:', result.stdout)),
           warnings=len(re.findall(rb'(?m)^.*:\d+:\d+: warning:', result.stdout)),
           output_sha256=hashlib.sha256(result.stdout).hexdigest())
receipt.write_text(json.dumps(row, indent=2) + '\n')
print(json.dumps(row, indent=2))
if result.returncode:
    print(result.stdout.decode(errors='replace'))
