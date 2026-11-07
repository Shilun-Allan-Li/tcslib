"""Elaborate one reviewed landing source/probe into this agent's private full overlay."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time

out = Path(__file__).resolve().parent
root = out.parents[4]
scratch = Path(os.environ['TCSLIB_SCRATCH'])
wt = scratch / 'wt-epad'
overlay = scratch / 'oleans-mig1-comp-loop-20261107'
label, mode, argument = sys.argv[1:4]
if not re.fullmatch(r'[A-Za-z0-9_-]+', label):
    raise SystemExit('invalid output label')
receipt_path = out / (label + '.json')
log_path = out / (label + '.out')
if receipt_path.exists() or log_path.exists():
    raise SystemExit('refusing to overwrite a prior attempt')
if mode == 'module':
    source = wt / argument
    if not argument.startswith('TCSlib/') or not argument.endswith('.lean') or '..' in Path(argument).parts:
        raise SystemExit('invalid module path')
    data = source.read_bytes()
    archive = out / (label + '.lean.txt')
    archive.write_bytes(data)
    command = ['bash', str(root / 'devtools/seyoon/leanelab-o.sh'), str(wt),
               str(overlay), argument, str(overlay)]
elif mode == 'probe':
    source = out / argument
    if source.parent != out or not source.name.endswith('.lean.txt'):
        raise SystemExit('invalid probe path')
    data = source.read_bytes()
    directory = Path(tempfile.mkdtemp(prefix='tcslib-mig1-comp-loop-', dir='/private/tmp'))
    probe = directory / (label + '.lean')
    probe.write_bytes(data)
    command = ['bash', str(root / 'devtools/seyoon/leanelab.sh'), str(wt), str(overlay), str(probe)]
else:
    raise SystemExit('mode must be module or probe')
start = time.time()
completed = subprocess.run(command, cwd=wt, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log_path.write_bytes(completed.stdout)
receipt = dict(label=label, mode=mode, source=str(source), command=command,
    overlay=str(overlay), seconds=time.time()-start, exit=completed.returncode,
    errors=len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:', completed.stdout)),
    input_sha256=hashlib.sha256(data).hexdigest(),
    output_sha256=hashlib.sha256(completed.stdout).hexdigest(),
    source_still_matches=source.read_bytes()==data)
receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
text=completed.stdout.decode(errors='replace')
print(text if len(text)<8000 else 'Full raw output retained in '+str(log_path))
