"""Run one reviewed archived proposal through the managed plain elaborator."""
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

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
source=OUT/sys.argv[1]
assert source.parent==OUT and source.name.endswith('.lean.txt')
stem=source.name.removesuffix('.lean.txt')
log=OUT/(stem+'.out');receipt=OUT/(stem+'-run.json')
assert not log.exists() and not receipt.exists()
data=source.read_bytes()
temporary=Path(tempfile.mkdtemp(prefix='tcslib-additional-zero-',dir='/private/tmp'))
probe=temporary/(stem.replace('-','_')+'.lean')
probe.write_bytes(data)
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-natbits'
snapshot=Path(os.environ['TCSLIB_SCRATCH'])/'oleans-mac3'
wrapper=ROOT/'devtools/seyoon/leanelab.sh'
command=['bash',str(wrapper),str(wt),str(snapshot),str(probe)]
start=time.time()
(OUT/(stem+'-request.json')).write_text(json.dumps(dict(command=command,
    start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),
    input_sha256=hashlib.sha256(data).hexdigest(),temporary_input=str(probe),
    runner_pid=os.getpid(),unapproved=True),indent=2)+'\n')
completed=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log.write_bytes(completed.stdout)
output=completed.stdout.decode(errors='replace')
row=dict(command=command,start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),
         seconds=time.time()-start,input_sha256=hashlib.sha256(data).hexdigest(),
         output_sha256=hashlib.sha256(completed.stdout).hexdigest(),
         exit=completed.returncode,errors=len(re.findall(r'^.*:\d+:\d+: error:',output,re.M)),
         temporary_input=str(probe),snapshot=str(snapshot),local_slots=os.environ.get('TCSLIB_LEAN_SLOTS'),
         execution='plain managed leanelab, no compiled output; one sequential Lean, no nested lock',
         unapproved=True)
receipt.write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(row,indent=2),flush=True)
print(output,flush=True)
