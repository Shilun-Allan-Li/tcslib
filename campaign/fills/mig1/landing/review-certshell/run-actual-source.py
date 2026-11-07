"""Elaborate only the applied owned source via the managed plain wrapper."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
c=json.loads((OUT/'setup.json').read_text())
a=json.loads((OUT/'application.json').read_text())
p=Path(c['owned_source'])
assert hashlib.sha256(p.read_bytes()).hexdigest()==a['new_sha256']
assert not (OUT/'Actual-source-run.json').exists()
command=['bash',str(ROOT/'devtools/seyoon/leanelab.sh'),c['worktree'],c['complete_private_overlay'],str(p)]
start=time.time();row=dict(command=command,start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),input_sha256=a['new_sha256'],local_slots=os.environ.get('TCSLIB_LEAN_SLOTS'),plain_managed=True,no_outer_lock=True,actual_owned_source=True)
(OUT/'Actual-source-request.json').write_text(json.dumps(row,indent=2)+'\n')
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(OUT/'Actual-source.out').write_bytes(r.stdout)
row.update(exit=r.returncode,seconds=time.time()-start,errors=len(re.findall(r'^.*:\d+:\d+: error:',r.stdout.decode(errors='replace'),re.M)),output_sha256=hashlib.sha256(r.stdout).hexdigest())
(OUT/'Actual-source-run.json').write_text(json.dumps(row,indent=2)+'\n')
assert hashlib.sha256(p.read_bytes()).hexdigest()==row['input_sha256']
print(json.dumps(row,indent=2));print(r.stdout.decode(errors='replace'))
