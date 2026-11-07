"""Run one archived probe sequentially via the repository-managed plain elaborator."""
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
name,context=sys.argv[1:]
assert context in ['base','head']
source=OUT/'probes'/(name+'.lean.txt')
data=source.read_bytes()
label=name+'-'+context
log=OUT/'logs'/(label+'.out');receipt=OUT/'runs'/(label+'.json')
assert not log.exists() and not receipt.exists()
log.parent.mkdir(exist_ok=True);receipt.parent.mkdir(exist_ok=True)
tmp=Path(tempfile.mkdtemp(prefix='tcslib-106r2-',dir='/private/tmp'))
probe=tmp/(name.replace('-','_')+'.lean');probe.write_bytes(data)
pins=json.loads((OUT/'context.json').read_text())
wt=Path(pins[context+'_source']);snap=Path(pins[context+'_snapshot'])
command=['bash',str(ROOT/'devtools/seyoon/leanelab.sh'),str(wt),str(snap),str(probe)]
start=time.time()
row=dict(command=command,start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),input_sha256=hashlib.sha256(data).hexdigest(),local_slots=os.environ.get('TCSLIB_LEAN_SLOTS'),one_sequential_Lean=True,no_outer_lock=True)
(receipt.parent/(label+'-request.json')).write_text(json.dumps(row,indent=2)+'\n')
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log.write_bytes(r.stdout)
text=r.stdout.decode(errors='replace')
row.update(seconds=time.time()-start,exit=r.returncode,errors=len(re.findall(r'^.*:\d+:\d+: error:',text,re.M)),output_sha256=hashlib.sha256(r.stdout).hexdigest())
receipt.write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(dict(label=label,exit=row['exit'],errors=row['errors'],seconds=row['seconds']),indent=2))
print(text[-1800:])
