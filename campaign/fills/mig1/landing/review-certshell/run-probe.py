"""One sequential plain elaboration through the managed wrapper, raw input and receipts retained."""
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
context=json.loads((OUT/'setup.json').read_text())
name=sys.argv[1]
source=OUT/(name+'.lean.txt');log=OUT/(name+'.out');receipt=OUT/(name+'-run.json')
assert not log.exists() and not receipt.exists()
data=source.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-certshell-probe-',dir='/private/tmp'))
p=tmp/(name.replace('-','_')+'.lean');p.write_bytes(data)
command=['bash',str(ROOT/'devtools/seyoon/leanelab.sh'),context['worktree'],context['complete_private_overlay'],str(p)]
start=time.time();row=dict(command=command,start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),input_sha256=hashlib.sha256(data).hexdigest(),local_slots=os.environ.get('TCSLIB_LEAN_SLOTS'),plain_managed=True,no_outer_lock=True)
(OUT/(name+'-request.json')).write_text(json.dumps(row,indent=2)+'\n')
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log.write_bytes(r.stdout);text=r.stdout.decode(errors='replace')
row.update(exit=r.returncode,seconds=time.time()-start,errors=len(re.findall(r'^.*:\d+:\d+: error:',text,re.M)),output_sha256=hashlib.sha256(r.stdout).hexdigest())
receipt.write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(row,indent=2));print(text)
