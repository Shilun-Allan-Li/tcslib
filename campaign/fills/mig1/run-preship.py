"""Run the reviewed conditional route and its one-definition seal/controls."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

h=Path(__file__).resolve().parent;r=h.parents[2];s=Path(os.environ['TCSLIB_SCRATCH'])
for name,expected,errors in [('RouteProbe',0,0),('RouteProbe-sealed',0,0),
                             ('ControlsUnsealed',0,0),('ControlsSealed',1,2)]:
    source=h/'inputs'/f'{name}.lean.txt'
    target=s/'mig1-probes'/f'{name}.lean'
    target.write_bytes(source.read_bytes())
    cmd=['bash',str(r/'devtools/seyoon/leanelab.sh'),str(s/'wt-camp'),
         str(s/'oleans-mac0'),str(target)]
    start=time.time()
    with (h/'logs'/f'{name}.out').open('w') as out:
        p=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
    output=(h/'logs'/f'{name}.out').read_text()
    diagnostic_errors=output.count('error:')+output.count('error(')
    receipt={'command':cmd,'exit':p.returncode,'expected_exit':expected,
             'errors':diagnostic_errors,'expected_errors':errors,'seconds':time.time()-start,
             'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    (h/'logs'/f'{name}-run.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert p.returncode==expected and diagnostic_errors==errors,(name,output)
    if expected==0:assert 'sorryAx' not in output and 'warning:' not in output,(name,output)
    print(name,'passed expected result',flush=True)
