"""Serial Lean checks through leanelab, retaining exact inputs and raw receipts."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

H=Path(__file__).resolve().parent
R=H.parents[3]
S=Path(os.environ['TCSLIB_SCRATCH'])
P=S/'linear-consumer-validation'
P.mkdir(exist_ok=True)

cases=[('Census-base','ModuleCensus','oleans-mac1',0,0),
       ('Census-head','ModuleCensus','oleans-linear-preflight',0,0),
       ('AllConstants-base','AllConstants','oleans-mac1',0,0),
       ('AllConstants-head','AllConstants','oleans-linear-preflight',0,0),
       ('Inventory','Inventory','oleans-linear-preflight',0,0),
       ('SimpDefs','SimpDefs','oleans-linear-preflight',0,0),
       ('Hierarchy-sealed','Hierarchy-sealed','oleans-linear-preflight',0,0),
       ('Controls-unsealed','Controls-unsealed','oleans-linear-preflight',0,0),
       ('Controls-sealed','Controls-sealed','oleans-linear-preflight',1,8)]
for label,name,olean,expected,errors in cases:
    f=P/(label+'.lean')
    src=H/(name+'.lean.txt')
    f.write_bytes(src.read_bytes())
    cmd=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(S/'wt-epad'),str(S/olean),str(f)]
    start=time.time()
    with (H/(label+'.out')).open('w') as output:
        p=subprocess.run(cmd,stdout=output,stderr=subprocess.STDOUT)
    out=(H/(label+'.out')).read_text()
    errs=out.count('error:')+out.count('error(')
    receipt={'command':cmd,'input_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),
        'source_sha256':hashlib.sha256((S/'wt-epad/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes()).hexdigest(),
        'exit':p.returncode,'expected_exit':expected,'errors':errs,'expected_errors':errors,
        'seconds':time.time()-start,'olean_tree':olean}
    (H/(label+'-run.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(label,'exit',p.returncode,'errors',errs,flush=True)
    assert p.returncode==expected and errs==errors,(label,out[-1400:])
