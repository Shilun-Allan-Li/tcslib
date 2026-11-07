"""One serialized base screen for the MIG-1 dispatch, with a source receipt."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

here=Path(__file__).resolve().parent
root=here.parents[2]
scratch=Path(os.environ['TCSLIB_SCRATCH'])
pins=json.loads((here/'inputs/pins.json').read_text())
pop=(here/'inputs/screen-population.txt').read_text().splitlines()
lock=scratch/'locks/screen'
while True:
    try:
        lock.mkdir()
        break
    except FileExistsError:
        time.sleep(5)
(lock/'pid').write_text(str(os.getpid())+'\n')
logs=here/'logs'
logs.mkdir(exist_ok=True)
cmd=['nice','-n','10','python3','-I',str(root/'scripts/copy-text-screen-v3.py'),pins['export'],*pop]
t=time.time()
try:
    with (logs/'screen-base.txt').open('w') as out:
        result=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
    receipt={'command':cmd,'base':pins['base'],'files':pop,'exit':result.returncode,
             'seconds':time.time()-t,
             'output_sha256':hashlib.sha256((logs/'screen-base.txt').read_bytes()).hexdigest()}
    (logs/'screen-base-run.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert result.returncode==0
    print((logs/'screen-base.txt').read_text().splitlines()[0],flush=True)
finally:
    assert (lock/'pid').read_text().strip()==str(os.getpid())
    (lock/'pid').unlink()
    lock.rmdir()
