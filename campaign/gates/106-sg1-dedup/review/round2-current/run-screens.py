"""Fresh complete nine-file screens, serial under the shared screen lock."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import tempfile
import time
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
context=json.loads((OUT/'context.json').read_text())
files=(OUT/'population.txt').read_text().splitlines()
screen=ROOT/'scripts/copy-text-screen-v3.py'
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen'
wait_start=time.time()
print('Waiting for shared screen lock',flush=True)
while True:
    try:
        lock.mkdir()
        (lock/'pid').write_text(str(os.getpid())+'\n')
        break
    except FileExistsError:
        time.sleep(2)
try:
    print('Acquired shared screen lock',flush=True)
    for label in ['base','head']:
        target=OUT/'screen'/(label+'.txt')
        assert not target.exists()
        target.parent.mkdir(exist_ok=True)
        temp=Path(tempfile.mkdtemp(prefix='tcslib-106r2-screen-'+label+'-',dir='/private/tmp'))
        for f in files:
            data=(OUT/(label+'-source')/(f+'.txt')).read_bytes()
            assert hashlib.sha256(data).hexdigest()==context['source_pins'][f][label+'_sha256']
            q=temp/f;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
        command=['nice','-n','10','python3','-I',str(screen),str(temp)]+files
        start=time.time()
        request=dict(command=command,start_utc=datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),population=files,screen_script_sha256=hashlib.sha256(screen.read_bytes()).hexdigest(),shared_screen_lock=str(lock),wait_seconds=start-wait_start)
        (target.parent/(label+'-request.json')).write_text(json.dumps(request,indent=2)+'\n')
        print('Running '+label+' complete nine-file screen',flush=True)
        r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        target.write_bytes(r.stdout);(target.parent/(label+'.stderr.txt')).write_bytes(r.stderr)
        request.update(exit=r.returncode,seconds=time.time()-start,output_sha256=hashlib.sha256(r.stdout).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr).hexdigest())
        (target.parent/(label+'-run.json')).write_text(json.dumps(request,indent=2)+'\n')
        assert r.returncode==0,(label,r.stderr.decode(errors='replace'))
        print(label+': '+r.stdout.decode().splitlines()[0],flush=True)
finally:
    (lock/'pid').unlink()
    lock.rmdir()
print('Released shared screen lock',flush=True)
r=subprocess.run(['python3','-I',str(ROOT/'devtools/seyoon/pairdiff.py'),str(OUT/'screen/head.txt'),str(OUT/'screen/base.txt')],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(OUT/'screen/pairdiff.txt').write_bytes(r.stdout)
(OUT/'screen/pairdiff.stderr.txt').write_bytes(r.stderr)
assert r.returncode==0
print(r.stdout.decode(),flush=True)
