"""Check one module through the shared host slots; retain every raw diagnostic."""
from pathlib import Path
import os,sys,subprocess,json,datetime,re,hashlib
repo=Path.cwd();module,label=sys.argv[1:3];out=Path(sys.argv[3])
out.mkdir(parents=True,exist_ok=True);log=out/(label+'.log');assert not log.exists(),log
env=dict(os.environ,LEAN_SLOT_TAG='seq-zk',TCSLIB_OLEANS=str(repo/'.lake/tcslib-check-oleans'))
env['PATH']='/Users/seyoonr/.elan/bin:'+env['PATH']
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with log.open('w') as f:
 f.write(f'START {start}\nMODULE {module}\n');f.flush()
 p=subprocess.run(['/private/tmp/seq-zk-lean-slot.sh','/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',module],env=env,stdout=f,stderr=subprocess.STDOUT)
 f.write(f'END {datetime.datetime.now(datetime.timezone.utc).isoformat()}\nEXIT {p.returncode}\n')
raw=log.read_text();errs=[]
for m in re.finditer(r'^(\S+\.lean):(\d+):(\d+): error(?:\([^\n)]*\))?:([^\n]*)',raw,re.M):
 errs.append({'path':m[1],'line':int(m[2]),'column':int(m[3]),'message':m[4].strip()})
rec={'module':module,'label':label,'start':start,'end':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':p.returncode,'error_count':len(errs),'errors':errs,'raw_log':str(log),'raw_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
with (out/'results.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(json.dumps(rec));print(raw[-5000:] if errs or p.returncode else raw[-1000:]);sys.exit(p.returncode)
