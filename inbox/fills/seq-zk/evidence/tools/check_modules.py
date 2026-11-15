"""Serial, slot-controlled one-module checks with raw evidence and timestamps."""
from pathlib import Path
import os,sys,subprocess,json,datetime,re,time,fcntl
repo=Path.cwd(); stage=sys.argv[1]; mods=Path(sys.argv[2]).read_text().splitlines()
out=repo/'evidence/logs'/stage;out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_SLOT_TAG='seq-zk',TCSLIB_OLEANS=os.environ.get('TCSLIB_OLEANS',str(repo/'.lake/tcslib-check-oleans')))
env['PATH']='/Users/seyoonr/.elan/bin:'+env['PATH']
for i,m in enumerate(mods,1):
 if not m.strip():continue
 log=out/(f'{i:03d}-'+m.replace('/','__')+'.log')
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();print(f'{stage} {i}/{len(mods)} START {m}',flush=True)
 with log.open('w') as f:
  f.write(f'START {start}\nMODULE {m}\n');f.flush()
  tree=Path(env['TCSLIB_OLEANS']);tree.mkdir(parents=True,exist_ok=True)
  with (tree/'.seq-zk-writer.lock').open('a') as lock:
   fcntl.flock(lock,fcntl.LOCK_EX)
   p=subprocess.run(['/private/tmp/seq-zk-lean-slot.sh','/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',m],env=env,stdout=f,stderr=subprocess.STDOUT)
  f.write(f'END {datetime.datetime.now(datetime.timezone.utc).isoformat()}\nEXIT {p.returncode}\n')
 raw=log.read_text();errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]',raw,re.M))
 rec={'module':m,'start':start,'end':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':p.returncode,'errors':errors,'raw_log':str(log.relative_to(repo))}
 with (out/'results.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(f'{stage} {i}/{len(mods)} END exit={p.returncode} errors={errors}',flush=True)
 if p.returncode or errors:
  print(raw[-6000:],flush=True);sys.exit(1)
 time.sleep(float(os.environ.get('SEQ_ZK_FAIR_GAP', '6')))
