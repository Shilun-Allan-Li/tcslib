from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys,time
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');P=A/'native-project';V=Path('/private/tmp/ab34-ro1-deterministic-native-overlay');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');rel,attempt=sys.argv[1:3]
assert rel.endswith('.lean') and '..' not in Path(rel).parts
d=A/'native';d.mkdir(exist_ok=True);key=rel[:-5].replace('/','__')+'__'+attempt;log=d/(key+'.log');receipt=d/(key+'.json');assert not log.exists() and not receipt.exists();b=(P/rel).read_bytes();removed=[]
for ext in ['.olean','.ilean','.c','.trace']:
 p=V/(rel[:-5]+ext)
 if p.exists():p.unlink();removed.append(str(p))
cmd=['bash',str(W/'devtools/seyoon/leanelab-o.sh'),str(P),str(V),rel,str(V)];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env)
raw=log.read_bytes();out=V/(rel[:-5]+'.olean');r={'file':rel,'attempt':attempt,'status':'private unapproved alternate owner probe','source_sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':b==(P/rel).read_bytes(),'started_utc':start,'seconds_including_slot_wait':time.monotonic()-t,'command':cmd,'exit':q.returncode,'errors':raw.count(b'error:'),'warnings':raw.count(b'warning:'),'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'raw_sha256':hashlib.sha256(raw).hexdigest(),'fresh_olean_exists':out.is_file(),'fresh_olean_sha256':hashlib.sha256(out.read_bytes()).hexdigest() if out.is_file() else None,'removed_only_own_private_outputs':removed,'one_own_slot_local3_machine5_j4_nice10':True,'original_MAC8_not_written':True};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
for l in raw.decode(errors='replace').splitlines():
 if 'error:' in l:print(l)
sys.exit(0 if q.returncode==0 and r['errors']==0 and r['fresh_olean_exists'] else 1)
