from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,os,sys,time,re
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');P=A/'native-project';W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');name,tree,expected=sys.argv[1:4];expected=int(expected);d=A/'probes';d.mkdir(exist_ok=True);key=Path(name).stem+'__attempt1';log=d/(key+'.log');receipt=d/(key+'.json');assert not log.exists() and not receipt.exists();b=(P/name).read_bytes();cmd=['bash',str(W/'devtools/seyoon/leanelab.sh'),str(P),tree,name];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env)
raw=log.read_bytes();r={'probe':name,'command':cmd,'source_sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':b==(P/name).read_bytes(),'started_utc':start,'seconds_including_slot_wait':time.monotonic()-t,'exit':q.returncode,'expected_exit':expected,'errors':len(re.findall(rb'\berror(?:\([^)]*\))?:',raw)),'warnings':raw.count(b'warning:'),'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'raw_sha256':hashlib.sha256(raw).hexdigest(),'one_own_slot_local3_machine5_j4_nice10':True,'no_native_object_written':True};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
for l in raw.decode(errors='replace').splitlines():
 if 'error:' in l or l.startswith('COMPLETE|'):print(l)
sys.exit(0 if q.returncode==expected else 1)
