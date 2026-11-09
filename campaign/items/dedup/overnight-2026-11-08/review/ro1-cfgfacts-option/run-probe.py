from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys,time
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');P=O/'native-project'
name,tree,attempt,expected=sys.argv[1:5];expected=int(expected)
assert name.endswith('.lean') and '/' not in name
d=O/'probes';d.mkdir(exist_ok=True);key=Path(name).stem+'__'+attempt;log=d/(key+'.log');receipt=d/(key+'.json');assert not log.exists() and not receipt.exists()
b=(P/name).read_bytes();cmd=['bash',str(W/'devtools/seyoon/leanelab.sh'),str(P),tree,name];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';t=time.monotonic();start=datetime.now(timezone.utc).isoformat()
with log.open('wb') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env)
raw=log.read_bytes();r={'probe':name,'attempt':attempt,'source_sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':b==(P/name).read_bytes(),'started_utc':start,'seconds_including_slot_wait':time.monotonic()-t,'command':cmd,'exit':q.returncode,'expected_exit':expected,'errors':raw.count(b'error:'),'warnings':raw.count(b'warning:'),'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'raw_sha256':hashlib.sha256(raw).hexdigest(),'raw_bytes':len(raw),'one_own_slot_local3_machine5_j4_nice10':True,'no_native_object_written':True};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
for line in raw.decode(errors='replace').splitlines():
 if 'error:' in line or 'COMPLETE|' in line:print(line)
sys.exit(0 if q.returncode==expected else 1)
