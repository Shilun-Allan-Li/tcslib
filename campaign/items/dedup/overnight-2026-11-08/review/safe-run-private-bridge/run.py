from pathlib import Path
from datetime import datetime,timezone
import sys,subprocess,os,json,hashlib,re,time
O=Path('/private/tmp/ab34-safe-run-bridge-refinement');P=O/'project';R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S='/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8';name,attempt,expected=sys.argv[1:4];expected=int(expected);key=Path(name).stem+'-'+attempt;log=O/(key+'.log');receipt=O/(key+'.json');assert not log.exists() and not receipt.exists();b=(P/name).read_bytes();cmd=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(P),S,name];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';t=time.monotonic();start=datetime.now(timezone.utc).isoformat()
with log.open('wb') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env)
raw=log.read_bytes();r={'name':name,'attempt':attempt,'command':cmd,'started_utc':start,'seconds_including_slot_wait':time.monotonic()-t,'source_sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':b==(P/name).read_bytes(),'exit':q.returncode,'expected_exit':expected,'errors':len(re.findall(rb'\berror(?:\([^)]*\))?:',raw)),'warnings':raw.count(b'warning:'),'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'raw_sha256':hashlib.sha256(raw).hexdigest(),'local3_machine5_j4_nice10_one_helper':True,'no_source_Git_snapshot_or_olean_output':True};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
for l in raw.decode(errors='replace').splitlines():
 if 'error' in l or l.startswith(('COMPLETE|','GUARDS|','SIMPDEFS|')):print(l)
sys.exit(0 if q.returncode==expected else 1)
