from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys,time
O=Path('/private/tmp/ab34-overnight-sg1-harvest');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');kind,attempt=sys.argv[1:3]
modules={'EmitIterEmbed':'TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean','SAT':'TCSlib/Complexity/ClassNP/SAT.lean','Hardness':'TCSlib/Complexity/CookLevin/Hardness.lean'};module=modules[kind]
log=O/f'native-{kind}-{attempt}.log';receipt=O/f'native-{kind}-{attempt}.json'
if log.exists() or receipt.exists():raise SystemExit('Refusing to overwrite native attempt')
command=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(O/'native-project'),'/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8',module]
env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:result=subprocess.run(command,env=env,stdout=f,stderr=subprocess.STDOUT)
b=log.read_bytes();r={'owner':kind,'source':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','snapshot':'whole oleans-mac8','command':command,'started_utc':start,'finished_utc':datetime.now(timezone.utc).isoformat(),'seconds_including_slot_wait':time.monotonic()-t,'exit':result.returncode,'errors':b.count(b'error:'),'warnings':b.count(b'warning:'),'sorry_warnings':b.count(b"declaration uses 'sorry'"),'raw_bytes':len(b),'raw_sha256':hashlib.sha256(b).hexdigest(),'probe_sha256':hashlib.sha256((O/'native-project'/module).read_bytes()).hexdigest(),'full_owner_hypothetical_source':True,'new_source_or_snapshot_output':False,'own_job_limit':1,'root_local_slots':3,'machine_cap':5,'j4_nice10':'repository leanelab wrapper'};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
for line in b.decode().splitlines():
 if 'error' in line or 'depends on axioms:' in line:print(line)
sys.exit(result.returncode)
