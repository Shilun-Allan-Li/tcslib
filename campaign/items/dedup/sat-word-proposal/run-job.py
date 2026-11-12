from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys,time
O=Path('/private/tmp/ab34-overnight-sat-import-proposal');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');name,file=sys.argv[1:3];log=O/(name+'.log');receipt=O/(name+'.json')
if log.exists() or receipt.exists():raise SystemExit('Refusing to overwrite attempt')
command=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(O/'native-project'),'/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8',file];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:p=subprocess.run(command,env=env,stdout=f,stderr=subprocess.STDOUT)
b=log.read_bytes();r={'name':name,'source':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','snapshot':'whole MAC8','command':command,'start_utc':start,'end_utc':datetime.now(timezone.utc).isoformat(),'seconds_with_slot_wait':time.monotonic()-t,'exit':p.returncode,'errors':b.count(b'error:'),'warnings':b.count(b'warning:'),'sorry_warnings':b.count(b"declaration uses 'sorry'"),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'probe_sha256':hashlib.sha256((O/'native-project'/file).read_bytes()).hexdigest(),'one_own_job':True,'local3_machine5_j4_nice10':True,'no_olean_or_source_output':True};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
for line in b.decode().splitlines():
 if 'error' in line or 'depends on axioms' in line or line.startswith(('GUARDS|','COMPLETE|')):print(line)
sys.exit(p.returncode)
