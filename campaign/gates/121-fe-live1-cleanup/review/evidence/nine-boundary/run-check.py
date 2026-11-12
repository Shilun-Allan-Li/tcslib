from pathlib import Path
import subprocess,os,json,datetime,hashlib,time,sys
O=Path(__file__).resolve().parent
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
label=sys.argv[1];f=O/'runtime'/sys.argv[2];b=f.read_bytes();d=O/'attempts'/label;d.mkdir()
(d/'source.lean.txt').write_bytes(b)
e=dict(os.environ);e['TCSLIB_LEAN_SLOTS']='3'
cmd=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(R),'/private/tmp/ab34-fe-live1-final-validation/live/oleans-fe1',str(f)]
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
(d/'request.json').write_text(json.dumps({'utc':start,'command':cmd,'source_sha256':hashlib.sha256(b).hexdigest(),'snapshot':'whole passed oleans-fe1 / 895 objects','source_base':'a93d1867d6ed9700f2fd89a28092e39a45db2dd2','scope':sys.argv[3],'local_slots':3,'machine_cap':5,'j4_nice10_by_wrapper':True,'no_olean_output':True},indent=2)+'\n')
t=time.time()
with (d/'raw.out').open('wb')as log:p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,env=e)
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':p.returncode,'wall_seconds':time.time()-t,'source_sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':f.read_bytes()==b,'actual_execution':True,'no_olean_output':True}
(d/'run.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
