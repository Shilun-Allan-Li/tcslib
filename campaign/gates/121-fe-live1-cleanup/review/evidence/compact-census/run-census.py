from pathlib import Path
import subprocess,os,json,datetime,hashlib,time,sys,shutil
B=Path(__file__).resolve().parent
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
REPLAY=Path('/private/tmp/ab34-nfe2-replay')
phase=sys.argv[1];label=sys.argv[2];assert phase in ['BASE','HEAD']
prep=json.loads((B/'bindings/source-bindings.json').read_text())
receipt=json.loads((REPLAY/'RESULT.json').read_text())
assert receipt['pass'] and receipt['snapshot_valid']
assert receipt['modules']==receipt['expected_modules']==157 and receipt['failed']==0 and receipt['static_exit']==0
assert receipt['head']==prep['HEAD'] and receipt['source_unchanged_during_replay']
req=json.loads((REPLAY/'request.json').read_text());assert req['head']==prep['HEAD'] and req['snapshot_lean_commit']==prep['BASE']
source=json.loads((REPLAY/'source-before.json').read_text())
headmap=json.loads((B/'bindings/HEAD-all1003-Lean-map.json').read_text())
assert {p:v['git_blob'] for p,v in source.items()}==headmap
snapshot=Path(req['snapshot'] if phase=='BASE' else req['output'])
expected=json.loads((REPLAY/('input-before.json' if phase=='BASE' else 'output.json')).read_text())
def objects():
 return {str(f.relative_to(snapshot)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(snapshot.rglob('*.olean'))}
before=objects();assert len(before)==895 and before==expected
f=B/'runtime/CompactInventory.lean';data=f.read_bytes();assert data==(B/'CompactInventory.lean.txt').read_bytes()
d=B/'attempts'/label;d.mkdir()
(d/'source.lean.txt').write_bytes(data)
for name in ['RESULT.json','request.json']:
 shutil.copyfile(REPLAY/name,d/('guarded-replay-'+name))
(d/'snapshot-before.json').write_text(json.dumps(before,indent=2)+'\n')
e=dict(os.environ);e['TCSLIB_LEAN_SLOTS']='3'
cmd=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(R),str(snapshot),str(f)]
request={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'phase':phase,'source_commit':prep[phase],'command':cmd,'probe_SHA256':hashlib.sha256(data).hexdigest(),'source_guard_passed157':True,'source_map_all1003_exact':True,'whole_snapshot_objects':895,'snapshot':str(snapshot),'local_slots':3,'machine_cap':5,'j4_nice10_by_wrapper':True,'no_olean_output':True,'proof_values_rendered':False,'selection':'all nonprivate outside confirmed internal numeric proof-auxiliary Prop cohort, plus9 changed private roots','AX':'every constant owned by four modules; no library-global claim'}
(d/'request.json').write_text(json.dumps(request,indent=2)+'\n')
t=time.monotonic()
with (d/'raw.out').open('wb')as log:p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,env=e)
after=objects();unchanged=after==before and f.read_bytes()==data
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'phase':phase,'exit':p.returncode,'seconds':time.monotonic()-t,'source_commit':prep[phase],'probe_SHA256':hashlib.sha256(data).hexdigest(),'whole895_snapshot_unchanged':after==before,'probe_source_unchanged':f.read_bytes()==data,'actual_execution':True,'no_olean_output':True}
(d/'snapshot-after.json').write_text(json.dumps(after,indent=2)+'\n');(d/'run.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
assert unchanged
sys.exit(p.returncode)
