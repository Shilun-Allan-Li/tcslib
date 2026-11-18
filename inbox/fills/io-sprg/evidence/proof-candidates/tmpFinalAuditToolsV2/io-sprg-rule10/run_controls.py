# io-sprg serial paired-control queue, Mac host 2026-11-18. Root only.
# Reuses runner_full.py and its one pinned lean-slot.sh invocation per probe.
# Archives overwritten logs; reuses only identical-source/log expected passes.
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
import runpy
bind=runpy.run_path(str(Path(__file__).with_name("environment_binding.py")))
ap=argparse.ArgumentParser();ap.add_argument('root');ap.add_argument('tree');ap.add_argument('run');a=ap.parse_args()
root=Path(a.root).resolve();home=root/a.run;logs=home/'control-runs';logs.mkdir(exist_ok=True)
environment=bind['snapshot'](a.tree,home)
binding=home/'control-environment-bindings.jsonl'
order=home/'orders/current-control.txt';order.parent.mkdir(exist_ok=True)
plans=[]
for variant in ['coe-A','coe-B','strict-A','strict-B']:
 plans.extend((variant,p) for p in json.loads((home/'controls'/variant/'controls-plan.json').read_text()))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def records():
 return [json.loads(l) for l in(logs/'results.jsonl').read_text().splitlines()] if(logs/'results.jsonl').exists() else[]
for sealed in [False,True]:
 for variant,rec in plans:
  if rec['sealed']!=sealed:continue
  mod=rec['module'];source=root/(mod+'.lean');log=logs/'mods'/(mod.replace('/','_')+'.log')
  expected_errors=sum(c['negative'] for c in rec['controls']) if sealed else 0
  expected_rc=int(expected_errors>0)
  previous=next((r for r in reversed(records()) if r.get('module')==mod),None)
  bound=bind['previous'](binding,mod)
  if previous and bound and bound['environment_sha256']==environment and bound['source_sha256']==sha(source) and bound['log_sha256']==previous['log_sha256'] and previous['source_sha256']==sha(source) and previous['rc']==expected_rc and previous['errors']==expected_errors and log.exists() and sha(log)==previous['log_sha256']:
   print('REUSE_IDENTICAL_EXPECTED '+variant+' '+mod,flush=True);continue
  if log.exists():
   archive=home/'control-log-archive';archive.mkdir(exist_ok=True);(archive/(sha(log)+'.log')).write_bytes(log.read_bytes())
  order.write_text(mod+'\n');print('START '+variant+' sealed='+str(sealed)+' '+mod,flush=True)
  subprocess.run(['python3','-I',str(root/'evidence/tools/seal/runner_full.py'),str(root),str(order),a.tree,str(logs)],cwd=root,check=True)
  actual=next(r for r in reversed(records()) if r.get('module')==mod)
  bind['record'](binding,actual,environment)
  print('END rc='+str(actual['rc'])+' errors='+str(actual['errors'])+' expected='+str(expected_errors)+' '+mod,flush=True)
  if actual['rc']!=expected_rc or actual['errors']!=expected_errors:
   archive=home/'failed-control-probes';archive.mkdir(exist_ok=True)
   (archive/(sha(source)+'.lean.txt')).write_bytes(source.read_bytes());(archive/(sha(log)+'.log')).write_bytes(log.read_bytes())
   print('UNEXPECTED_CONTROL_FAILURE_STOP',flush=True);sys.exit(1)
 if not sealed:
  (home/'unsealed-pretest.json').write_text(json.dumps(dict(all_ok=True,bad=[],qualification='All current unsealed source/log hashes checked by the resumable queue; exact outcomes additionally checked by ctlcheck2 and dynamic_counts.'))+'\n')
print('CONTROL_QUEUE_COMPLETE '+str(len(plans)),flush=True)
