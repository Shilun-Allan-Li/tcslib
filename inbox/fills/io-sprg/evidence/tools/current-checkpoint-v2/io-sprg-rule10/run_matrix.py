# io-sprg serial Rule10 matrix,2026-11-18. Root execution only.
# Reuses the audited Mac runner without changing it; each probe holds exactly one
# pinned lean-slot.sh slot and produces no olean. Canonical failures stop early.
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
import runpy
bind=runpy.run_path(str(Path(__file__).with_name("environment_binding.py")))
ap=argparse.ArgumentParser();ap.add_argument('root');ap.add_argument('tree');ap.add_argument('run');a=ap.parse_args()
root=Path(a.root).resolve();home=root/a.run;logs=home/'seal-runs';logs.mkdir(exist_ok=True)
environment=bind['snapshot'](a.tree,home)
binding=home/'seal-environment-bindings.jsonl'
order=home/'orders/current-seal.txt';order.parent.mkdir(exist_ok=True)
all_order=[]
for variant in ['coe-A','coe-B','strict-A','strict-B']:
 manifest=json.loads((home/'seals'/variant/'manifest.json').read_text())
 all_order.extend(p['probe_module'] for p in manifest['probes'])
(home/'orders/seals-full.txt').write_text(''.join(m+'\n' for m in all_order))
for variant in ['coe-A','coe-B','strict-A','strict-B']:
 manifest=json.loads((home/'seals'/variant/'manifest.json').read_text())
 for item in manifest['probes']:
  mod=item['probe_module'];order.write_text(mod+'\n')
  if (logs/'results.jsonl').exists():
   prior=[json.loads(l) for l in(logs/'results.jsonl').read_text().splitlines()]
   previous=next((r for r in reversed(prior) if r.get('module')==mod),None)
   digest=hashlib.sha256((root/(mod+'.lean')).read_bytes()).hexdigest()
   bound=bind['previous'](binding,mod)
   if previous and bound and bound['environment_sha256']==environment and bound['source_sha256']==digest and bound['log_sha256']==previous['log_sha256'] and previous['rc']==previous['errors']==0 and previous['source_sha256']==digest:
    log=logs/'mods'/(mod.replace('/','_')+'.log')
    if log.exists() and hashlib.sha256(log.read_bytes()).hexdigest()==previous['log_sha256']:
     print('REUSE_IDENTICAL_PASS '+variant+' '+mod,flush=True);continue
  log=logs/'mods'/(mod.replace('/','_')+'.log')
  if log.exists():
   archive=home/'log-archive';archive.mkdir(exist_ok=True)
   digest=hashlib.sha256(log.read_bytes()).hexdigest()
   (archive/(digest+'.log')).write_bytes(log.read_bytes())
  print('START '+variant+' '+mod,flush=True)
  subprocess.run(['python3','-I',str(root/'evidence/tools/seal/runner_full.py'),str(root),str(order),a.tree,str(logs)],cwd=root,check=True)
  records=[json.loads(l) for l in(logs/'results.jsonl').read_text().splitlines()]
  rec=next(r for r in reversed(records) if r.get('module')==mod)
  bind['record'](binding,rec,environment)
  if rec['rc'] or rec['errors']:
   archive=home/'failed-probes';archive.mkdir(exist_ok=True)
   (archive/(rec['source_sha256']+'.lean.txt')).write_bytes((root/(mod+'.lean')).read_bytes())
   log=logs/'mods'/(mod.replace('/','_')+'.log')
   (archive/(rec['log_sha256']+'.log')).write_bytes(log.read_bytes())
  print('END '+variant+' rc='+str(rec['rc'])+' errors='+str(rec['errors'])+' '+mod,flush=True)
  if variant.startswith('coe-') and (rec['rc'] or rec['errors']):
   print('CANONICAL_FAILURE_STOP '+mod,flush=True);sys.exit(1)
print('FULL_MATRIX_COMPLETE '+str(len(all_order)),flush=True)
