from pathlib import Path
import json,hashlib,datetime
O=Path('/private/tmp/ab34-safe-run-bridge-refinement');assert not (O/'MANIFEST.json').exists()
files=[]
for p in sorted(O.rglob('*')):
 assert not p.is_symlink(),str(p)
 if p.is_file():
  b=p.read_bytes();files.append({'path':p.relative_to(O).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
manifest={'status':'FROZEN_PRIVATE_REFINEMENT_PREFLIGHT_ROOT_ADOPTION_PENDING','frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_file_count':len(files),'payload_bytes':sum(r['bytes'] for r in files),'files':files,'manifest_self_excluded':True,'no_actual_source_Git_canonical_mutation':True,'no_new_replay_or_fullscreen_claim':True}
(O/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
for r in files:
 p=O/r['path'];assert p.stat().st_size==r['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
for n in ['MANIFEST.json','README.md','bridge-refinement.patch','owner-proposed.lean.txt','RESULTS.json']:
 p=O/n;print(n,hashlib.sha256(p.read_bytes()).hexdigest())
print('FROZEN',len(files),'files',manifest['payload_bytes'],'bytes')
