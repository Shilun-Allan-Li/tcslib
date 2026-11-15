"""Verify retained paired controls against unchanged definition-home import closures and final requests."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path('evidence');old='e978a28274fdeb545e622ae28747221088352512';new='d842dc8f681f6b89499129f5b64a50d0e4587935'
def j(p):return json.loads(Path(p).read_text())
cache={}
def src(rev,mod):
 k=(rev,mod)
 if k not in cache:cache[k]=subprocess.check_output(['git','show',rev+':'+mod.replace('.','/')+'.lean'])
 return cache[k]
def closure(mod):
 seen=set()
 def visit(m):
  if m in seen:return
  seen.add(m)
  for d in re.findall(r'^import\s+(TCSlib\.\S+)',src(new,m).decode(),re.M):visit(d)
 visit(mod);return sorted(seen)
rs=[json.loads(l) for l in (E/'logs/checkpoint2-controls/control-results.jsonl').read_text().splitlines()];assert len(rs)==10
out=[]
for r in rs:
 assert r['expectation_passed'];assert len(r['errors'])==(1 if r['sealed'] else 0)
 source=E/'rule10/checkpoint2/coe/sources'/(r['module'].split('/')[-1]+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
 hashes={}
 for home in r['direct_imports']:
  if home.startswith('TCSlib.'):
   for m in closure(home):
    b=src(new,m);assert b==src(old,m),m;hashes[m]=hashlib.sha256(b).hexdigest()
 if r['sealed']:
  g=j(Path(r['raw_log']).with_suffix('.guards.json'));assert g['native_identity_install_mask_eof_complete'];assert g['request_count']==1
  fin=E/'rule10/final-repair/coe'/('seal-'+r['variant'])/(r['request_record']+'.json');rows=j(fin)['rows'];assert any(x['spelling']==r['target'] for x in rows)
 for p in ['lake-manifest.json','lean-toolchain']:assert subprocess.check_output(['git','show',old+':'+p])==subprocess.check_output(['git','show',new+':'+p])
 out.append(dict(label=r['label'],target=r['target'],variant=r['variant'],sealed=r['sealed'],errors=len(r['errors']),raw_log=r['raw_log'],unchanged_definition_home_closure_sha256=hashes,native_source_sha256=r['source_sha256'],pins_equal=True,final_requested_identity_verified=bool(r['sealed'])))
summary=dict(retained_controls=10,unsealed_pass=5,sealed_negative_exactly_one_failure_positive_pass=5,source_and_full_definition_home_closures_unchanged=True,pins_equal=True,old_revision=old,final_revision=new,records=out)
(E/'rule10/final-repair/control-reuse-provenance.json').write_text(json.dumps(summary,indent=2)+'\n');print('PASS: all 10 retained native controls, full definition-home closures/pins, sealed identities and guards')
