"""Plan the full matrix; reuse only exact source/closure/pin/request/guard matches."""
from pathlib import Path
import json,subprocess,hashlib
root=Path.cwd();rev='7cecd426dddac78789c9e7fc627a7cd013d67792';baseout=Path('evidence/rule10/final')
def closures(path):
 d={}
 for l in Path(path).read_text().splitlines():
  if l.startswith('CLOSURE '):
   r=json.loads(l[8:]);d[r['module']]=r['closure']
 return d
oldc=closures('evidence/logs/checkpoint1-axioms/002-.lake__seq-zk-rule10__checkpoint1__Collect.log');newc=closures('evidence/logs/final-axioms/final-collector.log')
oldplan=json.loads(Path('evidence/rule10/checkpoint1/stable-helper-matrix-plan.json').read_text());oldmap={}
for r in oldplan:
 record=json.loads(Path(r['record']).read_text());variant='coe' if '/coe/' in r['record'] else 'strict';letter='A' if '/seal-A/' in r['record'] else 'B';oldmap[(variant,letter,record['module'])]=(r,record)
cache={}
def contents(rev,path):
 key=(rev,path)
 if key not in cache:cache[key]=subprocess.check_output(['git','show',rev+':'+path])
 return cache[key]
allrows=[];reuse=[];fresh=[]
for variant in ['coe','strict']:
 for letter in ['A','B']:
  manifest=baseout/variant/('seal-'+letter)/'manifest.json'
  for p in json.loads(manifest.read_text())['probes']:
   rp=manifest.parent/(p['label']+'.json');record=json.loads(rp.read_text());r=dict(module=p['probe_module'],label='final-'+variant+'-'+p['label'],record=str(rp),owner=p['module'],variant=variant,eval=letter,requested=p['requested']);allrows.append(r)
   previous=oldmap.get((variant,letter,p['module']))
   if previous:
    plan,old=previous;assert old['source_sha256']==record['source_sha256'];assert old['rows']==record['rows'];assert oldc[p['module']]==newc[p['module']]
    assert contents(old['rev'],'lake-manifest.json')==contents(rev,'lake-manifest.json');assert contents(old['rev'],'lean-toolchain')==contents(rev,'lean-toolchain')
    hashes={}
    for m in oldc[p['module']]+[p['module']]:
     path=m.replace('.','/')+'.lean';a=contents(old['rev'],path);b=contents(rev,path);assert a==b,(m,old['rev'],rev);hashes[path]=hashlib.sha256(a).hexdigest()
    log=Path('evidence/logs/stable-helper-matrix')/(plan['label']+'.log');guard=log.with_suffix('.guards.json');g=json.loads(guard.read_text());assert g['native_identity_install_mask_eof_complete'] and g['request_count']==record['requested']
    att=json.loads(log.with_suffix('.attribution.json').read_text());expected=10 if p['module'].endswith('.Defs') else 0;assert len(att['errors'])==expected
    reuse.append(dict(final=r,retained=plan,retained_guard=str(guard),retained_log=str(log),errors=expected,source_closure_sha256=hashes,pins_equal=True,exact_request_rows_equal=True))
   else:fresh.append(r)
assert len(allrows)==164 and len(reuse)==20 and len(fresh)==144,(len(allrows),len(reuse),len(fresh))
(baseout/'complete-matrix-plan.json').write_text(json.dumps(allrows,indent=2)+'\n');(baseout/'reuse-provenance.json').write_text(json.dumps(reuse,indent=2)+'\n')
# Start every canonical eval-excluded cell before stress variants in each stream.
groups=[[] for _ in range(3)];weights=[0,0,0]
for r in sorted(fresh,key=lambda r:(0 if r['variant']=='coe' and r['eval']=='A' else 1,-r['requested'],r['label'])):
 i=min(range(3),key=lambda j:weights[j]);groups[i].append(r);weights[i]+=r['requested']
for i,rows in enumerate(groups,1):(baseout/f'stream-{i}-plan.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(total=len(allrows),exact_reused=len(reuse),fresh=len(fresh),streams=[len(g) for g in groups],request_weights=weights)))
