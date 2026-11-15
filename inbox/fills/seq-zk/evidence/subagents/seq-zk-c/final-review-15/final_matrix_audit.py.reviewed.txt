"""Certify all final cells using exact native request, source, closure, pin and guard identities."""
from pathlib import Path
import json, subprocess, hashlib, collections, csv, re
E=Path('evidence'); FINAL='d842dc8f681f6b89499129f5b64a50d0e4587935'
def j(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def clos(p):
 d={}
 for l in Path(p).read_text().splitlines():
  if l.startswith('CLOSURE '):
   r=json.loads(l[8:]);d[r['module']]=r['closure']
 return d
closures=clos(E/'logs/final-repair-axioms/final-repair-collector.log')
cache={}
def content(rev,path):
 k=(rev,path)
 if k not in cache:cache[k]=subprocess.check_output(['git','show',rev+':'+path])
 return cache[k]
def readrows(p):return [json.loads(l) for l in Path(p).read_text().splitlines() if l.strip()]
oldreuse={}
for p in j(E/'rule10/final/reuse-provenance.json'):
 r=p['final'];oldreuse[(r['owner'],r['variant'],r['eval'])]=p
fresh={}
for path in sorted((E/'logs').glob('final-seals-stream-*/attributed-results.jsonl')):
 for r in readrows(path):fresh[(r['owner'],r['variant'],r['eval'])]=(r,path.parent)
repair={}
for path in sorted((E/'logs').glob('repaired-seals-stream-*/attributed-results.jsonl')):
 for r in readrows(path):repair[(r['owner'],r['variant'],r['eval'])]=(r,path.parent)
affected=set(j(E/'rule10/final-repair/affected-owners.json')['owners'])
cells=[];provenance={};pending=[]
for variant in ['coe','strict']:
 for letter in ['A','B']:
  m=E/'rule10/final-repair'/variant/('seal-'+letter)/'manifest.json'
  for p in j(m)['probes']:
   owner=p['module'];key=(owner,variant,letter);rp=m.parent/(p['label']+'.json');fin=j(rp)
   if owner in affected:
    selected=repair.get(key);origin='native final revision'
   elif key in oldreuse:
    x=oldreuse[key];log=Path(x['retained_log']);selected=(j(log.with_suffix('.attribution.json')),log.parent);origin='exact checkpoint 1 reuse'
   else:selected=fresh.get(key);origin='exact revision 5 reuse'
   if not selected:pending.append(key);continue
   r,out=selected;rec=j(r['record']);log=out/(r['label']+'.log');guard=log.with_suffix('.guards.json')
   if not guard.exists():pending.append(key);continue
   g=j(guard);assert g['native_identity_install_mask_eof_complete'];assert g['request_count']==fin['requested'];assert sha(log)==g['raw_log_sha256'];assert sha(r['record'])==g['record_sha256']
   assert rec['rows']==fin['rows'] and rec['source_sha256']==fin['source_sha256']
   source_rev=rec['rev'];pk=(owner,source_rev)
   if pk not in provenance:
    hashes={}
    for mod in closures[owner]+[owner]:
     path=mod.replace('.','/')+'.lean';a=content(source_rev,path);b=content(FINAL,path);assert a==b,(mod,source_rev);hashes[path]=hashlib.sha256(b).hexdigest()
    for path in ['lake-manifest.json','lean-toolchain']:assert content(source_rev,path)==content(FINAL,path)
    provenance[pk]=dict(owner=owner,native_source_revision=source_rev,final_revision=FINAL,source_and_full_TCSlib_closure_sha256=hashes,pins_equal=True)
   expected=10 if owner.endswith('.Defs') else 0
   assert len(r['errors'])==expected,(key,r['errors']);assert r['exit']==(1 if expected else 0)
   raw_errors=list(re.finditer(r'^\S+\.lean:(\d+):(\d+): error[:(]',log.read_text(),re.M))
   assert len(raw_errors)==len(r['errors'])==g['proof_error_diagnostics'],(key,'diagnostic mismatch')
   cells.append(dict(owner=owner,variant=variant,eval=letter,origin=origin,native_revision=source_rev,final_request_record=str(rp),native_request_record=r['record'],raw_log=str(log),guards=str(guard),requested=fin['requested'],error_count=len(r['errors']),failing_declarations=r['failing_declarations'],source_closure_identity_verified=True,exact_request_rows_verified=True))
summary=dict(final_revision=FINAL,expected_cells=164,completed=len(cells),pending=pending,origins=dict(collections.Counter(c['origin'] for c in cells)),zero_error_cells=sum(c['error_count']==0 for c in cells),inherited_Defs_error_cells=sum(c['error_count']>0 for c in cells),inherited_failing_declarations=sorted({n for c in cells for n in c['failing_declarations']}))
(E/'rule10/final-repair/selected-matrix.json').write_text(json.dumps(cells,indent=2)+'\n');(E/'rule10/final-repair/final-source-closure-provenance.json').write_text(json.dumps(list(provenance.values()),indent=2)+'\n');(E/'logs/final-rule10-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
with (E/'rule10/final-repair/selected-matrix.tsv').open('w') as f:
 fields=list(cells[0]) if cells else [];w=csv.DictWriter(f,fieldnames=fields,delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(cells)
print(json.dumps(summary,indent=2));assert not pending and len(cells)==164
