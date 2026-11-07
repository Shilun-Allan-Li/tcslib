"""Per-example coverage and fixed-total adversarial check for all 37 seal pairs."""
from pathlib import Path
import json,re,hashlib
out=Path(__file__).resolve().parent
src=(out/'Controls-37-sealed-v1.lean.txt').read_text();raw=(out/'Controls-37-sealed-v1.out').read_text();lines=src.splitlines();starts=[];pair=None;form=0
for i,l in enumerate(lines,1):
 m=re.match(r'-- (C\d\d)\b',l)
 if m:pair=m[1];form=0
 if l.startswith('example'):
  form+=1;assert pair and form<=2;starts.append({'pair':pair,'form':form,'line':i})
assert len(starts)==74 and len({r['pair'] for r in starts})==37
ends=[r['line'] for r in starts[1:]]+[len(lines)+1]
def diagnostics(s):
 return [{'line':int(m[1]),'col':int(m[2]),'message':m[3]} for m in re.finditer(r'^.*?:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$',s,re.M)]
def check(ds):
 assert len(ds)==74,('total',len(ds))
 rows=[];used=[]
 for r,end in zip(starts,ends):
  owned=[(i,d) for i,d in enumerate(ds) if r['line']<=d['line']<end]
  assert len(owned)==1,('multiplicity',r,len(owned))
  i,d=owned[0];assert 'rfl' in d['message'],('kind',d);used.append(i);rows.append(dict(r,next_example_line=end,diagnostic=d))
 assert sorted(used)==list(range(74)),'unmapped'
 return rows
ds=diagnostics(raw);rows=check(ds)
assert len(ds)==74
# Same total, duplicated first goal and omitted second: must reject per-goal multiplicity.
synthetic=[ds[0],ds[0]]+ds[2:];assert len(synthetic)==74
try:check(synthetic)
except AssertionError as e:negative={'rejected':True,'same_total':True,'reason':repr(e.args)}
else:raise AssertionError('duplicate/drop guard accepted')
# Actual earlier ineffective q0 controls must also be rejected.
try:check(diagnostics((out/'Controls-36-sealed-v1.out').read_text()))
except AssertionError as e:earlier={'rejected':True,'reason':repr(e.args)}
else:raise AssertionError('rejected v1 accepted')
u=json.loads((out/'Controls-37-unsealed-v1-run.json').read_text());s=json.loads((out/'Controls-37-sealed-v1-run.json').read_text());assert u['exit']==0 and u['errors']==0;assert s['exit']==1 and s['errors']==74
manifest=json.loads((out/'Final-sections-sealed-v2-manifest.json').read_text());defs=re.search(r'^attribute \[local irreducible\] (.*)$',src,re.M)[1].split();assert set(defs)==set(manifest['definitions']) and len(defs)==37
result={'pairs':37,'goals':74,'unsealed_exit':u['exit'],'unsealed_errors':0,'sealed_exit':s['exit'],'sealed_errors':74,'one_rfl_failure_per_goal':True,'no_unmapped_errors':True,'all37definitions_matched_to_control_pairs':True,'synthetic_duplicate_drop':negative,'prior_invalid_attempt_rejected_by_final74_contract':earlier,'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'output_sha256':hashlib.sha256(raw.encode()).hexdigest(),'rows':rows}
(out/'controls37-coverage.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
