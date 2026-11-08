from pathlib import Path
import json,gzip,hashlib,difflib,re,collections
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());B=Path(ctx['baseline_frozen_folder']);d=json.loads((P/'delta-base-head.json').read_text());wanted={r['name']for r in d['shared_field_changes']['typeExprSHA256']};types={}
for side,archive in [('Base',B/'Base.out.gz'),('Head',P/'Head-inventory.out.gz')]:
 t={}
 for line in gzip.open(archive,'rt'):
  if line.startswith('CENSUS|'):
   r=json.loads(line.split('|',1)[1])
   if r['name']in wanted:t[r['name']]=r['typeExpr']
 assert set(t)==wanted;types[side]=t
rows=[]
for n in sorted(wanted):
 a=types['Base'][n];b=types['Head'][n];ac=collections.Counter(re.findall(r'Lean.Expr.const `([^\s\[\]]+)',a));bc=collections.Counter(re.findall(r'Lean.Expr.const `([^\s\[\]]+)',b));sm=difflib.SequenceMatcher(None,a.splitlines(),b.splitlines(),autojunk=False);diffs=[]
 for tag,i,j,k,l in sm.get_opcodes():
  if tag!='equal':diffs.append({'tag':tag,'base_lines':[i+1,j],'head_lines':[k+1,l],'base':'\n'.join(a.splitlines()[i:j]),'head':'\n'.join(b.splitlines()[k:l])})
 rows.append({'name':n,'base_type_bytes':len(a.encode()),'base_type_sha256':hashlib.sha256(a.encode()).hexdigest(),'head_type_bytes':len(b.encode()),'head_type_sha256':hashlib.sha256(b.encode()).hexdigest(),'constant_occurrences_removed':dict(ac-bc),'constant_occurrences_added':dict(bc-ac),'exact_line_differences':diffs})
(P/'all94-exact-type-expression-differences.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
auth=json.loads((P/'metadata-summary.json').read_text())['public_authored_shared_type_changes']
for r in rows:
 if r['name']in auth:
  print(r['name'],'BYTES',r['base_type_bytes'],r['head_type_bytes'],'BLOCKS',len(r['exact_line_differences']))
  print('CONSTS',r['constant_occurrences_removed'],r['constant_occurrences_added'])
  for q in r['exact_line_differences'][:5]:print('DIFF',q['base'][:1500],'=>',q['head'][:1500])
print('CHANGED_AUTH_PRIVATE')
for r in json.loads((P/'all-shared-type-changes-classified.json').read_text()):
 if r['head_classification']['category']=='authored private source declaration':print(r['name'])
