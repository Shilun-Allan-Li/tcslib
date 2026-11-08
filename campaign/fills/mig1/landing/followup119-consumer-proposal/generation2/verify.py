"""Read-only independent generation2 exact-source/header/patch reconciliation."""
from pathlib import Path
import ast,collections,hashlib,importlib.util,json,os,re,subprocess,sys
sys.dont_write_bytecode=True
p=Path(__file__).resolve().parent;parent=p.parent;root=parent.parents[4]
H=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
# Reviewed maintainer-owned parser: import guarded pure definitions, never payload scripts.
parser_path=root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py'
spec=importlib.util.spec_from_file_location('maintainer_source_parser',parser_path)
P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
qa_path=root/'campaign/fills/mig1/landing/review-final-source-final/source_review.py'
tree=ast.parse(qa_path.read_text());fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='split_header')
ns={'P':P,'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(qa_path),'exec'),ns);split_header=ns['split_header']
controls=[('theorem x (h : P (input := x)) : True := by\n  trivial\n','True'),('lemma y :\n    let B := machine x\n    P B := by\n  exact h\n','P B'),('lemma z :\n    let V : T := by\n      have h := p\n      exact t h\n    let n := f (input := x)\n    Q V n := by\n  exact z\n','Q V n')]
for text,last in controls:
 h,d,b=split_header(text);assert h.endswith(last) and d==':=' and b.startswith('by\n')
P.header=lambda s:P.norm(split_header(s)[0])
def decls(s):
 ds=P.decls(s)
 for d in ds:
  raw=d['raw'];doc=re.search(r'(?m)^/(?:--|-!)',raw)
  if doc:raw=raw[:doc.start()]
  d['raw']=raw.rstrip()+'\n';h,delimiter,b=split_header(d['raw']);d['header']=h;d['body']=b
 return ds
receipt=json.loads((p/'receipt.json').read_text());sweep=json.loads((parent/'sweep-inventory.json').read_text());changes=receipt['changes'];assert len(changes)==15
sources={r['file']:(parent/'sweep-inputs'/(r['file'].replace('/','__')+'.txt')).read_text() for r in sweep['source_files']}
current=dict(sources)
for row in receipt['files']:
 f=row['file'];owner=Path(f).stem;after=(p/'inputs'/f'{owner}-after15-b1-REQUIRES-INTEGRATED-API119.lean.txt').read_text()
 assert H(sources[f])==row['before_sha256'] and H(after)==row['after_sha256'];current[f]=after
# Independent exact in-memory unified-hunk reader; mismatches are rejected, no patch process.
def patch(text,state):
 lines=text.splitlines(keepends=True);i=0;paths=[]
 while i<len(lines):
  assert lines[i].startswith('--- a/');f=lines[i][6:].rstrip('\n');i+=1
  assert lines[i]=='+++ b/'+f+'\n';i+=1;old=state[f].splitlines(keepends=True);out=[];pos=0
  while i<len(lines) and not lines[i].startswith('--- a/'):
   m=re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@\n',lines[i]);assert m,lines[i]
   a,n,b,mn=[int(v) if v is not None else 1 for v in m.groups()];i+=1
   assert a-1>=pos;out+=old[pos:a-1];pos=a-1;assert len(out)==b-1;used=made=0
   while used<n or made<mn:
    line=lines[i];i+=1;tag=line[0];assert tag in ' +-'
    if tag in ' -':assert old[pos]==line[1:];pos+=1;used+=1
    if tag in ' +':out.append(line[1:]);made+=1
   assert used==n and made==mn
  out+=old[pos:];state[f]=''.join(out);paths.append(f)
 return paths
roundtrip=dict(sources);paths=patch((p/'all15-bodies.patch').read_text(),roundtrip);assert roundtrip==current and len(paths)==6
old={f:decls(s) for f,s in sources.items()};new={f:decls(s) for f,s in current.items()};stats=[];changed=[];removed=[]
expected={('TCSlib/Complexity/TuringMachine/'+('Build/' if x['file'] in ['Loop','Primitives','Catalog','Wrappers'] else '')+x['file']+'.lean','Turing.FinTM.'+x['declaration']) for x in changes if x['declaration']!='redirectTM_spaceUsedByTape'}
for f in sources:
 a={d['name']:d for d in old[f]};b={d['name']:d for d in new[f]};assert not set(b)-set(a)
 removed.extend((f,n) for n in set(a)-set(b))
 assert [d['name'] for d in old[f] if d['name'] in b]==[d['name'] for d in new[f]]
 for n in set(a)&set(b):
  x,y=a[n],b[n];assert (x['header'],x['kind'],x['private'])==(y['header'],y['kind'],y['private'])
  if x['raw']!=y['raw']:
   assert x['kind'] in ['lemma','theorem'];assert (f,n) in expected
   changed.append({'file':f,'name':n,'private':y['private'],'header_sha256':H(y['header']),'before_body_sha256':H(x['body']),'after_body_sha256':H(y['body']),'line_after':y['start']})
  else:assert x['body']==y['body']
 assert P.imports(sources[f])==P.imports(current[f])
 # Exact differences are wholly accounted by reviewed theorem chunks and one block deletion.
 reconstructed=sources[f]
 for ch in changes:
  if ch['file']!=Path(f).stem or ch['declaration']=='redirectTM_spaceUsedByTape':continue
  name=ch['declaration'];before=(p/'inputs'/f'{ch["file"]}-{name}-before.lean.txt').read_text();after=(p/'inputs'/f'{ch["file"]}-{name}-after.lean.txt').read_text();assert reconstructed.count(before)==1;reconstructed=reconstructed.replace(before,after,1)
 if f.endswith('/Catalog.lean'):
  block=(parent/'inputs/removed-Catalog-redirect-block.lean.txt').read_text();assert reconstructed.count(block)==1;reconstructed=reconstructed.replace(block,'',1)
 assert reconstructed==current[f]
 stats.append({'file':f,'public_before':sum(not d['private'] for d in old[f]),'public_after':sum(not d['private'] for d in new[f]),'private_before':sum(d['private'] for d in old[f]),'private_after':sum(d['private'] for d in new[f]),'source_sha256_after':H(current[f])})
assert {(x['file'],x['name']) for x in changed}==expected and len(changed)==14
assert removed==[('TCSlib/Complexity/TuringMachine/Build/Catalog.lean','Turing.FinTM.redirectTM_spaceUsedByTape')]
# Literal source-target admission checks; global compiled census is outside this draft.
targets=json.loads((root/'campaign/fills/mig1/inputs/target-admissions.json').read_text());targetrows=[]
for t in targets:
 a=next(d for d in old[t['path']] if d['name']==t['name']);b=next(d for d in new[t['path']] if d['name']==t['name']);assert a['header']==b['header'];assert not re.search(r'\b(?:sorry|admit)\b',P.clean(b['body']));targetrows.append({'name':t['name'],'header_exact':True,'source_proof_filled':True})
assert len(targetrows)==17
residuals=[]
for f,ds in new.items():
 for d in ds:
  if re.search(r'\b(?:sorry|admit)\b',P.clean(d['body'])):
   a=next(x for x in old[f] if x['name']==d['name']);assert a['raw']==d['raw'];residuals.append({'file':f,'name':d['name'],'unchanged':True})
assert len(residuals)==3 and all('/RAMSimulation/' in r['file'] for r in residuals)
# Optional sketches modify comments only and reproduce their own provided inert source copies.
withdocs=dict(current);docpaths=patch((p/'optional-sketches-after-bodies.patch').read_text(),withdocs)
for f in sources:
 assert P.norm(P.clean(current[f]))==P.norm(P.clean(withdocs[f]))
 if f in docpaths:
  owner=Path(f).stem;assert withdocs[f]==(p/'inputs'/f'{owner}-after15-body-and-sketch-b1-REQUIRES-INTEGRATED-API119.lean.txt').read_text()
# Full generation1 is frozen before extensions; every manifest byte still matches.
gen1=json.loads((parent/'generation1-manifest.json').read_text())
for r in gen1['files']:
 b=(parent/r['path']).read_bytes();assert H(b)==r['sha256'] and len(b)==r['bytes']
# Actual checkout remains exact all12 original bytes, no staging/source action.
wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-epad');env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
git=lambda *a:subprocess.run(['git','-C',str(wt),*a],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env).stdout
assert git('rev-parse','HEAD').decode().strip()==receipt['baseline']
assert not git('diff','--name-only','--','*.lean').strip() and not git('diff','--cached','--name-only','--','*.lean').strip()
for f,s in sources.items():assert (wt/f).read_text()==s and git('show',receipt['baseline']+':'+f)==s.encode()
summary={'status':'PASS source-only exact15hunk construction; additional9production rewrites NOT native checked','generation1_inputs_outputs_receipts_still_byte_frozen':True,'patch_roundtrip_exact_all12':True,'changed_files':paths,'changed_proof_bodies':changed,'changed_proof_count':len(changed),'private_body_changes':sum(x['private'] for x in changed),'public_body_changes':sum(not x['private'] for x in changed),'removed_exact_owner_adoption':removed,'public_added':[],'private_added_or_removed':[],'all_surviving_headers_attributes_relative_order_homes_imports_exact':True,'all_runtime_type_instance_data_bodies_literal_including_existing_two_inj_proofs':True,'selected_header_reader_controls_passed':True,'header_reader_sources':[{ 'path':str(parser_path.relative_to(root)),'sha256':H(parser_path.read_bytes())},{'path':str(qa_path.relative_to(root)),'sha256':H(qa_path.read_bytes()),'executed_scope':'Only reviewed pure split_header function AST, not source-review top level'}],'twelve_file_source_counts':stats,'target_admissions_filled':17,'target_checks':targetrows,'RAM_residuals':residuals,'optional_sketch_patch_comment_only':True,'actual_b1_Lean_source_and_index_unchanged':True,'integration_limits':'No source/API/debt/audit acceptance or speculative fullsource native/seal/replay/screen. Saved fullfiles are b1-relative documentation, not overwrite payloads after API119 merge.'}
(p/'freeze.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['changed_proof_bodies','twelve_file_source_counts','target_checks','header_reader_sources']},indent=2))
