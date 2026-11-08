import ast, collections, datetime, hashlib, io, json, pathlib, re, subprocess, sys
R = pathlib.Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
O = pathlib.Path(__file__).resolve().parent
RAW_PINS = {
 'records':'8f14c7f1f67ccfb1c03613531abd91fea40c4d46',
 'campaign_source':'df4341236e04a861e65e29d58b35a713f14c819c',
 'SG1':'b12902832c67210acd737d87d2d0c761bd5b35eb',
 'MIG':'55df52da9754f04b0c71646df29f83f33ec3aa52',
 'SG1_actual_full':'078263a74fe90b92aa6228cf20e43726138afbe6',
 'MIG_actual_full':'eaecd6b2afd992ead0844fa5f351eaf143fd1d1c'}
def git(*args): return subprocess.check_output(['git',*args],cwd=R)
def save(n,o): (O/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
pins={}
for k,v in RAW_PINS.items():
 c=git('rev-parse',v+'^{commit}').decode().strip(); git('cat-file','-e',c+'^{commit}')
 pins[k]={'commit':c,'parents':git('show','-s','--format=%P',c).decode().split(),'object_type':git('cat-file','-t',c).decode().strip()}
def tree(c):
 out={}
 for e in git('ls-tree','-rz','--full-tree',c).split(b'\0'):
  if not e: continue
  head,p=e.split(b'\t',1); mode,typ,h=head.decode().split(); p=p.decode()
  if p.endswith('.lean'): out[p]=h
 return out
maps={k:tree(v['commit']) for k,v in pins.items()}
assert all(len(v)==1003 for v in maps.values())
assert maps['records']==maps['campaign_source']
C=maps['records'];S=maps['SG1'];M=maps['MIG']
Sfiles=sorted(p for p in set(C)|set(S) if C.get(p)!=S.get(p)); Mfiles=sorted(p for p in set(C)|set(M) if C.get(p)!=M.get(p))
assert set(Sfiles).isdisjoint(Mfiles)
combined=dict(C)
for p in Sfiles: combined[p]=S[p]
for p in Mfiles: combined[p]=M[p]
maps['prospective_disjoint_source_union']=combined
actual_tree=git('rev-parse','24dc5b7469720646eba3e002156fcd677ca182af^{tree}').decode().strip()
git('cat-file','-e',actual_tree+'^{tree}')
assert git('cat-file','-t',actual_tree).decode().strip()=='tree'
maps['root_prospective_merge_tree']=tree(actual_tree)
assert maps['root_prospective_merge_tree']==combined
unique=sorted(set(h for mp in maps.values() for h in mp.values()))
proc=subprocess.run(['git','cat-file','--batch'],input=('\n'.join(unique)+'\n').encode(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=R,check=True)
f=io.BytesIO(proc.stdout); blobs={}
for expected in unique:
 h,t,n=f.readline().decode().split(); b=f.read(int(n)); assert f.read(1)==b'\n'; assert h==expected and t=='blob'
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h
 blobs[h]=b
assert not f.read()
def imports(src):
 # Header lexer only: nested comments, line comments, optional prelude, import commands.
 n=len(src);p=0;out=[];lines=[]
 def skip(p):
  while p<n:
   if src[p].isspace(): p+=1
   elif src.startswith('--',p):
    q=src.find('\n',p);p=n if q<0 else q+1
   elif src.startswith('/-',p):
    depth=1;p+=2
    while depth:
     assert p<n, 'unclosed header comment'
     if src.startswith('/-',p): depth+=1;p+=2
     elif src.startswith('-/',p):depth-=1;p+=2
     else:p+=1
   else: break
  return p
 while True:
  p=skip(p)
  if src.startswith('prelude',p) and (p+7==n or src[p+7].isspace()):p+=7;continue
  m=re.match(r'import\b',src[p:])
  if not m:break
  p+=m.end()
  # In this repository all imports occupy one physical line; verify against independent parser.
  q=src.find('\n',p);q=n if q<0 else q
  content=src[p:q].split('--',1)[0].strip()
  names=content.split();assert names
  assert all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',x) for x in names),content
  out.extend(names);lines.append({'line':src.count('\n',0,p)+1,'modules':names});p=q
 return {'imports':out,'import_commands':lines,'first_body_line':src.count('\n',0,p)+1}
control='/- outer /- inner -/ tail -/\n-- line\nimport TCSlib.One TCSlib.Two -- c\nimport Mathlib.X\ndef x := 0\n'
assert imports(control)['imports']==['TCSlib.One','TCSlib.Two','Mathlib.X']
headers={h:imports(b.decode()) for h,b in blobs.items()}
# AST-isolate just the inspected header reader from the repository; never execute its main.
graph_src=(R/'devtools/seyoon/graph.py').read_text()
fn=next(n for n in ast.parse(graph_src).body if isinstance(n,ast.FunctionDef) and n.name=='imports_of')
fn.name='reference_imports';refmod=ast.Module(body=[fn],type_ignores=[]);ast.fix_missing_locations(refmod)
for h,b in blobs.items():
 ns={'open':lambda *a, _s=b.decode(), **k:io.StringIO(_s)};exec(compile(refmod,'<isolated-header-parser>','exec'),ns)
 assert headers[h]['imports']==ns['reference_imports']('unused'),h
# Complete internal graph at each endpoint and the source union, with explicit package boundaries.
def module(p): return p[:-5].replace('/','.')
def path(m): return m.replace('.','/')+'.lean'
graphs={k:{module(p):headers[h]['imports'] for p,h in mp.items() if p.startswith('TCSlib')} for k,mp in maps.items()}
for k,g in graphs.items():
 for m,imps in g.items():
  for i in imps: assert not i.startswith('TCSlib') or i in g,(k,m,i)
def closure(g,owner):
 todo=[owner];seen=set();ext=set()
 while todo:
  m=todo.pop()
  if m in seen:continue
  if m not in g:ext.add(m);continue
  seen.add(m);todo.extend(g[m])
 return seen,ext
def shortest(g,owner,target):
 todo=collections.deque([[owner]]);seen=set()
 while todo:
  q=todo.popleft();m=q[-1]
  if m==target:return q
  if m in seen:continue
  seen.add(m);todo.extend(q+[i] for i in g.get(m,[]) if i in g)
 return None
Smods=[module(p) for p in Sfiles];Mmods=[module(p) for p in Mfiles]
allclosures={};effects={}
for label,owners,other in [('MIG',Mmods,Smods),('SG1',Smods,Mmods)]:
 before=graphs[label]; after=graphs['prospective_disjoint_source_union']; rows=[];union_b=set();union_a=set()
 for owner in owners:
  b,be=closure(before,owner);a,ae=closure(after,owner);union_b|=b;union_a|=a
  rb=[m for m in other if m in b];ra=[m for m in other if m in a]
  rows.append({'owner':owner,'before_closure':sorted(b),'before_external_boundary':sorted(be),'after_closure':sorted(a),'after_external_boundary':sorted(ae),'before_module_count':len(b),'after_module_count':len(a),'new_internal_modules':sorted(a-b),'lost_internal_modules':sorted(b-a),'new_external_boundaries':sorted(ae-be),'lost_external_boundaries':sorted(be-ae),'other_PR_changed_upstream_before':rb,'other_PR_changed_upstream_after':ra,'shortest_upstream_paths':{t:shortest(after,owner,t) for t in ra}})
 allclosures[label]={'rows':rows,'union_before':sorted(union_b),'union_after':sorted(union_a),'union_before_count':len(union_b),'union_after_count':len(union_a)}
 effects[label]={'affected_owner_count':sum(bool(r['other_PR_changed_upstream_after']) for r in rows),'owners_adding_import_modules':{r['owner']:r['new_internal_modules'] for r in rows if r['new_internal_modules']},'upstream_intersection':sorted(set(other)&union_a),'owner_upstream_path_table':{r['owner']:r['shortest_upstream_paths'] for r in rows}}
save('git-pins-and-source-maps.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pins':pins,'Lean_file_counts':{k:len(v) for k,v in maps.items()},'records_equals_F6_source_all_Lean':True,'SG1_changed_files':Sfiles,'MIG_changed_files':Mfiles,'changed_file_intersection':[],'prospective_union_method':'per-path SG1 and MIG changes relative to records; disjoint paths only. Not an executed merge or Git tree object; root verifies actual merge-tree map.','path_to_blob_maps':maps,'unique_source_blobs_verified':len(blobs),'root_created_actual_merge_tree':actual_tree,'root_actual_tree_equals_independent_disjoint_source_union_all_Lean':True})
save('full-source-import-graphs.json',{'method':'header parser with nested-comment/multiple-import control and exact agreement with AST-isolated maintainer imports_of on every unique source blob','reference_parser_source_sha256':hashlib.sha256(graph_src.encode()).hexdigest(),'graphs':graphs,'source_headers':{h:headers[h]|{'bytes':len(blobs[h]),'sha256':hashlib.sha256(blobs[h]).hexdigest()} for h in sorted(headers)}})
save('complete-owner-closures.json',allclosures)
save('dependency-effects-summary.json',effects)
print(json.dumps({'output':str(O),'unique_source_blobs':len(blobs),'SG1_changed_files':Sfiles,'MIG_changed_files':Mfiles,'effects':{k:{j:v for j,v in e.items() if j!='owner_upstream_path_table'} for k,e in effects.items()}},indent=2))

# Downstream candidate lists are dependency computations, not executions.
downstream={}
for label in ['records','SG1','MIG','prospective_disjoint_source_union','root_prospective_merge_tree']:
 g=graphs[label];rev=collections.defaultdict(set)
 for owner,imps in g.items():
  for i in imps:rev[i].add(owner)
 rows={}
 for target_label,targets in [('SG1',Smods),('MIG',Mmods),('both',Smods+Mmods)]:
  todo=list(targets);seen=set()
  while todo:
   m=todo.pop()
   if m in seen:continue
   seen.add(m);todo.extend(rev[m])
  seen.discard('TCSlib')
  assert all(any(m.startswith('TCSlib.'+root+'.') or m=='TCSlib.'+root for root in ['Complexity','BooleanAnalysis','Programs','ComputationalModels']) for m in seen)
  rows[target_label]={'count':len(seen),'modules':sorted(seen),'root_TCSlib_excluded':True}
 downstream[label]=rows
save('downstream-candidate-scopes.json',downstream)
# Attribute/source evidence is read as data at the immutable records pin.
inputs=[]
def frozen(path):
 b=git('show',pins['records']['commit']+':'+path)
 live=(R/path).read_bytes();assert live==b,path
 h=git('rev-parse',pins['records']['commit']+':'+path).decode().strip();git('cat-file','-e',h)
 inputs.append({'path':path,'git_blob':h,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'live_file_equals_records_blob':True})
 return b
P='campaign/gates/106-sg1-dedup/review/round4-compiled-and-seals/'
summary=json.loads(frozen(P+'metadata-summary.json'));mb=json.loads(frozen(P+'map-base.json'))['census'];mh=json.loads(frozen(P+'map-head.json'))['census']
sb=json.loads(frozen(P+'effective-simp-base.json'));sh=json.loads(frozen(P+'effective-simp-head.json'));assert sb==sh
probe=frozen(P+'Metadata-ciattrs.lean.txt').decode();ctx=json.loads(frozen(P+'context.json'))
source_freeze=json.loads(frozen('campaign/gates/106-sg1-dedup/review/round4-source-screen25/source-freeze.json'))
# Verify cited payloads against their frozen manifest without running the archived scripts.
manifest=json.loads(frozen(P+'MANIFEST.json'));listed={r['path']:r for r in manifest['files']}
for row in inputs:
 if not row['path'].startswith(P) or row['path']==P+'MANIFEST.json':continue
 r=listed[row['path'][len(P):]];assert r['sha256']==row['sha256'] and r['bytes']==row['bytes']
owner='TCSlib.Complexity.TuringMachine.Build.Contract.Basic'
basic_rules={n:{'owner':mb[n]['owner'],'rules':v} for n,v in sb.items() if mb[n]['owner']==owner}
assert len(basic_rules)==7
assert all(mh[n]['owner']==owner for n in basic_rules)
public_b={n:r for n,r in mb.items() if not r['private']};public_h={n:r for n,r in mh.items() if not r['private']}
assert len(public_b)==1351 and public_b.keys()==public_h.keys()
for n in public_b:
 assert {k:v for k,v in public_b[n].items() if k!='type_repr'}=={k:v for k,v in public_h[n].items() if k!='type_repr'}
 assert all(public_b[n]['type_repr'][k]==public_h[n]['type_repr'][k] for k in ['sha256','utf8_bytes'])
# Existing selected metadata owners keep exact old-to-current source closures before the other PR.
context_adoption={}
for old,new,owners,label in [('SG1_actual_full','SG1',ctx['owners'],'SG1_nine_metadata_owners'),('MIG_actual_full','MIG',Mmods,'MIG_twelve_changed_owners')]:
 rows=[]
 for m in owners:
  a,_=closure(graphs[old],m);b,_=closure(graphs[new],m);assert a==b
  changed=[n for n in sorted(a) if maps[old][path(n)]!=maps[new][path(n)]]
  assert not changed,(label,m,changed)
  rows.append({'owner':m,'closure_count':len(a),'all_source_blobs_and_edges_exact':True})
 context_adoption[label]=rows
basic_src=blobs[combined[path(owner)]].decode()
basic_snippet='\n'.join(f'{n+1}: {line}' for n,line in enumerate(basic_src.splitlines()) if 335<=n+1<=348)
(O/'Basic-simp-source-excerpt.txt').write_text(basic_snippet+'\n')
(O/'metadata-probe-scope-excerpt.txt').write_text('\n'.join(f'{n+1}: {l}'for n,l in enumerate(probe.splitlines()) if n<12 or 45<=n+1<=59 or 73<=n+1<=103)+'\n')
relevant=['TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean','TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean']
relevant_freezes=[]
for row in source_freeze['files']:
 if row['path'] in relevant:
  relevant_freezes.append({k:v for k,v in row.items() if k!='changed_proof_complete_headers'})
  assert row['terms_instances_data_attributes_identical'] and row['common_proof_headers_identical']
(O/'SG1-reached-files-source.diff.txt').write_bytes(git('diff','--no-ext-diff','--no-color','--unified=4',pins['records']['commit'],pins['SG1']['commit'],'--',*relevant))
import_deltas={}
for label,files in [('SG1',Sfiles),('MIG',Mfiles)]:
 rows=[]
 for p in files:
  a=headers[C[p]]['imports'];b=headers[maps[label][p]]['imports']
  rows.append({'path':p,'base_imports':a,'head_imports':b,'added_imports':[i for i in b if i not in a],'removed_imports':[i for i in a if i not in b]})
 import_deltas[label]=rows
# Direct source references to replaced private helpers are a bounded diagnostic only.
old_private=['counter_span_append','dgSpan_add','_private.TCSlib.Complexity.TuringMachine.Build.CounterLoop','_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape']
hits=[]
for p in Mfiles:
 text=blobs[M[p]].decode()
 for n,line in enumerate(text.splitlines(),1):
  if any(s in line for s in old_private):hits.append({'path':p,'line':n,'text':line})
attribute_evidence={'source_freeze_pin':{'base':source_freeze['base'],'head':source_freeze['head']},'metadata_pins':{'base':summary['base'],'head':summary['head']},'existing_joint_metadata_all_1351_nonprivate_names_type_payload_hashes_and_metadata_fields_equal':True,'archive_locator_fields_not_compared_as_type_payload':True,'existing_joint_metadata_168_owned_effective_rules_equal':sum(map(len,sb.values()))==168,'joint_probe_directly_imports_Basic_at_both_endpoints':('import '+owner) in probe,'not_a_per_MIG_owner_simp_environment_freeze':True,'Basic_unchanged_source_blob_at_records_SG1_MIG_and_combined':len({mp[path(owner)] for k,mp in maps.items() if k in ['records','SG1','MIG','prospective_disjoint_source_union']})==1,'Basic_recorded_effective_rules':basic_rules,'relevant_two_file_existing_source_freeze_rows':relevant_freezes,'bounded_MIG_twelve_source_private_helper_reference_search':{'needles':old_private,'hits':hits,'absence_is_not_semantic_dependency_proof':True},'actual_old_to_current_owner_context_adoption':context_adoption,'no_theorem_proof_value_equality_or_new_Lean_execution_claim':True}
save('attribute-and-source-evidence.json',attribute_evidence)
save('changed-file-import-deltas.json',import_deltas)
save('frozen-input-bindings.json',{'records':pins['records']['commit'],'frozen_payloads':inputs,'all_listed_metadata_payloads_match_prior_manifest':True,'archive_scripts_not_executed':True})
print('Actual root-created merge tree equals independent 1003-source union:',actual_tree)
print('Union downstream candidate scope:',downstream['root_prospective_merge_tree']['both']['count'])
