"""Source-only complete-header supplement and fresh unchanged canonical lint CLIs."""
from pathlib import Path
import ast,datetime,hashlib,json,re,subprocess,sys,time,types
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
OLD=ROOT/'campaign/fills/f6/landing/source-screen23'
C=json.loads((OUT/'capture.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(name,value):(OUT/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
def pure(path,name,env):
 t=path.read_text();n=next(x for x in ast.parse(t).body if isinstance(x,ast.FunctionDef) and x.name==name)
 code=ast.get_source_segment(t,n)+'\n';(OUT/'tools'/(name+'.py.txt')).write_text(code)
 exec(compile(ast.Module(body=[n],type_ignores=[]),str(path)+':pure-function','exec'),env)
 return env[name]
clean=pure(ROOT/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py','clean',{})
split=pure(ROOT/'campaign/fills/mig1/landing/review-final-source-final/source_review.py','split_header',{'P':types.SimpleNamespace(clean=clean),'re':re})
def norm(t):return ' '.join(clean(t).split())
def header(t):
 a,d,b=split(t)
 return norm(a)+(' '+d if d!='none' else '')
controls=[
 ('named_argument','theorem t (c : Cfg (input := x)) : c = c := by rfl','theorem t (c : Cfg (input := x)) : c = c :='),
 ('simple_type_let','theorem t : let arg := [true]; arg = arg := by rfl','theorem t : let arg := [true]; arg = arg :='),
 ('nested_type_let','theorem t : let a := let b := 0; b; a = a := by rfl','theorem t : let a := let b := 0; b; a = a :='),
 ('structure_where','structure Example where\n n : Nat','structure Example where'),
 ('proof_let_have_inline','theorem t :\n  let hp : 1 < 2 := by\n    have := Nat.zero_lt_one; omega\n  1 < 2 := by\n  exact hp','theorem t : let hp : 1 < 2 := by have := Nat.zero_lt_one; omega 1 < 2 :='),
 ('proof_let_have_nested','theorem t :\n  let hp : 1 < 2 := by\n    have h : 0 < 1 := by\n      have q := Nat.zero_lt_one\n      exact q\n    omega\n  let x := 2\n  x = x := by\n  rfl','theorem t : let hp : 1 < 2 := by have h : 0 < 1 := by have q := Nat.zero_lt_one exact q omega let x := 2 x = x :='),
 ('proof_letI','theorem t :\n  letI : Inhabited Nat := by\n    have x := 0\n    exact ⟨x⟩\n  True := by\n  trivial','theorem t : letI : Inhabited Nat := by have x := 0 exact ⟨x⟩ True :='),
 ('proof_let_same_line_have','theorem t :\n  let hp : True := by have h := True.intro; exact h\n  True := by\n  exact hp','theorem t : let hp : True := by have h := True.intro; exact h True :='),
 ('comments_and_nested_binders','/-- := by fake -/\ntheorem t (x : {n : Nat // n = n}) :\n  let hp : True := by\n    -- := fake\n    have h := True.intro\n    exact h\n  True := by\n  exact hp','theorem t (x : {n : Nat // n = n}) : let hp : True := by have h := True.intro exact h True :=')]
control_rows=[]
for name,src,expected in controls:
 actual=header(src);assert actual==expected,(name,actual,expected)
 control_rows.append(dict(name=name,source=src,expected=expected,actual=actual,passed=True))
save('complete-header-controls.json',control_rows)
freeze=(ROOT/'devtools/seyoon/declfreeze.py').read_text();(OUT/'tools/declfreeze.py.txt').write_text(freeze)
ns={};exec(compile(freeze.split('a = chunks(open(sys.argv[1]).read())')[0],'<canonical-declfreeze-helpers>','exec'),ns);ns['stmt']=header
oldinv=json.loads((OLD/'source-inventory-complete-headers.json').read_text())
files=[];inventory={};corrections=[];newchunks=[]
owner='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'
for path in C['population']:
 sources={s:(OUT/'inputs'/s/(path+'.txt')).read_text() for s in ['base','head']}
 chunks={s:list(ns['chunks'](src)) for s,src in sources.items()}
 rows={s:{n:dict(private=p,text=t,header=header(t)) for n,p,t in chunks[s]} for s in ['base','head']}
 assert all(len(rows[s])==len(chunks[s]) for s in ['base','head'])
 a,b=rows['base'],rows['head'];common=a.keys()&b.keys()
 assert all(a[n]['header']==b[n]['header'] and a[n]['private']==b[n]['private'] for n in common),path
 assert [n for n,p,t in chunks['base'] if not p]==[n for n,p,t in chunks['head'] if not p],path
 assert [n for n,p,t in chunks['base'] if n in common]==[n for n,p,t in chunks['head'] if n in common],path
 changed=[n for n in sorted(common) if norm(a[n]['text'])!=norm(b[n]['text'])]
 added=[n for n,p,t in chunks['head'] if n not in a];removed=sorted(a.keys()-b.keys());assert not removed
 if path==owner:assert changed==['Complexity.space_universal'] and len(added)==18 and all(b[n]['private'] for n in added)
 else:assert sources['base']==sources['head'] and not changed and not added
 for side in ['base','head']:
  prior={x['name']:x for x in oldinv[path][side]}
  for n,p,t in chunks[side]:
   if n in prior and prior[n]['header']!=rows[side][n]['header']:
    corrections.append(dict(path=path,side=side,name=n,old_truncated_or_different_header=prior[n]['header'],corrected_complete_header=rows[side][n]['header']))
  inventory.setdefault(path,{})[side]=[dict(name=n,private=p,header=rows[side][n]['header'],chunk_sha256=sha(t.encode()),normalized_code_sha256=sha(norm(t).encode())) for n,p,t in chunks[side]]
 terms={s:{n:norm(t) for n,p,t in chunks[s] if not re.search(r'\b(?:theorem|lemma)\b',rows[s][n]['header'])} for s in ['base','head']};assert terms['base']==terms['head']
 for pattern in [r'^\s*(?:@\[|attribute\b)',r'^\s*import\s']:
  assert [s for s in sources['base'].splitlines() if re.match(pattern,s)]==[s for s in sources['head'].splitlines() if re.match(pattern,s)]
 files.append(dict(path=path,base_source_declarations=len(a),head_source_declarations=len(b),all_common_complete_headers_visibility_and_relative_order_identical=True,public_order_names_identical=True,private_added=added,removed=removed,changed_common_code_chunks=changed,source_terms_imports_attributes_identical=True))
 if path==owner:
  for n in added+['Complexity.space_universal']:
   t=b[n]['text'];start=sources['head'][:sources['head'].index(t)].count('\n')+1
   newchunks.append(dict(name=n,start_line=start,end_line=start+len(t.splitlines())-1,complete_header=b[n]['header'],raw_text=t,code_sha256=sha(norm(t).encode())))
# Structures/equations gain an explicit delimiter in this inventory; the substantive by-let
# correction is enumerated separately and never substituted into the canonical screen.
prooflet=[x for x in corrections if x['name'] in ['Complexity.f6_hosted','Complexity.f6_scan','Complexity.f6_prefix']]
assert len(prooflet)==3 and all(x['side']=='head' and x['path']==owner for x in prooflet)
assert all(' := by have' in x['old_truncated_or_different_header'] or ' := by show ' in x['old_truncated_or_different_header'] for x in prooflet)
save('source-inventory-complete-headers.json',inventory);save('header-inventory-corrections.json',corrections);save('new19-full-chunks.json',newchunks)
save('source-preservation.json',dict(base=C['base'],head=C['head'],method='Canonical qualified declaration chunks, pure reviewed comment-preserving clean and balanced split_header, with indented proof-valued statement-let skip and nine targeted controls. Source-only; no Lean AST/generated census/macro claim.',all23_common_headers_and_public_names_visibility_order_preserved=True,only_existing_code_change='Complexity.space_universal',new_private_helpers=18,all23_source_terms_imports_attributes_preserved=True,proof_valued_new_header_corrections=prooflet,other_header_representation_corrections=len(corrections)-3,old_inventory_preserved_as_data=True,raw_screen_untouched=True,files=files))
results={s:{} for s in ['base','head']}
for label,toolname in [('style','scripts/style_lint.py'),('campaign','scripts/campaign_style_lint.py')]:
 tool=ROOT/toolname;data=tool.read_bytes();assert data==(OLD/'tools'/(tool.name+'.txt')).read_bytes()
 for pin in [C['base'],C['head']]:assert subprocess.run(['git','-C',str(ROOT),'show',pin+':'+toolname],check=True,stdout=subprocess.PIPE).stdout==data
 (OUT/'tools'/(tool.name+'.txt')).write_bytes(data)
 for side in ['base','head']:
  tree=Path(C['temporary_trees'][side]);cmd=['python3','-I',str(tool)]+(C['population'] if label=='style' else ['TCSlib','--check8b'])
  tick=time.time();start=datetime.datetime.now(datetime.timezone.utc).isoformat();q=subprocess.run(cmd,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  (OUT/(label+'-'+side+'.out')).write_bytes(q.stdout);(OUT/(label+'-'+side+'.stderr.out')).write_bytes(q.stderr)
  findings=[s for s in q.stdout.decode().splitlines() if s.strip()] if label=='style' else [s for s in q.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',s)]
  counts={'findings':len(findings)} if label=='style' else {k:sum(s.startswith(k) for s in findings) for k in ['FAIL','WARN','INFO']}
  if label=='style':assert f'{len(findings)} findings in 23 files' in q.stderr.decode()
  else:assert 'over 23 files' in q.stdout.decode()
  row=dict(command=cmd,cwd=str(tree),start_utc=start,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.time()-tick,exit=q.returncode,stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr),counts=counts,findings=findings)
  save(label+'-'+side+'-run.json',row);results[side][label]=row
normalize=lambda s:re.sub(r'\bline \d+\b','line <LINE>',re.sub(r'\b\d+ lines\b','<LINES> lines',re.sub(r':\d+:',':LINE:',s)))
delta={}
for label in ['style','campaign']:
 a={normalize(s) for s in results['base'][label]['findings']};b={normalize(s) for s in results['head'][label]['findings']};delta[label]=dict(normalized_new=sorted(b-a),normalized_gone=sorted(a-b))
save('lint-results.json',dict(method='Fresh unchanged canonical CLIs on complete23 captured source exports both sides; line-position/count normalization only.',sides=results,delta=delta))
print(json.dumps(dict(source_preservation='PASS',new_private=18,changed_existing=['Complexity.space_universal'],corrected_proof_valued_let_headers=[x['name'] for x in prooflet],other_header_representation_corrections=len(corrections)-3,controls=len(controls),lints={s:{k:r['counts'] for k,r in v.items()} for s,v in results.items()},delta=delta),indent=2))
