"""Final source-only freeze, complete new/target headers and full23 unmodified lints.
Whole common declaration chunks prove all frozen headers except the explicitly body-changed
target; only the18 new helpers and target require header/body splitting. This avoids claiming
that a lexical header guess is a Lean parser for all unaffected legacy syntax.
"""
from pathlib import Path
import ast,datetime,hashlib,json,re,subprocess,sys,time,types
sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=Path(sys.argv[1]).resolve();assert OUT.is_relative_to(ROOT/'campaign/fills/f6/landing/source-screen23-resumed')
OLD=ROOT/'campaign/fills/f6/landing/source-screen23'
C=json.loads((OUT/'capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def pure(path,name,env):
 t=path.read_text();n=next(x for x in ast.parse(t).body if isinstance(x,ast.FunctionDef) and x.name==name)
 code=ast.get_source_segment(t,n)+'\n';(OUT/'tools'/(name+'.py.txt')).write_text(code)
 exec(compile(ast.Module(body=[n],type_ignores=[]),str(path)+':pure-function','exec'),env);return env[name]
clean=pure(ROOT/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py','clean',{})
split=pure(ROOT/'campaign/fills/mig1/landing/review-final-source-final/source_review.py','split_header',{'P':types.SimpleNamespace(clean=clean),'re':re})
norm=lambda t:' '.join(clean(t).split())
def head(t):
 a,d,b=split(t);return norm(a)+(' :=' if d==':=' else '')
controls=[
 ('named_argument','theorem t (c : Cfg (input := x)) : c = c := by rfl','theorem t (c : Cfg (input := x)) : c = c :='),
 ('simple_type_let','theorem t : let arg := [true]; arg = arg := by rfl','theorem t : let arg := [true]; arg = arg :='),
 ('nested_type_let','theorem t : let a := let b := 0; b; a = a := by rfl','theorem t : let a := let b := 0; b; a = a :='),
 ('structure_where','structure Example where\n n : Nat','structure Example'),
 ('proof_let_have_inline','theorem t :\n  let hp : 1 < 2 := by\n    have := Nat.zero_lt_one; omega\n  1 < 2 := by\n  exact hp','theorem t : let hp : 1 < 2 := by have := Nat.zero_lt_one; omega 1 < 2 :='),
 ('proof_let_have_nested','theorem t :\n  let hp : 1 < 2 := by\n    have h : 0 < 1 := by\n      have q := Nat.zero_lt_one\n      exact q\n    omega\n  let x := 2\n  x = x := by\n  rfl','theorem t : let hp : 1 < 2 := by have h : 0 < 1 := by have q := Nat.zero_lt_one exact q omega let x := 2 x = x :='),
 ('proof_letI','theorem t :\n  letI : Inhabited Nat := by\n    have x := 0\n    exact ⟨x⟩\n  True := by\n  trivial','theorem t : letI : Inhabited Nat := by have x := 0 exact ⟨x⟩ True :='),
 ('proof_let_same_line_have','theorem t :\n  let hp : True := by have h := True.intro; exact h\n  True := by\n  exact hp','theorem t : let hp : True := by have h := True.intro; exact h True :='),
 ('comments_nested_binders','/-- := by fake -/\ntheorem t (x : {n : Nat // n = n}) :\n  let hp : True := by\n    -- := fake\n    have h := True.intro\n    exact h\n  True := by\n  exact hp','theorem t (x : {n : Nat // n = n}) : let hp : True := by have h := True.intro exact h True :=')]
control_rows=[]
for n,t,e in controls:
 actual=head(t);assert actual==e,(n,actual,e);control_rows.append(dict(name=n,source=t,expected=e,actual=actual,passed=True))
save('complete-header-controls.json',control_rows)
freeze=(ROOT/'devtools/seyoon/declfreeze.py').read_text();(OUT/'tools/declfreeze.py.txt').write_text(freeze)
ns={};exec(compile(freeze.split('a = chunks(open(sys.argv[1]).read())')[0],'<trusted-declfreeze-helpers>','exec'),ns)
files=[];inventory={};new19=[];target='Complexity.space_universal';owner='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'
for path in C['population']:
 sources={s:(OUT/'inputs'/s/(path+'.txt')).read_text() for s in ['base','head']};chunks={s:list(ns['chunks'](t)) for s,t in sources.items()};rows={s:{n:(p,t) for n,p,t in chunks[s]} for s in chunks}
 assert all(len(rows[s])==len(chunks[s]) for s in chunks)
 a,b=rows['base'],rows['head'];common=a.keys()&b.keys();added=[n for n,p,t in chunks['head'] if n not in a];removed=sorted(a.keys()-b.keys());assert not removed
 assert [(n,p) for n,p,t in chunks['base']]==[(n,p) for n,p,t in chunks['head'] if n in a]
 changed=[n for n in sorted(common) if norm(a[n][1])!=norm(b[n][1])]
 if path==owner:
  assert changed==[target] and len(added)==18 and all(b[n][0] and n.startswith('Complexity.f6_') for n in added)
  for name in added+[target]:
   raw=b[name][1];m=re.search(r'(?m)^(?:private\s+)?(?:theorem|lemma)\s+',raw);assert m;statement=raw[m.start():];header,delimiter,body=split(statement);assert delimiter==':=' and body
   start=sources['head'][:sources['head'].index(raw)].count('\n')+1
   assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|run_tac|elab|macro)\b',norm(body)),name
   if len(body.splitlines())>20:assert '**Proof sketch.**' in raw,name
   new19.append(dict(name=name,start_line=start,end_line=start+len(raw.splitlines())-1,private=b[name][0],raw_complete_header=header+delimiter,normalized_complete_header=head(statement),body_lines=len(body.splitlines()),raw_text=raw,chunk_sha256=sha(raw.encode())))
  ta=a[target][1];tb=b[target][1];ma=re.search(r'(?m)^theorem\s+',ta);mb=re.search(r'(?m)^theorem\s+',tb);ha,da,_=split(ta[ma.start():]);hb,db,_=split(tb[mb.start():]);assert da==db==':=' and ha==hb
  save('target-complete-header.json',dict(base_raw_header=ha+da,head_raw_header=hb+db,exact_raw_header_identical=True,sha256=sha((ha+da).encode())))
 else:assert sources['base']==sources['head'] and not changed and not added
 for pattern in [r'^\s*(?:@\[|attribute\b)',r'^\s*import\s']:
  assert [x for x in sources['base'].splitlines() if re.match(pattern,x)]==[x for x in sources['head'].splitlines() if re.match(pattern,x)]
 inventory[path]={s:[dict(name=n,private=p,raw_chunk_sha256=sha(t.encode()),normalized_code_sha256=sha(norm(t).encode())) for n,p,t in chunks[s]] for s in chunks}
 files.append(dict(path=path,base_declarations=len(a),head_declarations=len(b),all_common_code_chunks_identical_except_authorized_target=changed in [[],[target]],all_common_names_visibility_relative_order_identical=True,public_names_order_identical=True,private_added=added,removed=removed,changed_existing=changed,imports_attributes_identical=True))
assert len(new19)==19
save('source-inventory-complete-chunks.json',inventory);save('new19-complete-headers-and-chunks.json',new19)
oldinv=json.loads((OLD/'source-inventory-complete-headers.json').read_text());prior={x['name']:x for x in oldinv[owner]['head']};fixed=[]
for n in ['Complexity.f6_hosted','Complexity.f6_scan','Complexity.f6_prefix']:
 row=next(x for x in new19 if x['name']==n);assert prior[n]['header']!=row['normalized_complete_header'];fixed.append(dict(name=n,old_incomplete_header=prior[n]['header'],corrected_complete_header=row['normalized_complete_header']))
save('new-header-parser-supplement.json',dict(original_inventory=str((OLD/'source-inventory-complete-headers.json').relative_to(ROOT)),original_inventory_sha256=sha((OLD/'source-inventory-complete-headers.json').read_bytes()),original_data_unchanged=True,corrections=fixed,controls_passed=len(controls),scope='Only18 new helper headers and target split. Existing frozen headers follow from identical complete code chunks; target exact raw header checked separately. No general Lean parser or raw-screen extraction change is claimed.'))
save('source-preservation.json',dict(base=C['base'],head=C['head'],all23_source_freeze=True,existing_whole_code_chunks_unchanged_except_target=True,target_exact_complete_raw_header_identical=True,source_public_names_visibility_order_identical=True,new_private_helpers=18,only_existing_body_change=target,source_terms_imports_attributes_unchanged=True,new19_complete_header_checks=True,proof_valued_new_header_corrections=fixed,no_raw_screen_changes=True,files=files))
results={s:{} for s in ['base','head']}
for label,name in [('style','scripts/style_lint.py'),('campaign','scripts/campaign_style_lint.py')]:
 data=(ROOT/name).read_bytes();assert data==(OLD/'tools'/(Path(name).name+'.txt')).read_bytes()
 for pin in [C['base'],C['head']]:assert subprocess.run(['git','-C',str(ROOT),'show',pin+':'+name],stdout=subprocess.PIPE,check=True).stdout==data
 (OUT/'tools'/(Path(name).name+'.txt')).write_bytes(data)
 for side in ['base','head']:
  tree=Path(C['temporary_trees'][side]);tool=tree/name;tool.parent.mkdir(parents=True,exist_ok=True);tool.write_bytes(data)
  cmd=['python3','-I',str(tool)]+(C['population'] if label=='style' else ['TCSlib','--check8b']);tick=time.time();start=datetime.datetime.now(datetime.timezone.utc).isoformat();q=subprocess.run(cmd,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  (OUT/(label+'-'+side+'.out')).write_bytes(q.stdout);(OUT/(label+'-'+side+'.stderr.out')).write_bytes(q.stderr)
  findings=[x for x in q.stdout.decode().splitlines() if x.strip()] if label=='style' else [x for x in q.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',x)]
  counts={'findings':len(findings)} if label=='style' else {k:sum(x.startswith(k) for x in findings) for k in ['FAIL','WARN','INFO']}
  if label=='style':assert f'{len(findings)} findings in 23 files' in q.stderr.decode()
  else:assert 'over 23 files' in q.stdout.decode()
  row=dict(command=cmd,cwd=str(tree),start_utc=start,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.time()-tick,exit=q.returncode,stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr),counts=counts,findings=findings);save(label+'-'+side+'-run.json',row);results[side][label]=row
normalize=lambda s:re.sub(r'\bline \d+\b','line <LINE>',re.sub(r'\b\d+ lines\b','<LINES> lines',re.sub(r':\d+:',':LINE:',s)))
delta={}
for label in ['style','campaign']:
 a={normalize(x) for x in results['base'][label]['findings']};b={normalize(x) for x in results['head'][label]['findings']};delta[label]=dict(normalized_new=sorted(b-a),normalized_gone=sorted(a-b))
save('lint-results.json',dict(method='Fresh unmodified canonical CLIs on complete23 captured exports, bothBASEandHEAD; only diagnostic source line positions/counts normalized.',sides=results,delta=delta))
print(json.dumps(dict(source_freeze='PASS',new_private_helpers=18,changed_existing=[target],new19_headers='PASS',proof_valued_let_controls=len(controls),lints={s:{k:r['counts'] for k,r in v.items()} for s,v in results.items()},delta=delta),indent=2))
