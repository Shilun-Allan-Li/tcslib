from pathlib import Path
import ast,datetime,hashlib,json,re,subprocess,sys,time,types
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent;ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=ROOT/'campaign/gates/106-sg1-dedup';OLD=G/'review/round3-current-source-screen25-final79';C=json.loads((OUT/'capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def pure(path,name,env):
 t=path.read_text();n=next(x for x in ast.parse(t).body if isinstance(x,ast.FunctionDef) and x.name==name);code=ast.get_source_segment(t,n)+'\n';(OUT/'tools'/(name+'.py.txt')).write_text(code);exec(compile(ast.Module(body=[n],type_ignores=[]),str(path)+':pure-function','exec'),env);return env[name]
clean=pure(ROOT/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py','clean',{})
# Proof-only delimiter: named binders and result-local lets are balanced. Do not treat a
# leading absolute-value bar as an equation clause. Unchanged complete chunks need no split.
def split_proof(raw):
 c=clean(raw);stack=[];quoted=False;i=0;pending=0
 while i<len(c):
  ch=c[i]
  if quoted:
   if ch=='\\':i+=2;continue
   if ch=='"':quoted=False
  elif ch=='"':quoted=True
  elif ch in '([{⟨':stack.append(ch)
  elif ch in ')]}⟩':
   assert stack;stack.pop()
  elif not stack:
   if re.match(r'(?:let|letI|have)\b',c[i:]) and (i==0 or not(c[i-1].isalnum() or c[i-1]=='_')):pending+=1
   if c.startswith(':=',i):
    if pending:
     pending-=1;tail=c[i+2:];m=re.match(r'\s*by\b[^\n]*\n',tail)
     if m:
      start=c.rfind('\n',0,i)+1;indent=len(c[start:i])-len(c[start:i].lstrip());j=i+2+m.end()
      while j<len(c):
       e=c.find('\n',j);e=len(c) if e<0 else e+1;line=c[j:e]
       if line.strip() and len(line)-len(line.lstrip())<=indent:break
       j=e
      i=j;continue
     i+=2;continue
    return raw[:i].rstrip(),':=',raw[i+2:].strip()
  i+=1
 return raw.rstrip(),'none',''
def proof_statement(raw):
 m=re.search(r'(?m)^(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:lemma|theorem)\s+',clean(raw));assert m;return raw[m.start():]
norm=lambda t:' '.join(clean(t).split())
controls=[('theorem t (c : Cfg (input := x)) : c = c := by rfl','c = c'),('theorem t : let x := 0; x=x := by rfl','x=x'),('theorem t : let a := let b := 0; b; a=a := by rfl','a=a'),('theorem t :\n  let hp : True := by\n    have := True.intro\n    assumption\n  True := by\n  exact hp','True'),('theorem t :\n  let hp : True := by\n    have h : True := by\n      have q := True.intro\n      exact q\n    exact h\n  True := by\n  exact hp','True'),('theorem t :\n  letI : Inhabited Nat := by\n    have x := 0\n    exact ⟨x⟩\n  True := by\n  trivial','True'),('theorem t :\n  let hp : True := by have h := True.intro; exact h\n  True := by\n  exact hp','True'),('/-- := false -/\ntheorem t : True := by trivial','True'),('theorem t : ∀ x : ℤ,\n  |x| ≤ |x| := by intro x; exact le_rfl','|x| ≤ |x|'),('theorem t (h : P (x := y)) :\n  let a := 0\n  ∀ x : ℤ, |x| ≤ |x| := by intros; exact le_rfl','∀ x : ℤ, |x| ≤ |x|')]
control_rows=[]
for src,last in controls:
 h,d,b=split_proof(src);assert d==':=' and norm(h).endswith(norm(last));control_rows.append(dict(source=src,header=h+':=',body=b,pass_=True))
save('proof-header-controls.json',control_rows)
freeze=(ROOT/'devtools/seyoon/declfreeze.py').read_text();(OUT/'tools/declfreeze.py.txt').write_text(freeze);f={};exec(compile(freeze.split('a = chunks(open(sys.argv[1]).read())')[0],'<canonical-source-chunks>','exec'),f)
prior_freeze={x['path']:x for x in json.loads((OLD/'source-freeze-complete-headers.json').read_text())['files']};inventory={};reports=[];changed_headers=[];F4=[];original_imports=[]
f4map={'TCSlib/Complexity/ClassNP/SAT.lean':'Complexity.sat_live_prefix','TCSlib/Complexity/CookLevin/Hardness.lean':'Complexity.clA5_live_prefix'}
known17={'Complexity.sat_pt_pair_input','Complexity.sat_pt_mapSnd','Complexity.sat_pt_pair','Complexity.sat_pt_append','Complexity.sat_pt_unaryLength','Complexity.clNative_linear','Complexity.clNative_map','Complexity.clNative_pair','Complexity.clNative_append','Complexity.clNative_unary','Complexity.clA5_pt_const','Complexity.clA5_pt_cond','Complexity.clA5_pt_and','Complexity.clA5Pair_sizes','Complexity.clA5Le_native','Complexity.clA5Drop_native','Complexity.taut_comp_on_image'};verified17=[]
for path in C['population']:
 src={s:(OUT/'inputs'/s/(path+'.txt')).read_text() for s in ['base','head']};chunks={s:list(f['chunks'](t)) for s,t in src.items()};rows={s:{n:(p,t) for n,p,t in v} for s,v in chunks.items()};assert all(len(rows[s])==len(chunks[s]) for s in rows)
 a,b=rows['base'],rows['head'];common=a.keys()&b.keys();assert all(a[n][0]==b[n][0] for n in common);assert [n for n,p,t in chunks['base'] if not p]==[n for n,p,t in chunks['head'] if not p];assert [n for n,p,t in chunks['base'] if n in common]==[n for n,p,t in chunks['head'] if n in common]
 added=[n for n,p,t in chunks['head'] if n not in a];removed=[n for n,p,t in chunks['base'] if n not in b];assert all(b[n][0] for n in added) and all(a[n][0] for n in removed);assert sorted(added)==prior_freeze[path]['private_added'] and sorted(removed)==prior_freeze[path]['private_removed']
 changed=[n for n in sorted(common) if norm(a[n][1])!=norm(b[n][1])];headers=[]
 for n in changed:
  ah,ad,_=split_proof(proof_statement(a[n][1]));bh,bd,_=split_proof(proof_statement(b[n][1]));assert ad==bd==':=' and ah==bh,(path,n,'header changed');headers.append(dict(name=n,raw_complete_header=ah+ad,header_sha256=sha((ah+ad).encode())))
 attrs={s:[x for x in src[s].splitlines() if re.match(r'^\s*(?:@\[|attribute\b)',x)] for s in src};assert attrs['base']==attrs['head']
 def proof(t):return bool(re.search(r'(?m)^(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma)\s+',clean(t)))
 terms={s:{n:norm(t) for n,p,t in chunks[s] if not proof(t)} for s in rows};assert terms['base']==terms['head'],path
 oldsrc={s:(OLD/'inputs'/s/(path+'.txt')).read_text() for s in ['base','head']};oldrows={s:{n:(p,t) for n,p,t in f['chunks'](oldsrc[s])} for s in oldsrc}
 if path in C['changed_files']:
  assert src['base']==oldsrc['base'];prior_to_current=[n for n in b if n in oldrows['head'] and b[n][1]!=oldrows['head'][n][1]];assert set(b)==set(oldrows['head'])
  expected=[f4map[path]] if path in f4map else [];assert prior_to_current==expected,(path,prior_to_current)
  recovered=src['head']
  for n in expected:
   before=oldrows['head'][n][1];after=b[n][1];h,d,body=split_proof(proof_statement(before));nh,nd,nb=split_proof(proof_statement(after));assert h==nh and d==nd==':=';assert norm(nb)=='by exact Turing.MultiTapeTM.runFrom_state_ne_none_of_le tm c t ht';assert recovered.count(after)==1;recovered=recovered.replace(after,before);F4.append(dict(path=path,name=n,header=h+d,header_sha256=sha((h+d).encode()),old_chunk=before,new_chunk=after,exact_public_forwarder=True,only_body_and_doc_change=True))
  assert recovered==oldsrc['head']
  for n in known17&b.keys():assert b[n][1]==oldrows['head'][n][1];verified17.append(n)
 else:assert src['base']==src['head'],path
 imports={s:[x for x in src[s].splitlines() if re.match(r'^\s*import\s',x)] for s in src};oldimports={s:[x for x in oldsrc[s].splitlines() if re.match(r'^\s*import\s',x)] for s in oldsrc};newplus=sorted(set(imports['head'])-set(imports['base']));newminus=sorted(set(imports['base'])-set(imports['head']));assert (newplus,newminus)==(sorted(set(oldimports['head'])-set(oldimports['base'])),sorted(set(oldimports['base'])-set(oldimports['head'])));original_imports.append(dict(path=path,carried_R3_added_imports=newplus,removed_imports=newminus,new_R4_imports=[]))
 inventory[path]={s:[dict(name=n,private=p,chunk_sha256=sha(t.encode()),normalized_code_sha256=sha(norm(t).encode())) for n,p,t in chunks[s]] for s in rows};reports.append(dict(path=path,base_source_declarations=len(a),head_source_declarations=len(b),base_public=sum(not p for p,t in a.values()),head_public=sum(not p for p,t in b.values()),base_private=sum(p for p,t in a.values()),head_private=sum(p for p,t in b.values()),public_names_privacy_order_identical=True,common_proof_headers_identical=True,changed_common_code_chunks=changed,changed_proof_complete_headers=headers,private_added=added,private_removed=removed,terms_instances_data_attributes_identical=True))
assert set(verified17)==known17 and len(F4)==2
save('source-inventory-complete-chunks.json',inventory);save('source-freeze.json',dict(base=C['base'],head=C['head'],all25_source_checks_pass=True,public_names_visibility_order_and_all_common_headers_preserved=True,all_terms_instances_data_attributes_identical=True,private_bridge_replacements_same_as_R3=True,original17_round3_repair_chunks_byte_identical=True,original17_names=sorted(known17),F4_private_bodies_docs_only=True,proof_specific_header_controls=len(controls),header_method='Changed proof headers split by binder/result-let balancing and indented by-value skipping; absolute bars never terminate a proof header. Unchanged complete code chunks establish every other header. Source-only, no general Lean AST/compiled census claim.',files=reports));save('F4-source-lineage.json',dict(previous=C['previous_head'],head=C['head'],exact_reverse_replacement_recovers_entire_prior_PR_files=True,repairs=F4));save('imports-carried-from-round3.json',original_imports)
results={s:{} for s in ['base','head']}
for label,name in [('style','scripts/style_lint.py'),('campaign','scripts/campaign_style_lint.py')]:
 data=(ROOT/name).read_bytes()
 for pin in [C['base'],C['head']]:assert subprocess.run(['git','-C',str(ROOT),'show',pin+':'+name],check=True,stdout=subprocess.PIPE).stdout==data
 (OUT/'tools'/(Path(name).name+'.txt')).write_bytes(data)
 for side in results:
  tree=Path(C['temporary_trees'][side]);tool=tree/name;tool.parent.mkdir(parents=True,exist_ok=True);tool.write_bytes(data);cmd=['python3','-I',str(tool)]+(C['population'] if label=='style' else ['TCSlib','--check8b']);tick=time.time();start=datetime.datetime.now(datetime.timezone.utc).isoformat();q=subprocess.run(cmd,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(OUT/(label+'-'+side+'.out')).write_bytes(q.stdout);(OUT/(label+'-'+side+'.stderr.out')).write_bytes(q.stderr);findings=[x for x in q.stdout.decode().splitlines() if x.strip()] if label=='style' else [x for x in q.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',x)];counts={'findings':len(findings)} if label=='style' else {k:sum(x.startswith(k) for x in findings) for k in ['FAIL','WARN','INFO']}
  if label=='style':assert f'{len(findings)} findings in 25 files' in q.stderr.decode()
  else:assert 'over 25 files' in q.stdout.decode()
  row=dict(command=cmd,cwd=str(tree),start_utc=start,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.time()-tick,exit=q.returncode,stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr),counts=counts,findings=findings);save(label+'-'+side+'-run.json',row);results[side][label]=row
normalize=lambda s:re.sub(r'\bline \d+\b','line <LINE>',re.sub(r'\b\d+ lines\b','<LINES> lines',re.sub(r':\d+:',':LINE:',s)));delta={}
for label in ['style','campaign']:
 a={normalize(x) for x in results['base'][label]['findings']};b={normalize(x) for x in results['head'][label]['findings']};delta[label]=dict(normalized_new=sorted(b-a),normalized_gone=sorted(a-b))
save('lint-results.json',dict(fresh_full25_unmodified_CLIs=True,sides=results,delta=delta));print(json.dumps(dict(source_freeze='PASS',F4_private_forwarders=[x['name'] for x in F4],other17_byte_identical=True,header_controls=len(controls),lints={s:{k:r['counts'] for k,r in v.items()} for s,v in results.items()},delta=delta),indent=2))
