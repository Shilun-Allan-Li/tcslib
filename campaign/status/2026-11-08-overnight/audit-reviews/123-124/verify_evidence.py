from pathlib import Path
import json,re,hashlib,subprocess,collections
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');H=lambda b:hashlib.sha256(b).hexdigest();owner='TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean';base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);anchor=json.loads((R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text());results=[]
for gate,slug,folder in [(123,'ch7-run','ch7-full-five-scopes-v2'),(124,'safe-run','exact-adopted-private-bridge-preflight')]:
 pref=f'campaign/gates/{gate}-{slug}/review/';P=R/pref;S={r['path']:r for r in json.loads((O/str(gate)/'SECTION-BINDINGS.json').read_text())};used={}
 def read(rel):
  path=pref+rel;b=(P/rel).read_bytes();assert path in S and H(b)==S[path]['sha256'] and len(b)==S[path]['bytes'];used[rel]={'bytes':len(b),'sha256':H(b)};return b
 def J(rel):return json.loads(read(rel))
 pub=json.loads((O/str(gate)/'publication.json').read_text());head=pub['source'];result=J('replay/RESULT.json');req=J('replay/request.json');assert result['pass'] and result['head']==head and result['modules']==80 and result['failed']==0 and result['static_exit']==0 and req['snapshot_lean_commit']==base;mods=read('replay/down.txt').decode().splitlines();rows=J('replay/module-results.json');assert len(mods)==80 and mods==[r['module'] for r in rows];source=J('replay/source-before.json');assert len(source)==1003;srcidx=J('replay/compiled-source-index.json');srcidx=srcidx['files'] if isinstance(srcidx,dict) else srcidx;assert len(srcidx)==80;idx={r['path']:r for r in srcidx};warn=[]
 # Batch-read every source Git blob at the issued head without touching any Git state.
 bt=g('ls-tree','-r','-z',head);tree={}
 for row in bt.split(b'\0'):
  if row:
   a,p=row.split(b'\t',1);parts=a.split()
   if parts[1]==b'blob':tree[p.decode()]=parts[2].decode()
 ids=list(dict.fromkeys(tree[p] for p in source));out=subprocess.check_output(['git','--no-optional-locks','-C',str(R),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode());blob={};at=0
 for oid in ids:
  end=out.index(b'\n',at);h=out[at:end].split();assert h[0].decode()==oid and h[1]==b'blob';n=int(h[2]);at=end+1;blob[oid]=out[at:at+n];at+=n+1
 for p,d in source.items():assert d['git_blob']==tree[p] and d['sha256']==H(blob[tree[p]]) and d['bytes']==len(blob[tree[p]])
 for r in rows:
  log=read('replay/logs/'+r['module']+'.log');assert r['pass'] and r['exit']==0 and r['errors']==0 and r['fresh_output'] and H(log)==r['log_sha256'] and log.count(b"declaration uses 'sorry'")==r['sorry'];p=r['module']+'.lean';d=idx[p];cap=d['capture'];cap=cap[len('replay/'):] if cap.startswith('replay/') else cap;cap='replay/'+cap;src=read(cap);assert src==blob[tree[p]] and d['git_blob']==tree[p] and d['sha256']==H(src)
  if r['sorry']:
   assert src==g('show',base+':'+p);warn.append({'module':r['module'],'count':r['sorry'],'BASE_HEAD_source_bytes_exact':True})
 before=J('replay/input-before.json');after=J('replay/input-after.json');output=J('replay/output.json');assert before==after==anchor and len(before)==len(output)==895 and set(before)==set(output);changed=[p for p in output if output[p]!=before[p]];assert changed==[owner[:-5]+'.olean'];assert sum(r['sorry'] for r in rows)==31;static=read('replay/static.txt').decode();assert re.search(r'modules 80, mismatches 0, static total 31',static)
 meta={};metarows=[]
 for side in ['BASE','HEAD']:
  selected=J('metadata/'+side+'-selected.json');raw=read('metadata/'+side+'.log');run=J('metadata/'+side+'-run.json');request=J('metadata/'+side+'-request.json');actual=[json.loads(l.split('ABI|',1)[1]) for l in raw.decode().splitlines() if l.startswith('ABI|')];assert actual==selected['roots'];assert run['exit']==0 and run['errors']==0 and H(raw)==run['raw_sha256'] and len(raw)==run['raw_bytes'];assert request['complete_snapshot_owner_object_before_sha256']==(before if side=='BASE' else output)[owner[:-5]+'.olean'];meta[side]=selected['roots']
  for d in actual:assert d['axioms']==['propext','Quot.sound'] and d['full_type_Expr_repr'] and '...' not in d['full_type_Expr_repr'];assert not d['simp_lemma'] and not d['simp_unfold']
  metarows.append({'side':side,'raw_log_sha256':H(raw),'records':len(actual),'exit':run['exit'],'object_bound':True})
 bm={d['source_name']:d for d in meta['BASE']};hm={d['source_name']:d for d in meta['HEAD']};assert all(bm[n]==hm[n] for n in bm)
 if gate==123:assert len(bm)==len(hm)==5 and read('metadata/BASE.log')==read('metadata/HEAD.log')
 else:
  assert len(bm)==3 and len(hm)==4;new=[d for n,d in hm.items() if n not in bm];assert len(new)==1 and new[0]['private'] and not new[0]['simp_lemma'] and not new[0]['simp_unfold']
 Q='inputs/'+folder+'/';guarddata=J(Q+('SOURCE.json' if gate==123 else 'guard-context.json'));guards=guarddata['guards'];assert len(guards)==(6 if gate==123 else 7);nat_name='ScopeNative' if gate==123 else 'ScopeGuardNative';nat=read(Q+nat_name+'.lean.txt').decode();sea=read(Q+'ScopeSealed.lean.txt').decode();norm=lambda s:[l for l in s.splitlines() if l.strip() and not l.startswith('attribute [local irreducible]')];assert norm(nat)==norm(sea) and 'attribute [-simp] Turing.Action.apply' in nat and 'attribute [-simp] Turing.Action.apply' in sea
 if gate==123:chunks=guarddata['complete_literal_chunks'];scope_runs=J(Q+'RESULTS.json')
 else:
  binding=J('literal-source-and-scope-binding.json');chunks={d['name']:d['HEAD_chunk'] for d in binding['complete_three_chunks']};chunks['Turing.safeRun_iff_segment']=read(Q+'private-bridge.lean.txt').decode().rstrip();scope_runs=[J(Q+name+'-attempt1.json') for name in ['ScopeGuardNative','ScopeSealed']]
 ownertext=(O/str(gate)/'OWNER-HEAD.lean.txt').read_text();guardline=next(l for l in sea.splitlines() if l.startswith('attribute [local irreducible]'));assert set(guardline.split()[3:])==set(guards)
 for name,chunk in chunks.items():assert ownertext.count(chunk)==nat.count(chunk)==sea.count(chunk)==1;assert sea.index(chunk)>sea.index(guardline)
 controls={}
 for side in ['Native','Sealed']:
  src=read(Q+'Controls'+side+'.lean.txt').decode();logname='Controls'+side+('.log' if gate==123 else '-attempt1.log');raw=read(Q+logname);lines=re.findall(r'^CONTROL\|([^|\n]+)\|([^|\n]+)\|(PASS|FAIL)(?:\|kernelChecked=([^\n]+))?',raw.decode(),re.M);expect=len(guards)*2;assert len(lines)==expect;assert {(n,m) for n,m,_,_ in lines}=={(n,m) for n in guards for m in ['point','abstract']};assert all(status==('PASS' if side=='Native' else 'FAIL') for _,_,status,_ in lines)
  if side=='Native':assert all(k for _,_,_,k in lines) and len({k for _,_,_,k in lines})==expect and b'error:' not in raw
  else:assert raw.count(b'error:')==expect and raw.count(b'RFL_CONTROL|')==expect
  controls[side]={'identities':len(lines),'log_sha256':H(raw),'kernel_checked':side=='Native','expected_rfl_failure':side=='Sealed'}
 for name in [nat_name,'ScopeSealed']:
  raw=read(Q+name+('.log' if gate==123 else '-attempt1.log'));assert b'error:' not in raw and b"sorryAx" not in raw
  if gate==123:r=next(x for x in scope_runs if x['name']==name);assert r['exit']==0 and r['errors']==0 and H(raw)==r['log_sha256'] and H(read(Q+name+'.lean.txt'))==r['input_sha256']
  else:r=next(x for x in scope_runs if x['name']==name+'.lean');assert r['exit']==0 and r['errors']==0 and H(raw)==r['raw_sha256'] and H(read(Q+name+'.lean.txt'))==r['source_sha256']
 # Parse complete supplied screens only; do not run extraction/LCS or another screen.
 pop=read('screen-population.txt').decode().splitlines();assert len(pop)==33 and len(set(pop))==33;source_diff=[]
 for path in pop:
  a=read('source/BASE/'+path+'.txt');b=read('source/HEAD/'+path+'.txt');assert a==g('show',base+':'+path) and b==blob[tree[path]]
  if a!=b:source_diff.append(path)
 assert source_diff==[owner]
 parsed={};screen_rows=[]
 for side,rel,resrel in [('BASE','screen/BASE/screen-BASE.txt','screen/BASE/RESULT.json'),('HEAD','screen/HEAD.txt','screen/HEAD-RESULT.json')]:
  raw=read(rel);rr=J(resrel);digest=rr.get('sha256',rr.get('raw_sha256'));assert rr['exit']==0 and H(raw)==digest and len(raw)==rr['bytes'];text=raw.decode();m=re.match(r'declarations screened: (\d+); copy pairs .*: (\d+); reproduced text: ([\d,]+) chars',text);assert m;ps={}
  for l in text.splitlines()[1:]:
   if not l.strip():continue
   q=re.fullmatch(r'\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%',l);assert q,l;key=(q.group(1),q.group(2));assert key not in ps;ps[key]=tuple(map(int,q.groups()[2:]))
  assert len(ps)==int(m.group(2));parsed[side]=ps;screen_rows.append({'side':side,'filtered_bodies':int(m.group(1)),'pairs':len(ps),'reproduced_chars':int(m.group(3).replace(',','')),'sha256':digest})
 B=parsed['BASE'];T=parsed['HEAD'];new=[k for k in T if k not in B];gone=[k for k in B if k not in T];changed_scores=[k for k in T if k in B and T[k]!=B[k]];assert len(new)==0 and len(gone)==(2 if gate==123 else 0)
 # Lint is verified as recorded bytes, without a new linter execution.
 stylebase=read('qa/BASE-style-lint.txt');stylehead=read('qa/HEAD-style-lint.txt');assert stylebase==stylehead and re.search(rb'0 (?:issues|errors|findings|violation)',stylebase) is not None
 ca=read('qa/BASE-campaign-lint.txt').decode();cb=read('qa/HEAD-campaign-lint.txt').decode();linea=[l for l in ca.splitlines() if 'INFO' in l and owner in l];lineb=[l for l in cb.splitlines() if 'INFO' in l and owner in l];assert len(linea)==len(lineb)==1
 # Normalize actual export root paths only, then the one owner INFO row.
 clean=lambda s:re.sub(r'/private/tmp/[^\s]+/(?:BASE|HEAD)/','<TREE>/',s)
 aa=clean(ca).replace(clean(linea[0]),'<OWNER-INFO>');bb=clean(cb).replace(clean(lineb[0]),'<OWNER-INFO>');campaign_other_equal=aa==bb
 receipt={'gate':gate,'replay':{'PASS_modules':80,'errors':0,'inherited_admissions':31,'warning_modules':warn,'all80_logs_and_source_captures_exact':True,'all1003_source_blobs_exact':True,'input895_equals_MAC8_anchor_and_after':True,'only_owner_output_object_changed':True,'outside80_closure_objects_unchanged':815,'static_record_matches':[80,0,31]},'metadata':{'runs':metarows,'public_all_recorded_fields_exact':True,'new_private_non_simp':gate==124,'scope':'selected5 or selected3+newprivate1; no proof-value/global ABI/simp equality'},'guards':{'ordinary_names':guards,'complete_scope_count':len(chunks),'all_chunks_exact_HEAD_and_within_guard':True,'source_modes_differ_only_guard_and_blank_lines':True,'Action_apply_definition_simp_removed_both':True,'controls':controls,'no_new_Lean_execution_by_this_review':True},'screen':{'population':33,'all66_sources_exact_to_Git_endpoints':True,'rows':screen_rows,'new':new,'gone':gone,'persistent_score_changed':changed_scores,'no_screen_or_pair_recompute_by_this_review':True},'lint':{'style_recorded_zero_findings_equal':True,'BASE_owner_INFO':linea,'HEAD_owner_INFO':lineb,'campaign_other_rows_after_export_root_normalization_equal':campaign_other_equal,'no_new_linter_run_by_this_review':True},'all_used_files_authenticate_to_issued_bundle':used};(O/str(gate)/'EVIDENCE-VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');results.append(receipt);print(json.dumps({k:receipt[k] for k in ['gate','replay','metadata','guards','screen','lint']}),flush=True)
