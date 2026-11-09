from pathlib import Path
import json,re,hashlib,subprocess,collections
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G='campaign/gates/122-first-halt-reuse/review';P=R/G;H=lambda b:hashlib.sha256(b).hexdigest();g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';head='f3c8c050ef98375bc237c72bde74f83d33833374';e0b='e0b7fd50ca81d9b8f3dd486f120292da1b4fb880';bind={r['path']:r for r in json.loads((O/'LOGICAL-PAYLOAD-BINDINGS.json').read_text())};used={}
def read(rel):
 b=(P/rel).read_bytes();r=bind[rel];assert H(b)==r['sha256'] and len(b)==r['bytes'];used[rel]={'bytes':len(b),'sha256':H(b)};return b
def J(rel):return json.loads(read(rel))
def blobmap(rev,paths):
 tree={}
 for row in g('ls-tree','-r','-z',rev).split(b'\0'):
  if row:
   a,p=row.split(b'\t',1);parts=a.split()
   if parts[1]==b'blob':tree[p.decode()]=parts[2].decode()
 ids=list(dict.fromkeys(tree[p] for p in paths));raw=subprocess.check_output(['git','--no-optional-locks','-C',str(R),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode());out={};at=0
 for oid in ids:
  end=raw.index(b'\n',at);parts=raw[at:end].split();assert parts[0].decode()==oid;size=int(parts[2]);at=end+1;out[oid]=raw[at:at+size];at+=size+1
 assert at==len(raw);return tree,out
anchor=J('inputs/historical-fh10-e0b/anchors/MAC8/object-hashes.json');replays=[];prev=None
for rel,rev,count in [('inputs/historical-fh10-e0b/replay',e0b,222),('replay-current153',head,153)]:
 result=J(rel+'/RESULT.json');request=J(rel+'/request.json');assert result['pass'] and result['head']==rev and result['modules']==count and result['failed']==0 and result['static_exit']==0;mods=read(rel+'/down.txt').decode().splitlines();rows=J(rel+'/module-results.json');assert len(mods)==count and mods==[r['module'] for r in rows];source=J(rel+'/source-before.json');assert len(source)==1003;tm,bm=blobmap(rev,source)
 for p,d in source.items():assert d['git_blob']==tm[p] and d['sha256']==H(bm[tm[p]]) and d['bytes']==len(bm[tm[p]])
 index=J(rel+('/compiled-source-index.json' if count==222 else '/COMPILED-SOURCE-MAP153.json'));assert len(index)==count;ix={r['module']:r for r in index};warnings=[]
 for r in rows:
  log=read(rel+'/logs/'+r['module']+'.log');assert r['pass'] and r['exit']==0 and r['errors']==0 and r['fresh_output'] and H(log)==r['log_sha256'];assert log.count(b"declaration uses 'sorry'")==r['sorry'];d=ix[r['module']];p=r['module']+'.lean';cap=read(rel+'/compiled-source/'+p+'.txt');assert cap==bm[tm[p]];assert d.get('git_blob',d.get('source_blob'))==tm[p];assert d.get('sha256',d.get('source_sha256'))==H(cap)
  if r['sorry']:assert cap==g('show',base+':'+p);warnings.append({'module':r['module'],'count':r['sorry'],'source_BASE_exact':True})
 assert sum(r['sorry'] for r in rows)==31;assert sorted(x['count'] for x in warnings)==[2,8,21];assert re.search(r'modules '+str(count)+r', mismatches 0, static total 31',read(rel+'/static.txt').decode())
 before=J(rel+'/input-before.json');after=J(rel+'/input-after.json');output=J(rel+'/output.json');assert before==after==(anchor if prev is None else prev) and len(output)==len(before)==895 and set(output)==set(before);changed=sorted(p for p in output if output[p]!=before[p]);assert len(changed)==(8 if count==222 else 2);outside=[p for p in output if p not in {m+'.olean' for m in mods}];assert len(outside)==895-count and all(output[p]==before[p] for p in outside)
 if count==153:assert changed==['TCSlib/Complexity/TuringMachine/Universal.olean','TCSlib/Complexity/TuringMachine/UniversalStartup.olean'];assert request['snapshot_lean_commit']==e0b and request['whole_clone']=='cp -cR';assert not g('diff','--name-only',request['prospective_tree'],head,'--','*.lean');assert not g('diff','--name-only',base,request['records'],'--','*.lean')
 replays.append({'source':rev,'modules':count,'all_logs_source_captures_and_1003_Git_blob_inventory_exact':True,'warnings':warnings,'static_supplied_record':[count,0,31],'input895_unchanged_and_complete_predecessor_exact':True,'output895_changed':changed,'outside_closure_identical':len(outside),'request_whole_clone':request.get('whole_clone','see complete preserved driver/request')});prev=output
B='inputs/blive305/';selected=J(B+'SELECTED13-TYPES-AX-BOUNDS.json');assert len(selected)==13;freshbase=J(B+'BASE-FOOTPRINTS5.json');freshhead=J(B+'CANDIDATE-FOOTPRINTS5.json');oldbase=J(B+'prior-evidence/BASE-SELECTED10.json');oldhead=J(B+'prior-evidence/HEAD-FOOTPRINTS10.json');fb={r['root']:r for r in freshbase};fh={r['root']:r for r in freshhead};ob={r['root']:r for r in oldbase};oh={r['root']:r for r in oldhead};allheads=set();metadata=[]
for r in selected:
 root=r['root'];fresh=r['id'] in ['BLIVE1','BLIVE2','BLIVE3',85,86];a=(fb if fresh else ob)[root];b=(fh if fresh else oh)[root];at=a['root_type_Expr'] if fresh else a['type_Expr'];al=a['root_levelParams'] if fresh else a['universe_params'];ax=a['root_axioms'] if fresh else a['axioms'];assert at==b['root_type_Expr']==r['BASE_type_Expr']==r['candidate_type_Expr'];assert al==b['root_levelParams']==r['BASE_universe_params']==r['candidate_universe_params'];assert sorted(ax)==sorted(b['root_axioms'])==sorted(r['BASE_axioms'])==sorted(r['candidate_axioms']);assert set(ax)<={'propext','Classical.choice','Quot.sound'};assert at and '...' not in at;allheads.update(r['guard_heads']);metadata.append({'id':r['id'],'root':root,'full_type_SHA256':H(at.encode()),'universe_params':al,'axioms':ax,'fresh5':fresh,'guard_count':len(r['guard_heads'])})
for side in ['BASE','CANDIDATE']:
 raw=read(B+side+'-metadata.out');parsed=[json.loads(l[len('BOUNDARY|'):]) for l in raw.decode().splitlines() if l.startswith('BOUNDARY|')];assert parsed==(freshbase if side=='BASE' else freshhead);run=next(r for r in J(B+'METADATA-RUNS.json') if r['side']==side);assert run['exit']==run['errors']==0 and H(raw)==run['output_sha256'] and len(raw)==run['output_bytes'];defs=[json.loads(l[len('DEFINITION_IDENTITY|'):]) for l in raw.decode().splitlines() if l.startswith('DEFINITION_IDENTITY|')];assert defs==J(B+side+'-DEFINITION-IDENTITIES.json')
base_defs=J(B+'BASE-DEFINITION-IDENTITIES.json');head_defs=J(B+'CANDIDATE-DEFINITION-IDENTITIES.json');assert base_defs==head_defs and len(base_defs)==23;assert {r['name'] for r in head_defs}==allheads;reuse=J(B+'CONTROL-REUSE-IDENTITIES23.json');candout=J(B+'OUTPUT895.json')
for r in reuse['body_identity_rows']:
 p=r['owner'].replace('.','/')+'.olean';assert anchor[p]==candout[p]==r['whole_owner_olean_hash_equal_BASE_candidate']
control=[]
for folder,n in [('prior-evidence/controls44',44),('controls-pairEncode',2)]:
 runs=J(B+folder+'/CONTROL-RUNS.json');sources={};identities={}
 for side in ['native','sealed']:
  r=next(x for x in runs if x['side']==side);src=read(B+folder+'/Controls-'+side+'.lean.txt').decode();log=read(B+folder+'/Controls-'+side+'.out');assert H(src.encode())==r['input_sha256'] and H(log)==r['output_sha256'];assert r['errors']==(0 if side=='native' else n);assert r['exit']==(0 if side=='native' else 1);rows=re.findall(r'^CONTROL\|(\d+)\|([^|\n]+)\|([^|\n]+)\|(PASS|FAIL)(?:\|kernelChecked=([^\n]+))?',log.decode(),re.M);assert len(rows)==n and all(x[3]==('PASS' if side=='native' else 'FAIL') for x in rows);assert 'CONTROL_COMPLETE|'+str(n) in log.decode();identities[side]=[(x[0],x[1],x[2]) for x in rows];sources[side]=src
  if side=='native':assert all(x[4] for x in rows) and b'error:' not in log
  else:assert log.count(b'error:')==log.count(b'CONTROL_RFL|')==n
 assert identities['native']==identities['sealed'];norm=lambda s:[l for l in s.splitlines() if l.strip() and not l.startswith('attribute [local irreducible]')];assert norm(sources['native'])==norm(sources['sealed']);control.append({'pairs':n,'same_reflected_point_and_abstract_goals':True,'native_kernel_checked':True,'sealed_expected_rfl_errors':n,'common_smartUnfolding_false':True})
oldguards=J(B+'prior-evidence/boundary/CURRENT-GUARD-RECEIPTS10.json');freshguards=J(B+'guards/GUARD-RESULTS.json');guardchecks=[]
for row in selected:
 fresh=row['id'] in ['BLIVE1','BLIVE2','BLIVE3',85,86];r=next(d for d in (freshguards if fresh else oldguards) if d['id']==row['id']);src=read('source/HEAD/'+r['path']+'.txt').decode();guard=read(B+('guards/'+r['input_evidence'] if fresh else 'prior-evidence/old8-guard-inputs/'+str(r['id'])+'.lean.txt')).decode();raw=read(B+('guards/'+r['output_file'] if fresh else 'prior-evidence/old8-guard-logs/'+str(r['id'])+'.out'));assert H(guard.encode())==r['input_sha256']==row['guard_input_sha256'] and H(raw)==r['output_sha256']==row['guard_output_sha256'];assert r['exit']==r['errors']==0 and r['guard_status_witness'];assert set(r['ordinary_heads'])==set(row['guard_heads']);start=r['exact_complete_target_doc_header_body_start'];end=r['prefix_through_complete_target_end'];sec='FHFullBoundary_'+str(row['id']);attr='section '+sec+'\nattribute [local irreducible] '+' '.join(r['ordinary_heads'])+'\n';simp=r['definition_simp_rows_removed'];attr+=('attribute [-simp] '+' '.join(simp)+'\n') if simp else '';prefix=src[:start]+attr+src[start:end];assert guard.startswith(prefix);assert 'GUARD_OK|'+str(row['id'])+'|' in raw.decode() and not b'error:' in raw;states=r['guard_states'];assert len(states)==len(r['ordinary_heads']) and all(s['irreducible'] and not s['definition_simp_unfold'] for s in states);guardchecks.append({'id':row['id'],'fresh5':fresh,'ordinary_heads':r['ordinary_heads'],'exact_current_source_prefix_through_whole_target':True,'historical_full_owner_hash_matches_current':H(src.encode())==r['full_source_sha256'],'input_sha256':H(guard.encode()),'output_sha256':H(raw),'exit':0})
assert [x['id'] for x in guardchecks if not x['historical_full_owner_hash_matches_current']]==[16]
# Parse the supplied full comparison outputs; no extraction or LCS execution.
parsed={};screen=[]
for r in J('screen/RESULTS.json'):
 side=r['side'];raw=read('screen/'+side+'.txt');assert r['exit']==0 and r['source_unchanged'] and len(raw)==r['bytes'] and H(raw)==r['sha256'];s=raw.decode();m=re.match(r'declarations screened: (\d+); copy pairs .*: (\d+); reproduced text: ([\d,]+) chars',s);assert m;ps={}
 for line in s.splitlines()[1:]:
  if not line.strip():continue
  q=re.fullmatch(r'\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%',line);assert q;key=(q.group(1),q.group(2));assert key not in ps;ps[key]=tuple(map(int,q.groups()[2:]))
 assert len(ps)==int(m.group(2));parsed[side]=ps;screen.append({'side':side,'filtered_bodies':int(m.group(1)),'pairs':len(ps),'reproduced_chars':int(m.group(3).replace(',','')),'sha256':H(raw)})
a=parsed['BASE'];b=parsed['HEAD'];new=set(b)-set(a);gone=set(a)-set(b);delta={k for k in a.keys()&b.keys() if a[k]!=b[k]};assert len(new)==0 and len(gone)==19 and len(delta)==4;disp=J('screen/pair-dispositions.json');assert len(disp)==23 and all(x['source_review_complete'] for x in disp);assert collections.Counter(x['status'] for x in disp)=={'BASE_ONLY':19,'PERSISTENT_SCORE_CHANGED':4}
qa='inputs/current77/qa/';runs=J(qa+'RUNS.json')
for r in runs:
 for f,k in [(r['stdout'],'stdout'),(r['stderr'],'stderr')]:
  raw=read(qa+f);assert H(raw)==r[k+'_sha256'] and len(raw)==r[k+'_bytes']
comp=J(qa+'comparison.json');assert comp['style']['BASE_findings']==comp['style']['HEAD_findings']==68 and comp['style']['BASE_exit']==comp['style']['HEAD_exit']==1;assert comp['campaign']['BASE_exit']==comp['campaign']['HEAD_exit']==0
for kind in ['style','campaign']:assert comp[kind]['new_identity_occurrences']==comp[kind]['removed_identity_occurrences']==0
sizes={}
for side in ['BASE','HEAD']:
 ss=[read('source/'+side+'/'+p+'.txt') for p in sorted({r['owner'] for r in json.loads((O/'SOURCE-VERIFICATION.json').read_text())['roots']})];sizes[side]={'bytes':sum(map(len,ss)),'lines':sum(len(x.decode().splitlines()) for x in ss),'over1000':sum(len(x.decode().splitlines())>1000 for x in ss)};assert all(comp['sizes'][side+'_'+k]==v for k,v in sizes[side].items())
r={'replays':replays,'metadata13':metadata,'full_23_definition_Expr_identities_equal_and_owner_object_reuse_bound':True,'controls':control,'guards13':guardchecks,'ordinary_union':sorted(allheads),'screen44':screen,'screen_delta':{'new':len(new),'BASE_only':len(gone),'persistent_score_changed':len(delta),'all23_source_dispositions':True},'recorded_lint':comp,'independent_source_sizes':sizes,'execution_limit':'Only read-only Git, byte/hash/source/record parsing; no Lean, native/seal/control, replay, static checker, lint, extraction or LCS execution by this review. Physical snapshots not inspected.','used_inputs':used};(O/'EVIDENCE-VERIFICATION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['replays','controls','screen44','screen_delta','independent_source_sizes','execution_limit']},indent=2))
