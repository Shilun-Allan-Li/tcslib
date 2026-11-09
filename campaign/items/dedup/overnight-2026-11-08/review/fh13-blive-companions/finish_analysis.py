from pathlib import Path
import json,hashlib,re,ast,shutil,subprocess,datetime
O=Path(__file__).parent;E=Path('/private/tmp/ab34-fh10-final-qa/EXPORT');pin=json.loads((O/'PIN.json').read_text());W=Path(pin['source_worktree']);sha=lambda b:hashlib.sha256(b).hexdigest()
def write(p,d):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def g(*a):return subprocess.check_output(['git','-C',str(W),*a])
assert g('rev-parse','HEAD').decode().strip()==pin['HEAD'];g('cat-file','-e',pin['HEAD']+'^{commit}');g('cat-file','-e',pin['BASE']+'^{commit}');assert not g('status','--porcelain','--untracked-files=no')
oldpin=json.loads((E/'PIN.json').read_text());owners=[]
for d in oldpin['owners']:
 p=d['path'];a=g('show',pin['HEAD']+':'+p);b=g('show',pin['BASE']+':'+p);assert a==(W/p).read_bytes();assert sha(a)==d['HEAD_sha256'] and sha(b)==d['BASE_sha256']
 c=(O/'source/CANDIDATE'/(p+'.txt')).read_bytes() if (O/'source/CANDIDATE'/(p+'.txt')).exists() else a
 for side,raw in [('E0B',a),('BASE',b),('CANDIDATE',c)]:
  f=O/'source'/side/(p+'.txt');f.parent.mkdir(parents=True,exist_ok=True)
  if f.exists():assert f.read_bytes()==raw
  else:f.write_bytes(raw)
 owners.append({'path':p,'BASE_blob':d['BASE_blob'],'E0B_blob':d['HEAD_blob'],'BASE_sha256':sha(b),'E0B_sha256':sha(a),'candidate_sha256':sha(c),'candidate_differs_from_E0B':a!=c,'candidate_has_no_Git_blob_binding':True})
write(O/'SOURCE-MAP8.json',owners)
helper=W/'devtools/seyoon/declfreeze.py';dest=O/'tools/declfreeze.py';dest.parent.mkdir(exist_ok=True);shutil.copyfile(helper,dest)
module=ast.parse(helper.read_text());allowed={'KW','DECL','ANON','STOP','SCOPE'};nodes=[n for n in module.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(t,ast.Name) and t.id in allowed for t in n.targets)];ns={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns);chunks=ns['chunks'];allchunks={};counts=[]
for d in owners:
 p=d['path'];a=(O/'source/E0B'/(p+'.txt')).read_text();c=(O/'source/CANDIDATE'/(p+'.txt')).read_text();A={n:(priv,t) for n,priv,t in chunks(a)};C={n:(priv,t) for n,priv,t in chunks(c)};assert set(A)==set(C);changed=[]
 for n,(priv,t) in A.items():
  at=a.index(t);allchunks[(p,n)]={'private':priv,'text':t,'source_line':a[:at].count('\n')+1,'lines':len(t.splitlines())}
  if A[n]!=C[n]:changed.append(n)
 counts.append({'path':p,'public':sum(not z[0] for z in A.values()),'private':sum(z[0] for z in A.values()),'changed_complete_declarations':changed})
assert sorted(n for d in counts for n in d['changed_complete_declarations'])==sorted('Turing.'+r['name'] for r in pin['targets'])
reverse=[]
for d in owners:
 p=d['path'];a=(O/'source/E0B'/(p+'.txt')).read_text();c=(O/'source/CANDIDATE'/(p+'.txt')).read_text();restored=c
 for t in pin['targets']:
  if t['path']!=p:continue
  old=(O/t['old_chunk']).read_text();new=(O/t['new_chunk']).read_text();assert restored.count(new)==1;restored=restored.replace(new,old,1);assert old.startswith(t['literal_header']) and new.startswith(t['literal_header']);assert (O/'source/BASE'/(p+'.txt')).read_text().count(t['literal_header'])==1
 assert restored==a
 imports=lambda s:re.findall(r'(?m)^import[^\n]*',s)
 assert imports(a)==imports(c)
 reverse.append({'path':p,'three_body_reversal_recovers_complete_E0B_bytes':True,'imports_exact':True,'all_names_privacy_attrs_and_non_target_chunks_exact':True})
write(O/'SOURCE-PRESERVATION8.json',{'only_changed_decl_bodies':3,'no_import_header_name_definition_API_statement_home_route_or_admission_change':True,'owner_counts':counts,'recovery':reverse,'parser_source_sha256':sha(helper.read_bytes()),'actual_source_still_clean_at':pin['HEAD']})
B=O/'bounded-sweep8';candidates=json.loads((B/'ALL-FORM-CANDIDATES.json').read_text());assert len(candidates)==39
reasons={
1:'Undo simulation induction consumes the supplied complete live-prefix guard; it does not infer earlier liveness from a later live endpoint.',
2:'Capture simulation consumes the supplied complete live-prefix guard through capture_run.',
3:'First-halt/capture restoration uses enumCont_first_halt; this is not generic backwards propagation of liveness.',
4:'Return simulation induction consumes a supplied complete live-prefix guard.',
5:'One-step nondeterministic/deterministic capture correspondence, with a halted-state case split; no two-time liveness inference.',
6:'Uses canonical first-halt existence and transfer; deterministic first-None selection, not backwards-live reproof.',
7:'Nondeterministic host simulation shifts a supplied live-prefix guard with runFrom_succ.',
8:'Coverage proof consumes its supplied full live-prefix guard and previously proved coverage facts.',
9:'Verifier host simulation shifts a supplied live-prefix guard with runFrom_succ.',
10:'Host composition consumes provided live-prefix and coverage facts; no generic earlier-live derivation.',
11:'Canonical first-halt/output packaging.',12:'Canonical first-halt reader plus positive-time packaging from initial liveness.',
13:'Already directly cites MultiTapeTM.runFrom_state_ne_none_of_le.',
14:'One-source-step/frame correspondence with source-state case split; no time-prefix liveness conclusion.',
15:'One-step position correspondence with halted-state stationarity.',
16:'Canonical first-halt reader plus positive-time packaging from initial liveness.',
17:'Already directly cites MultiTapeTM.runFrom_state_ne_none_of_le.',
18:'First-halt minimality and periodic-core injection argument; the supplied later endpoint is halted, not live.',
19:'Canonical first-halt minimum and resource count, with forward post-halt stability; different contract.',
20:'All-times space bound from a halted endpoint using forward tail absorption, not a backwards-live conclusion.',
21:'Lockstep induction from a provided complete live-prefix guard.',
22:'Machine-specific simulation blocks and halted-state stuttering, not generic earlier-live inference.',
23:'Constructs a ready state and lookup block by machine-specific simulation; no generic two-time live inference.',
24:'MATCH BLIVE1: decomposes s <= t, uses runFrom_add/runFrom_of_halt contradiction; exact public reader specialization passes.',
25:'Consumes local timedCut_live_before, then reasons about the machine-specific applyRecord stop state; wrapper is repointed by BLIVE1.',
26:'Consumes timedCut_live_before and no_record to prove lockstep replay; wrapper is repointed by BLIVE1.',
27:'Constructs the exact later live endpoint from parser runs; that witness is the premise used by BLIVE2.',
28:'MATCH BLIVE2: predecessor endpoint plus add/post-halt contradiction; exact public reader and timedPrefix_penultimate specialization passes.',
29:'Countdown/simulation composition and forward post-halt simplification; consumes timed_replay, not a generic earlier-live reproof.',
30:'Capture induction consumes a supplied complete source live-prefix guard.',
31:'One-step frame correspondence with a halted-state stuttering case.',
32:'Non-computation of every output implies live at the same deadline; no earlier-time conclusion.',
33:'Same-deadline non-computation-to-live reasoning; no earlier-time conclusion.',
34:'MATCH BLIVE3: decomposes s <= t, uses runFrom_add/runFrom_of_halt contradiction; exact public reader specialization passes.',
35:'Already consumes universal_live_before with universalPrefix_penultimate; wrapper is repointed by BLIVE3.',
36:'Capture induction consumes a supplied complete source live-prefix guard.',
37:'Already exact canonical exists_first_halt reader, not backwards-live reproof.',
38:'A definition specifying a clean/first-halt contract, with no proof.',39:'A definition specifying a clean/first-halt contract, with no proof.'}
rows=[]
for d in candidates:
 k=(d['path'],d['name']);z=allchunks[k];saved=(B/d['chunk']).read_text();assert saved.rstrip()==z['text'].rstrip();row=d|{'complete_chunk_sha256':sha(saved.encode()),'actual_full_source_sha256':next(r['E0B_sha256'] for r in owners if r['path']==d['path']),'inspected_complete_chunk':True,'disposition':'MECHANICAL_REPAIR' if d['id'] in [24,28,34] else 'ALREADY_READER' if d['id'] in [13,17,25,26,35,37] else 'DIFFERENT_CONTRACT_OR_NO_REPROOF','reason':reasons[d['id']],'same_public_API_route':'Turing.MultiTapeTM.runFrom_state_ne_none_of_le' if d['id'] in [13,17,24,28,34] else None};rows.append(row)
write(B/'DISPOSITIONS39.json',rows)
md=['# Bounded backwards-live inspection of the eight actual FH owners','',f'Actual source: `{pin["HEAD"]}`. Candidate enumeration plus inspection; no global absence or exhaustive-search claim. The original 22 narrower candidates, expanded 39 complete chunks and all 380 raw closing-form hits are retained uncapped. All 39 complete chunks were inspected. Only candidates 24, 28 and 34 match the generic backwards-live reproof kind and need the three private repoints.','', '| ID | Declaration | Disposition | Inspection |','|---|---|---|---|']
for d in rows:md.append(f'| {d["id"]} | `{d["name"]}` | {d["disposition"]} | {d["reason"]} |')
(B/'DISPOSITIONS39.md').write_text('\n'.join(md)+'\n')
# Preserve two additional decomposition/absorption chunks as explicit exclusion controls.
extra=[]
for i,n in enumerate(['Complexity.enumCont_first_anchor','Complexity.enumCont_halt_transfer'],1):
 p='TCSlib/Complexity/ClassNP/EXP.lean';z=allchunks[(p,n)];f=B/'mixed-stop-exclusions'/f'{i:02}.lean.txt';f.parent.mkdir(exist_ok=True);f.write_text(z['text']+'\n');extra.append({'name':n,'path':p,'chunk':str(f.relative_to(B)),'source_line':z['source_line'],'sha256':sha(f.read_bytes()),'inspected_complete_chunk':True,'reason':'Absorption at the live anchor some qa and transfer between two machines. The endpoint/forbidden state is not the halted state none; the generic backwards-live reader does not supply this contract. Different mixed-stop family, retained unchanged.'})
write(B/'MIXED-STOP-EXCLUSIONS2.json',extra)
raw=json.loads((B/'ALL-CLOSING-HITS.json').read_text());assert len(raw)==380;contained=[]
for h in raw:
 source=(O/'source/E0B'/(h['path']+'.txt')).read_text();assert source.splitlines()[h['line']-1]==h['text'];containers=[{'name':n,'start_line':z['source_line'],'lines':z['lines']} for (p,n),z in allchunks.items() if p==h['path'] and z['source_line']<=h['line']<z['source_line']+z['lines']];contained.append(h|{'declaration_containers':containers})
write(B/'RAW380-SOURCE-BINDING.json',contained)
write(B/'ALL-DECLARATION-INVENTORY8.json',[{'path':p,'name':n,**{k:v for k,v in z.items() if k!='text'},'chunk_sha256':sha(z['text'].encode())} for (p,n),z in allchunks.items()])
write(B/'METHOD-LIMITS.json',{'scope':'eight actual FH touched owners at e0b; no unchanged43-context-owner expansion','original_narrow_candidates':22,'expanded_complete_candidates_inspected':39,'additional_mixed_stop_chunks_inspected':2,'uncapped_original_raw_closing_form_hits':380,'matched_repair_members':['BLIVE1','BLIVE2','BLIVE3'],'all_closing_forms_reviewed':['Nat.exists_eq_add_of_le','runFrom_add','runFrom_of_halt','step_of_halt','state none/ne none/isSome/Halted predicates','inline have/intro/contradiction','change/show/simp/simpa/simp_all/rw/rwa/unfold/delta/dsimp','induction/contraposition/by_contra','exact-only readers'],'reconstruction_note':'The initial inline enumeration scripts were not retained. This saved script independently verifies every saved complete chunk and every raw hit against actual pinned source, preserves the complete declaration inventory, and records the inspected dispositions. It does not invent original command provenance.','limits':['Candidate enumeration plus source inspection only; no proof of exhaustive absence.','Mixed-stop and nondeterministic contracts remain outside this generic deterministic backwards-live family.','No additional Lean jobs or copy-text screen were run for this sweep.']})
# Validate the new effective controls and all five current guards.
C=O/'controls-pairEncode';runs=json.loads((C/'CONTROL-RUNS.json').read_text());controls=[]
for d in runs:
 raw=(C/d['output_file']).read_bytes();assert sha(raw)==d['output_sha256'];s=raw.decode();assert s.count('CONTROL_COMPLETE|2')==1
 if d['side']=='native':assert d['exit']==0 and d['errors']==0 and s.count('|PASS|kernelChecked=')==2 and '|FAIL' not in s
 else:assert d['exit']==1 and d['errors']==2 and s.count('|FAIL')==2 and s.count('error: CONTROL_RFL|')==2 and '|PASS' not in s
for mode in ['point','abstract']:controls.append({'name':'Turing.pairEncode','mode':mode,'native_kernel_checked':True,'sealed_rfl_expected_failure':True,'no_unrelated_error':True})
write(C/'CONTROL-VERIFIED2.json',controls)
guards=json.loads((O/'guards/GUARD-RESULTS.json').read_text());assert len(guards)==5 and all(d['PASS_compilation'] and d['exit']==0 and d['errors']==0 and d['guard_status_witness'] for d in guards);assert all(d['argv'][3]==str(O/'live/oleans-candidate13') for d in guards)
base=json.loads((O/'BASE-FOOTPRINTS5.json').read_text());cand=json.loads((O/'CANDIDATE-FOOTPRINTS5.json').read_text());comparison=[]
for a,b in zip(base,cand):
 assert a['root']==b['root'];keys=['root_type_Expr','root_levelParams','root_axioms'];actual=[k for k in keys if k in a];assert actual
 for k in actual:assert a[k]==b[k],(a['root'],k)
 comparison.append({'root':b['root'],'compared_fields':actual,'all_exact':True,'BASE_full_metadata':'BASE-FOOTPRINTS5.json','candidate_full_metadata':'CANDIDATE-FOOTPRINTS5.json'})
write(O/'TYPE-AX-COMPARISON5.json',comparison)
# Reuse only full unchanged source owners for the other eight selected FH roots.
root10=json.loads((E/'ROOTS10.json').read_text());write(O/'PRIOR10-SOURCE-BINDING.json',{'roots_document_sha256':sha((E/'ROOTS10.json').read_bytes()),'other_six_owners_byte_exact_E0B':[d for d in owners if not d['candidate_differs_from_E0B']],'two_affected_owners_five_fresh_guards':['BLIVE1','BLIVE2','BLIVE3',85,86],'reuse_limit':'The other eight FH roots in six unchanged owners retain exact owner bytes and old bounded guards. No literal old-prefix equality is claimed for the two affected capture roots; they have fresh full-head guards. Exact old44 controls reuse is separately bound by full definition type/value Expr strings and whole-owner object hashes.'})
print(json.dumps({'source_owners':len(owners),'only_private_changed_bodies':3,'full_candidate_scan_dispositions':len(rows),'extra_mixed_stop_exclusions':len(extra),'raw_hits_verified':len(raw) if isinstance(raw,list) else 380,'guards_current':len(guards),'new_pairs':len(controls),'metadata_comparisons':len(comparison)}))
