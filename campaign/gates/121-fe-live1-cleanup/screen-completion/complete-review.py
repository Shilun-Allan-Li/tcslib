from pathlib import Path
import json,hashlib,re,shutil
O=Path('/private/tmp/ab34-fe9-screen-review');D=Path('/private/tmp/ab34-fe9-gate-draft')
h=lambda b:hashlib.sha256(b).hexdigest()
assert not (O/'MANIFEST.json').exists()
for n in ['BASE-declaration-capture-index.json','HEAD-declaration-capture-index.json']:
 shutil.copy2(D/'qa'/n,O/n)
for n in ['ACKNOWLEDGED-FE-SCOPE.txt','ACKNOWLEDGED-FE-SCOPE-binding.json','ACKNOWLEDGMENT-INPUTS.json']:
 shutil.copy2(D/'bindings'/n,O/n)
# Copy the exact recorded ruling context and ledger named by its binding; no new ruling.
for r in json.loads((D/'bindings/ACKNOWLEDGMENT-INPUTS.json').read_text()):
 p=O/r['capture'];p.parent.mkdir(parents=True,exist_ok=True);b=(D/r['capture']).read_bytes();assert h(b)==r['SHA256'];p.write_bytes(b)
p=O/'standards/campaign/duplication-ledger.md';p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((D/'standards/campaign/duplication-ledger.md').read_bytes());assert h(p.read_bytes())==json.loads((O/'ACKNOWLEDGED-FE-SCOPE-binding.json').read_text())['full_source_SHA256']
source=json.loads((O/'all66-source-bindings.json').read_text());source_by={(r['phase'],r['path']):r for r in source}
ep=json.loads((O/'endpoint-source-bindings.json').read_text());ep_by={(r['phase'],r['screen_label']):r for r in ep};sp=json.loads((O/'literal-spans.json').read_text())
def body(phase,label):
 r=ep_by[(phase,label)];return (O/r['capture']).read_text().split('\n/--',1)[0].split('\n/-!',1)[0]
def literal(phase,label,needle,category,note):
 r=ep_by[(phase,label)];text=(O/source_by[(phase,r['path'])]['capture']).read_text();chunk=(O/r['capture']).read_text();off=chunk.index(needle);start=r['source_start_char']+off;assert text[start:start+len(needle)]==needle
 row={'id':'S'+str(len(sp['spans'])+1),'phase':phase,'screen_label':label,'source_path':r['path'],'start_char':start,'end_char':start+len(needle),'start_line':text.count('\n',0,start)+1,'literal':needle,'UTF8_bytes':len(needle.encode()),'SHA256':h(needle.encode()),'category':category,'note':note};sp['spans'].append(row);return row['id']
# Exact original/source span bindings for removed rows, no pair matcher invoked.
for label in ['EXP.lean::enumCont_first_anchor','ExhaustiveReplay.lean::xr_firstArrival',"ExhaustiveReplay.lean::xr_firstArrival'"]:
 b=body('BASE',label);a=b.index('  classical');needle=b[a:]
 literal('BASE',label,needle,'removed inline first-entry selection/endpoint proof','Whole old proof body from classical onward, including Nat.find minimality and fixed-run endpoint reasoning; the supplied BASE rows remain historical observations.')
 literal('HEAD',label,'  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed','replacement public API citation','Exact existing generic public fixed-live-stop first-entry theorem; statement and singleton/predicate endpoint obligations stay at this caller.')
# Retained other-family donor proof bodies: actual before/after equality, not inferred from score.
unchanged=[]
for label in ['EXP.lean::enumCont_first_halt','EXP.lean::enumCont_halt_transfer','Hardness.lean::clCmp_idle','Hardness.lean::clCopy_idle','Hardness.lean::clFresh_idle','Hardness.lean::clInput_idle','Hardness.lean::clWipe_idle']:
 assert body('BASE',label)==body('HEAD',label)
 unchanged.append({'screen_label':label,'scope':'actual declaration/header/body before following comment','BASE_HEAD_exact':True,'UTF8_bytes':len(body('BASE',label).encode()),'SHA256':h(body('BASE',label).encode()),'BASE':ep_by[('BASE',label)],'HEAD':ep_by[('HEAD',label)]})
# Bind complete new InputCall callback, and separate terminal endpoint proof, without new tiling.
label='InputCall.lean::inputSeekRewind_run';b=body('HEAD',label);a=b.index('    (by\n      rintro z');z=b.index('    ⟨.done, rfl, rfl⟩ hend',a)
callback=literal('HEAD',label,b[a:z],'public reader / configuration-identity adapter','The five new InputCall edges share this zero-action callback; it proves fixedness of a done configuration from the already public step/effect/zero-move readers, then record cases. BASE already had the same fixedness subgoal.')
a=b.index('  have hend :');z=b.index('  obtain ⟨u, hu, hcut, he⟩',a)
terminal=literal('HEAD',label,b[a:z],'terminal endpoint adapter (distinct location)','Negative final input movement uses public controlAction_apply/moveInputPos_neg_val and Cfg.ext. The exact new zero-action literals are in the later callback, not here.')
(O/'literal-spans.json').write_text(json.dumps(sp,indent=2,ensure_ascii=False)+'\n')
(O/'unchanged-donor-declarations.json').write_text(json.dumps(unchanged,indent=2)+'\n')
pat=re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%',re.M)
rows={}
for phase in ['BASE','HEAD']:
 rows[phase]={}
 for t,s,n,d,p in pat.findall((O/(phase+'.txt')).read_text()):
  assert (t,s) not in rows[phase];rows[phase][(t,s)]={'matched_chars':int(n),'source_chars':int(d),'percent':int(p)}
shared=[]
for key in sorted(rows['BASE'].keys()&rows['HEAD'].keys()):
 assert rows['BASE'][key]==rows['HEAD'][key];shared.append({'target':key[0],'source':key[1],'BASE':rows['BASE'][key],'HEAD':rows['HEAD'][key],'score_unchanged':True})
assert len(shared)==2102
(O/'all2102-persistent-row-comparisons.json').write_text(json.dumps(shared,indent=2)+'\n')
delta=json.loads((O/'all-existing-row-deltas.json').read_text());dis=[]
def add(row,id,status,meaning,newmaterial,limits,spanids):
 er={phase:{kind:ep_by[(phase,row[kind])] for kind in ['target','source']} for phase in ['BASE','HEAD']}
 dis.append({'id':id,'direction':'target reproduces source','row_status':status,**row,'disposition':meaning,'material_entered_or_removed':newmaterial,'limits_and_debt':limits,'literal_span_ids':spanids,'endpoint_source_bindings':er,'recommendation':'accept bounded screen disposition; no new fix/design/ruling requested'})
for i,r in enumerate(delta['new'],1):
 t=r['target'];s=r['source']
 if t.startswith('Hardness'):
  names={'clCmp_first':('S7','S8','S9'),'clCopy_first':('S1','S2','S3'),'clRow_first':('S4','S5','S6')};ids=list(names[t.split('::')[1]])+['S10','S11','S12']
  particular={'clCmp_first':'Comparator stop predicate includes BOTH completed Bool verdicts; disjoint initial/returned sum constructors prove t>0, and the existing arithmetic verdict fact stays separately cited.','clCopy_first':'Copier preserves the entire recorded endpoint, even for empty w; initial0 and returned4 exclude t=0.','clRow_first':'Row uses stored endpoint bound and hl>0 to distinguish initial row0 from Fin.last l; no zero-width case is inferred beyond the unchanged hypothesis.'}[t.split('::')[1]]
  add(r,f'N{i}','new','public canonical API citation/result adaptation plus retained pre-existing positive-time exclusion',particular+' The new obtain/canonical call, predicate packaging, and result tuple replace old local Nat.find/minimality/endpoint-stabilization material. Each endpoint already had its own positive-time contradiction at BASE; the new congrArg Cfg.state he reads the stronger public endpoint instead of Nat.find_spec.', 'Existing FE-LIVE-1 explicitly includes initial-exclusion positive-time specializations, but grants no future-copy permission. This row does not introduce a new proved positive-time algorithm: its corresponding BASE block is preserved in the bindings. Residual positive-time adapters remain disclosed; do not claim full proof-family absence, new debt acceptance or exact counts from directed scores.',ids)
 else:
  donor=s.split('::')[1];ids={'clCmp_idle':['S19','S20'],'clCopy_idle':['S17','S18'],'clFresh_idle':['S21','S22'],'clInput_idle':['S15','S16'],'clWipe_idle':['S13','S14']}[donor]+['S23','S24','S25',callback,terminal]
  add(r,f'N{i}','new','public-reader zero-action configuration-identity glue', 'New text specializes step_of_some, controlAction_apply and moveInputPos_zero at InputSeekRw.done and closes a record identity by cases/simp_all. This shares public-reader invocations and simple configuration glue with '+donor+', whose actual declaration is byte-exact BASE/HEAD. BASE inputSeekRewind_run already had the same done-state full fixedness subgoal via step_of_inputMoveAction and Cfg.ext. No donor machine scan, first-entry minimization, counter, bank or dispatcher implementation entered.', 'This classification does not acknowledge a new debt kind. The old Hardness idle proof still unfolds MultiTapeTM.step and remains outside the nine edited targets; this review does not approve or retire that old proof. The terminal negative movement Cfg.ext block is separately bound and is not the location of the shared zero-action literals. Exact hfix/source context is preserved; selected literals do not reconstruct the greedy score.',ids)
for i,r in enumerate(delta['gone'],1):
 if r['target'].startswith('EXP'):
  add(r,f'G{i}','gone','old inline fixed-live-stop selection/absorption overlap removed at enumCont_first_anchor', 'The old anchor caller implemented Nat.find, least-time exclusion and absorption to preserve its endpoint; it now cites exists_first_entry_of_fixed and retains only singleton/result and tm/stop agreement adapters. The other endpoint '+(r['source'] if 'anchor' in r['target'] else r['target'])+' is unchanged at its actual declaration.', 'enumCont_first_halt remains the distinct first-None family; enumCont_halt_transfer retains its existing no-live-anchor transfer reasoning. Loss of these directed edges proves no retirement of first-None or all transfer proofs. A below-threshold source pair may still share routine text; no absence theorem is claimed.',[x['id'] for x in sp['spans'] if x['screen_label']=='EXP.lean::enumCont_first_anchor' and x['id'] not in [a['id'] for a in sp['spans'][:25]]])
 else:
  add(r,f'G{i}','gone','old mutual singleton/predicate first-entry implementation overlap removed', 'Both XR wrappers replaced their separate Nat.find/minimality/fixed-run endpoint implementations with the same existing canonical theorem and statement-preserving singleton/predicate result adapters.', 'Both full wrappers are source-bound before/after. These two directed rows count no additional unique declarations; this is no all-TCSlib FE retirement or first-None/BLIVE clearance.',[x['id'] for x in sp['spans'] if x['screen_label'] in ['ExhaustiveReplay.lean::xr_firstArrival',"ExhaustiveReplay.lean::xr_firstArrival'"] and x['id'] not in [a['id'] for a in sp['spans'][:25]]])
assert len(dis)==13
(O/'all13-pair-dispositions.json').write_text(json.dumps(dis,indent=2,ensure_ascii=False)+'\n')
lines=['# Complete FE9 current33 screen dispositions','','Direction is target reproduces source. Numeric rows are parsed verbatim from the two existing outputs; this review ran no scorer or screen. Complete endpoint bindings and selected literal spans are in the JSON companions.','', '| ID | Status | Target ← source | Recorded score | Actual material and disposition |','|---|---|---|---|---|']
for r in dis:
 brief=r['disposition']+'. '+r['material_entered_or_removed']+' Limits: '+r['limits_and_debt']
 lines.append('| '+r['id']+' | '+r['row_status']+' | `'+r['target']+'` ← `'+r['source']+'` | '+str(r['matched_chars'])+'/'+str(r['source_chars'])+'='+str(r['percent'])+'% | '+brief.replace('|','\\|')+' Span IDs: '+', '.join(r['literal_span_ids'])+'. |')
lines+=['','Persistent rows: **2,102 shared, all2,102 matched-chars/source-length/percent vectors identical; zero changed scores**. The complete uncapped parsed identity comparison is `all2102-persistent-row-comparisons.json`. No semantic review of all unchanged historical pairs or global debt clearance is claimed.','']
(O/'all13-pair-dispositions.md').write_text('\n'.join(lines))
receipt=json.loads((O/'screen-source-format-receipt.json').read_text());receipt.update({'review_kind':'read-only semantic inspection of all existing pair deltas and all persistent-score comparisons','full_uncapped_dispositions':13,'literal_source_spans':len(sp['spans']),'full_endpoint_phase_captures':30,'all_7_donor_actual_declarations_BASE_HEAD_exact':True,'new_unapproved_copied_proved_algorithm_found':False,'new_debt_acceptance_or_design_ruling_inferred':False,'reviewer_ran_Lean_screen_or_pair_scorer':False,'source_Git_canonical_external_mutations':False,'parent_frozen_input_manifest_SHA256':'1a0586d32d6bd4f9925a062ca2b4e8aad49ca369152790e615169cc942386d16','prior_peer_manifest_SHA256':'49e8f7f98122978b686a860463ba5c1ca62dc2f9084e77aef3db272160d3e7dd','current_request_SHA256':h((O/'request.json').read_bytes()),'current_result_SHA256':h((O/'RESULT.json').read_bytes()),'BASE_request_SHA256':h((O/'BASE-request.json').read_bytes()),'BASE_result_SHA256':h((O/'BASE-RESULT.json').read_bytes()),'helper_SHA256':h((O/'screen-tool.py').read_bytes()),'pairdiff_helper_SHA256':h((O/'pairdiff-tool.py').read_bytes()),'status':'COMPLETE_PRIVATE_REVIEW; root adoption/publication/external audit remain root-owned'})
(O/'completion-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'dispositions':len(dis),'spans':len(sp['spans']),'persistent':len(shared),'requestSHA':receipt['current_request_SHA256']}))
