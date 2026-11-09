from pathlib import Path
import json,re,hashlib,shutil,difflib,subprocess,datetime
O=Path(__file__).parent;S=O/'EXPORT-SAFE7';E=O/'EXPORT-REPAIRS3';assert not E.exists();E.mkdir();pin=json.loads((O/'PIN.json').read_text());safe=json.loads((S/'DISPOSITIONS17.json').read_text());eligible={9,16,18,19,33,85,86};repairs={47:'reader47',17:'reader17',54:'reader54'};W=Path(pin['source_worktree'])
P=O/'controls-retained10';cr=json.loads((P/'CONTROL-RUNS.json').read_text());a=(P/'Controls-native.out').read_text();b=(P/'Controls-sealed.out').read_text();pos=re.findall(r'CONTROL\|(\d+)\|([^|]+)\|(point|abstract)\|PASS\|kernelChecked=([^\s]+)',a);neg=re.findall(r'CONTROL\|(\d+)\|([^|]+)\|(point|abstract)\|FAIL',b);assert len(pos)==len(neg)==44 and [r[:3] for r in pos]==neg;assert 'CONTROL_COMPLETE|44' in a and 'CONTROL_COMPLETE|44' in b;assert cr[0]['exit']==0 and cr[0]['errors']==0 and cr[1]['exit']==1 and cr[1]['errors']==44;assert '|FAIL' not in a and '|PASS|' not in b
cv={'ordinary_union':22,'native_kernel_checked':44,'sealed_rfl_failures':44,'completion_markers_both':True,'native_exit':0,'native_errors':0,'sealed_exit':1,'sealed_expected_errors':44,'sealed_other_errors':0,'both_sides_smartUnfolding':False,'no_transparency_override':True,'identities':[{'index':int(r[0]),'head':r[1],'mode':r[2],'native_kernel_name':r[3],'native_PASS':True,'sealed_FAIL':True} for r in pos]};(E/'CONTROL-VERIFIED44.json').write_text(json.dumps(cv,indent=2)+'\n')
def copy_private_tree(src,dst):
 dst.mkdir(parents=True,exist_ok=True)
 for f in sorted(src.rglob('*')):
  rel=f.relative_to(src)
  if 'live' in rel.parts:continue
  assert not f.is_symlink()
  if f.is_file():
   assert not f.name.endswith('.lean');out=dst/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,out)
copy_private_tree(P,E/'controls')
for d in ['context','foreign-source']:shutil.copytree(O/d,E/d)
for n in ['PIN.json','FOREIGN-SOURCE-MAP.json','MAC8-OBJECTS895.json','BINDING-CHECK.json','prepare_hypothesis.py','run_hypothesis_native.py','CollectorSuffix.lean.txt','freeze_repairs.py','DEFINITION-CATALOG.json','READER-CATALOG.json']:shutil.copyfile(O/n,E/n)
rows=[];fulltypes=[];guards=[];commands=[];patch=[];finalpatch=[];paths=sorted({r['path'] for r in pin['roots'] if r['id'] in eligible|set(repairs)})
for path in paths:
 before=(O/'source'/(path+'.txt')).read_text();candidate=before
 for idx,label in repairs.items():
  r=next(r for r in pin['roots'] if r['id']==idx)
  if r['path']==path:candidate=(O/'hypotheses'/label/'source'/(path+'.txt')).read_text()
 for side,text in [('BEFORE70',before),('PRIVATE-CANDIDATE',candidate)]:
  out=E/'source'/side/(path+'.txt');out.parent.mkdir(parents=True,exist_ok=True);out.write_text(text)
 patch.extend(difflib.unified_diff(before.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path))
 base=subprocess.check_output(['git','-C',str(W),'show',pin['MAC8_source']+':'+path]).decode();out=E/'source/MAC8'/(path+'.txt');out.parent.mkdir(parents=True,exist_ok=True);out.write_text(base);finalpatch.extend(difflib.unified_diff(base.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path))
(E/'reader-repairs3-over70.patch').write_text(''.join(patch));(E/'proposed-final10-overMAC8.patch').write_text(''.join(finalpatch))
for r in safe:
 idx=r['id'];row=dict(r)
 if idx in eligible:
  row['retained_candidate_status']='PASS current committed body within recorded boundary';row['private_repair_applied']=False
  guard=next(g for g in json.loads((O/'GUARD-RESULTS.json').read_text()) if g['id']==idx)
  for rel in [guard['input_evidence'],guard['output_file']]:
   f=O/rel;out=E/'safe7'/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,out)
  fulltypes.append(next(f for f in json.loads((O/'FOOTPRINTS17.json').read_text()) if f['suffix']==r['name']));guards.append(guard)
 elif idx in repairs:
  H=O/'hypotheses'/repairs[idx];copy_private_tree(H,E/'hypotheses'/repairs[idx]);nr=json.loads((H/'NATIVE-RUN.json').read_text());fp=json.loads((H/'FOOTPRINT.json').read_text());G=H/'strong-source-reader' if idx==17 else H;gr=json.loads((G/'GUARD-RESULTS.json').read_text())[0];assert nr['exit']==0 and nr['errors']==0 and nr['sorry_warnings']==0 and gr['PASS_compilation'] and gr['guard_status_witness'];old=(H/'old-chunk.lean.txt').read_text();new=(H/'new-chunk.lean.txt').read_text();h=lambda s:s[:re.search(r':= by(?:\n|$)',s).start()];assert h(old)==h(new)
  row.update({'retained_candidate_status':'HYPOTHETICAL REPAIR PASS within recorded boundary; not current source until root adoption','private_repair_applied':True,'private_repair':repairs[idx],'hypothetical_repair_PASS':True,'fresh_compiled_ordinary_heads':len([f for f in fp['foreign_definition_mentions'] if f['ordinary_guard_target']]),'candidate_guard_heads':gr['ordinary_head_count'],'candidate_guard_names':gr['ordinary_heads'],'candidate_definition_simp_rows_removed':gr['definition_simp_rows_removed'],'candidate_native':nr,'candidate_guard':gr,'candidate_type_Expr':fp['root_type_Expr'],'candidate_type_pretty':fp['root_type_pretty'],'candidate_universe_params':fp['root_levelParams'],'candidate_axioms':fp['root_axioms'],'candidate_literal_header':h(new),'literal_header_unchanged':True,'compiled_type_Expr_and_universes_exact_current70':True,'candidate_chunk_sha256':hashlib.sha256(new.encode()).hexdigest(),'candidate_owner_sha256':hashlib.sha256((H/'source'/(r['path']+'.txt')).read_bytes()).hexdigest(),'candidate_explicit_foreign_definition_args':[],'candidate_explicit_Core_Mathlib_definition_args':[]})
  fulltypes.append(fp);guards.append(gr)
 else:row['retained_candidate_status']='HOLD; proposed final scope restores exact MAC8 whole owner source';row['private_repair_applied']=False
 rows.append(row)
original=json.loads((S/'EXPLICIT-COMMANDS.json').read_text());commands.extend(r for r in original if r['id'] in eligible)
reviews={17:'VirtualTag_iff, MultiTapeTM.initCfg_eq and Cfg.init_inputPos are published theorems. Remaining args are local facts or existing theorem readers; no foreign/Core definition argument.',47:'spaceUsedByTape_eq_card and mem_visitedByTapeHead_iff are published theorems. configBound is same-owner def; remaining args are local facts/theorems. No foreign/Core definition argument.',54:'initCfg_eq and Cfg.init_inputPos/workTapes/workTapePos are published theorems. ctrCfg is same-owner def; start local let; hi/hw/hp local facts. No foreign/Core definition argument.'}
for idx,label in repairs.items():commands.append({'id':idx,'complete_candidate_chunk':(O/'hypotheses'/label/'new-chunk.lean.txt').read_text(),'review':reviews[idx]})
(E/'DISPOSITIONS17-CANDIDATE10.json').write_text(json.dumps(rows,indent=2)+'\n');(E/'EXPLICIT-REVIEW10.json').write_text(json.dumps(commands,indent=2)+'\n');(E/'SELECTED-ROOT-TYPES10.json').write_text(json.dumps(fulltypes,indent=2)+'\n');(E/'GUARD-RECEIPTS10.json').write_text(json.dumps(guards,indent=2)+'\n');assert len(fulltypes)==len(guards)==10 and all(g['PASS_compilation'] for g in guards)
source_map=[]
for path in paths:
 a=E/'source/BEFORE70'/(path+'.txt');b=E/'source/PRIVATE-CANDIDATE'/(path+'.txt');c=E/'source/MAC8'/(path+'.txt');source_map.append({'path':path,'current70_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(b.read_bytes()).hexdigest(),'MAC8_sha256':hashlib.sha256(c.read_bytes()).hexdigest(),'candidate_bytes':b.stat().st_size})
(E/'CANDIDATE-SOURCE-MAP8.json').write_text(json.dumps(source_map,indent=2)+'\n');refs=[]
for n in ['MANIFEST.json','REVIEW.md','SHA256SUMS']:
 f=S/n;refs.append({'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size})
(E/'IMMUTABLE-SAFE7-PACKET.json').write_text(json.dumps({'path':str(S),'payloads':285,'files':refs},indent=2)+'\n')
text=f'''# FH existing-reader repair supplement: candidate scope ten

Current committed source at preflight is {pin['HEAD']} (parent {pin['parent']}); whole MAC8 input is {pin['MAC8_source']}. All candidate changes are private. This agent changed no actual source or Git state.

Recommend the seven current PASS roots9/16/18/19/33/85/86 plus privately repaired17/47/54. Remaining roots50/51/52/58/82/83/84 stay HOLD and are proposed to return to exact MAC8 source. All17 original dispositions remain explicit. No new API/import/statement/name/home/route/debt ruling or mathematical fill is implemented. Final adoption/commit/replay/audit remain root/Seyoon-owned.

Actual private results:
-47 ConfigCount: native prefix through complete proof PASS; fresh6 heads; full guard6 PASS. Existing spaceUsedByTape_eq_card and mem_visitedByTapeHead_iff replace the foreign definitional reads.
-17 Nondeterminism: native prefix PASS; fresh12 heads; full guard12 PASS. Stronger source-reader guard13 additionally hides Cfg.init and erases its definition simp row, and passes. Compiled metadata stays honestly12. Explicit foreign defs become published VirtualTag_iff/initCfg_eq/Cfg.init_inputPos readers.
-54 ClockMachine: native prefix PASS; fresh7 heads; full guard7 PASS. Existing initCfg_eq/Cfg.init field readers, functional extensionality and Cfg.ext reconstruct the final initialization equality. Only own ctrCfg/local start are unfolded. Mechanical colleague-file FYI is Seyoon's to send, without an @mention.

Each native execution has exit0/errors0/sorry0. Fresh full compiled root type Expr and universe parameters are exactly unchanged from current70. All literal headers are exact. Full types/pretty types/axiom sets, complete private owner files for all8 proposed owners, exact old/new3 chunks, full prefixes, metadata, helper/input sources and raw output logs are retained. Candidate native checks compile the original full preceding context and complete target prefix, not subsequent owner declarations. Original14 full-owner passes apply to70, not these private candidates; root's final full downstream replay is still required.

All10 candidate complete scopes pass their foreign-TCSlib-head guards and explicit argument review. Method and limits match safe7: full root type/proof mentions, all mentioned constant types, own ordinary helper values; no imported theorem proof values or foreign definition values. Projections/kernel abbreviations are excluded; Core/Mathlib explicit arguments reviewed separately. No foreign/Core definition argument is present in the candidate chunks.

Retained-ten union22 heads:44 actual positive controls are kernel checked;44 paired sealed controls fail at rfl with exactly44 expected errors and complete markers. Both sides disable smart unfolding for direct recursive runWith/body delta identities and remove Cfg.init/MultiTapeTM.initCfg definition simp rows. No transparency override. Initial42positive/44negative attempt is retained: smart unfolding blocked two runWith reflected identities; this was not a candidate proof failure. Corrected common options are identical and the only source-pair difference is the irreducibility line.

reader-repairs3-over70.patch and proposed-final10-overMAC8.patch are unapplied proposals. Full source recovery/hashes retained. Immutable safe7 and earlier710 packets remain untouched. No full replay, screen, source/canonical mutation or gate closure is claimed.

Reused guard generator's fixed historical 'Prepared17' print appears for one-root invocations; actual input lists and receipts each contain one target, with scopes6/12/13/7. No17 new private checks are claimed.

Frozen UTC: {datetime.datetime.now(datetime.timezone.utc).isoformat()}
''';(E/'REVIEW.md').write_text(text)
files=sorted(f for f in E.rglob('*') if f.is_file());assert not any(f.is_symlink() or f.name.endswith('.lean') for f in E.rglob('*'));manifest=[{'path':str(f.relative_to(E)),'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in files];(E/'MANIFEST.json').write_text(json.dumps({'payloads':len(manifest),'bytes':sum(r['bytes'] for r in manifest),'files':manifest},indent=2)+'\n');(E/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in manifest));print(json.dumps({'export':str(E),'payloads':len(manifest),'bytes':sum(r['bytes'] for r in manifest),'review_sha256':hashlib.sha256((E/'REVIEW.md').read_bytes()).hexdigest(),'manifest_sha256':hashlib.sha256((E/'MANIFEST.json').read_bytes()).hexdigest(),'sha256sums_sha256':hashlib.sha256((E/'SHA256SUMS').read_bytes()).hexdigest(),'repairs3_patch_sha256':hashlib.sha256((E/'reader-repairs3-over70.patch').read_bytes()).hexdigest(),'proposed10_patch_sha256':hashlib.sha256((E/'proposed-final10-overMAC8.patch').read_bytes()).hexdigest()},indent=2))
