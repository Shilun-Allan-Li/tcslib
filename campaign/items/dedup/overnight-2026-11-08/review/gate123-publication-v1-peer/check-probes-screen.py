import hashlib,json,re
from pathlib import Path
B=Path('/private/tmp/ab34-gate123-publication-peer');Q=B/'records-inputs/campaign/gates/123-ch7-run/review';ROOT=B/'records-inputs';G=ROOT/'campaign/gates/123-ch7-run'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def read(p):return json.loads((Q/p).read_text())
def write(name,value):(B/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
# Frozen315 transport: manifest contents are data, verify every row independently.
m=read('MANIFEST.json');assert len(m['files'])==315
for row in m['files']:
 p=Q/row['path'];raw=p.read_bytes();assert len(raw)==row['bytes'] and sha(raw)==row['sha256']
assert sha((Q/'MANIFEST.json').read_bytes())==json.loads((G/'adoption.json').read_text())['review_manifest_sha256']
# Reparse every ABI line, compare unnormalized full records to derived selected captures.
records={};all_meta=[]
probe_sha=sha((Q/'selected-metadata-probe.lean.txt').read_bytes());objs={'BASE':read('replay/input-before.json'),'HEAD':read('replay/output.json')};owner='TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.olean'
for side in ['BASE','HEAD']:
 raw=(Q/'metadata'/f'{side}.log').read_bytes();text=raw.decode();run=read(f'metadata/{side}-run.json');request=read(f'metadata/{side}-request.json');capture=read(f'metadata/{side}-selected.json')
 assert run['exit']==run['errors']==run['warnings']==0 and run['roots_observed']==5 and run['complete_marker_exact']
 assert sha(raw)==run['raw_sha256'] and len(raw)==run['raw_bytes'] and run['probe_source_sha256']==request['source_probe_sha256']==probe_sha
 assert request['complete_snapshot_owner_object_before_sha256']==objs[side][owner]
 roots=[json.loads(line.split('ABI|',1)[1]) for line in text.splitlines() if 'ABI|' in line];aux=[json.loads(line.split('TYPE_AUX|',1)[1]) for line in text.splitlines() if 'TYPE_AUX|' in line]
 assert roots==capture['roots'] and aux==capture['private_type_auxiliaries']==[] and len(roots)==5 and text.count('COMPLETE|5')==1
 assert all(not r['private'] and r['kind']=='theorem' and r['axioms']==['propext','Quot.sound'] and not r['simp_lemma'] and not r['simp_unfold'] and '...' not in r['full_type_Expr_repr'] for r in roots)
 records[side]=roots;all_meta.append({'phase':side,'raw_log_SHA256':sha(raw),'raw_records_exact_capture':True,'5_public_roots':True,'private_type_auxiliaries':0,'owner_object_SHA_bound_to_whole895_map':True,'allAX':['propext','Quot.sound'],'all_simp_flags':False})
assert records['BASE']==records['HEAD'];assert len(read('selected-ABI-comparison.json')['rows'])==5
write('ABI-CHECK.json',{'scope':'Only the five public selected declarations; no whole-private/global/proof-value claim','all5_raw_Expr_and_full_record_exact':True,'raw_Expr_not_pretty_printed_or_width_limited':True,'universe_names_kernel_owner_typeconstants_privacy_kind_simp_AX_exact':True,'sides':all_meta})
# Full literal scopes; recorded logs and controls only, no new Lean execution.
d=Q/'inputs/ch7-full-five-scopes-v2';src=read('inputs/ch7-full-five-scopes-v2/SOURCE.json');res=read('inputs/ch7-full-five-scopes-v2/RESULTS.json');log=(d/'Inventory.log').read_text();guards=json.loads(re.search(r'^GUARDS\|(.+)$',log,re.M)[1]);simp=json.loads(re.search(r'^SIMPDEFS\|(.+)$',log,re.M)[1])
assert guards==src['guards'] and simp==src['default_simp_removed']==['Turing.Action.apply'] and len(guards)==6
for row in res:
 assert sha((d/(row['name']+'.lean.txt')).read_bytes())==row['input_sha256'];assert sha((d/(row['name']+'.log')).read_bytes())==row['log_sha256']
 assert row['pass'] and row['exit']==row['expected_exit'] and row['errors']==row['expected_errors'] and row['sorry']==0
native=(d/'ControlsNative.log').read_text();sealed=(d/'ControlsSealed.log').read_text();positive=re.findall(r'^CONTROL\|([^|]+)\|(point|abstract)\|PASS\|kernelChecked=(Ch7RunControl_\d+_(?:point|abstract))$',native,re.M);negative=re.findall(r'^CONTROL\|([^|]+)\|(point|abstract)\|FAIL$',sealed,re.M)
expect=[(n,mode) for n in guards for mode in ['point','abstract']];assert [(n,mode) for n,mode,_ in positive]==negative==expect;assert len(set(n for _,_,n in positive))==12;assert sealed.count('error:')==12 and 'PASS' not in sealed
for f in ['ScopeNative.lean.txt','ScopeSealed.lean.txt','ControlsNative.lean.txt','ControlsSealed.lean.txt']:
 text=(d/f).read_text();assert text.count('attribute [-simp] Turing.Action.apply')==1;assert ('allowUnsafeReducibility' not in text)
 if 'Sealed' in f:
  line=re.search(r'^attribute \[local irreducible\] (.+)$',text,re.M)[1];assert line.split()==guards
inv=(d/'Inventory.lean.txt').read_text();assert '.thmInfo _' in inv and 'pending := pending ++ info.type.getUsedConstants' in inv and 'pending := pending ++ d.type.getUsedConstants ++ d.value.getUsedConstants' in inv
scopeAX=re.findall(r"^'([^']+)' depends on axioms: \[([^]]*)\]$",(d/'ScopeSealed.log').read_text(),re.M);assert [x[0] for x in scopeAX]==src['roots'] and all(x[1]=='propext, Quot.sound' for x in scopeAX)
for name,chunk in src['complete_literal_chunks'].items():
 proof=chunk.split(':= by',1)[1]
 assert not re.search(r'\b(?:unfold|delta)\b',proof)
 for m in re.finditer(r'\b(?:simp(?:a)?(?:\s+only)?|rw)\s*\[([^]]*)\]',proof):
  args=m.group(1);assert all(g not in args for g in guards)
write('BOUNDARY-CHECK.json',{'six_guard_union_exact_recorded_inventory':guards,'full5_literal_scopes_exact_HEAD':'SOURCE-CHECK.json','Action_apply_default_simp_removed_all4_variants':True,'all5_source_log_receipt_hashes_exact':True,'positive12_exact_unique_kernel_checked_identities':True,'negative12_exact_same_identity_pairs_fail_intended_refl':True,'sealed_scope_exit0_error0_sorry0':True,'selected5_sealed_AX_standard':True,'foreign_definition_values_and_types_traversed':True,'imported_theorem_types_only_proof_values_not_traversed':True,'projection_abbrev_exclusions_explicit':True,'no_explicit_guard_unfold_argument_in_five_changed_proofs':True,'limits':'No whole-owner seal or proof-value/type equality; unchanged Bool runFrom_one/RO1 separate'})
# Raw screen rows independently compared by directed identity, source/helper binding against captured bytes.
pop=(Q/'screen-population.txt').read_text().splitlines();assert len(pop)==len(set(pop))==33;phase_rows={};phase_summary=[]
for side,rf,rr,rq in [('BASE','screen/BASE/screen-BASE.txt','screen/BASE/RESULT.json','screen/BASE/screen-BASE-request.json'),('HEAD','screen/HEAD.txt','screen/HEAD-RESULT.json','screen/HEAD-request.json')]:
 req=read(rq);run=read(rr);raw=(Q/rf).read_bytes();text=raw.decode();assert req['population']==pop and run['exit']==0 and run['bytes']==len(raw) and run['sha256']==sha(raw)
 for p in pop:
  capture=(Q/'source'/side/(p+'.txt')).read_bytes();assert sha(capture)==req['source_sha256'][p]
  if side=='HEAD':assert capture==(ROOT/p).read_bytes()
 match=re.match(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',text);assert match
 pairs=re.findall(r'^\s*(\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%$',text,re.M);assert len(pairs)==int(match[2])
 pairmap={(t,s):{'matched':int(m),'source_tokens':int(n),'percent':int(pc)} for t,s,m,n,pc in pairs};assert len(pairmap)==len(pairs)
 phase_rows[side]=pairmap;phase_summary.append({'side':side,'decl_extraction_count':int(match[1]),'directed_pairs':int(match[2]),'reproduced_chars':int(match[3].replace(',','')),'actual_exit':run['exit'],'population33_capture_hashes_exact':True,'tool_SHA256':req['tool_sha256']})
assert phase_summary[0]['tool_SHA256']==phase_summary[1]['tool_SHA256']
new=set(phase_rows['HEAD'])-set(phase_rows['BASE']);gone=set(phase_rows['BASE'])-set(phase_rows['HEAD']);delta=read('screen/pair-delta.json');disp=read('screen/pair-dispositions.json');assert new==set() and len(gone)==2;assert gone=={(x['target'],x['source']) for x in delta['gone']}=={(x['target'],x['source']) for x in disp['BASE_only_rows']};assert delta['new']==disp['new_pair_rows']==[]
for row in delta['gone']:assert {k:row[k] for k in ['matched','source_tokens','percent']}==phase_rows['BASE'][(row['target'],row['source'])]
write('SCREEN-CHECK.json',{'exact33_population_two_sides':True,'raw_actual_stats_and_hashes':phase_summary,'new_directed_pairs':len(new),'BASE_only_directed_pairs':sorted(gone),'all_two_gone_rows_and_empty_new_dispositions_exact':True,'comparison_scope':'Directed identity only; persistent ratios retained raw; not Lean interface or semantic/global debt absence','screen_helper_code_not_in_bundle':True,'screen_helper_SHA256':phase_summary[0]['tool_SHA256']})
# Lint claims are raw comparison only, not fabricated exit receipts.
assert (Q/'qa/BASE-style-lint.txt').read_bytes()==(Q/'qa/HEAD-style-lint.txt').read_bytes()
base=(Q/'qa/BASE-campaign-lint.txt').read_text();head=(Q/'qa/HEAD-campaign-lint.txt').read_text();assert base.replace('EmitIterEmbed.lean                  326 lines','EmitIterEmbed.lean                  295 lines')==head
assert read('qa/BASE-sizes.json')=={'TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean':326};assert read('qa/HEAD-sizes.json')=={'TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean':295}
write('LINT-RAW-CHECK.json',{'style_stdout_exact':True,'sole_campaign_stdout_delta_owner326_to295':True,'sizes_exact326_to295':True,'new_lint_command_or_exit_receipt_not_claimed':True,'actual_lint_helper_code_missing_bundle':True})
print('ABI/control/screen/raw-lint checks PASS; full315 payload hashes exact. Helper-source and MAC8 anchor bundle gaps remain, plus minor canonical relative-path typo.')
