from pathlib import Path
import json,hashlib,re,subprocess,collections,datetime,ast
O=Path(__file__).parent;C=json.loads((O/'CONTEXT.json').read_text());R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');W=Path(C['private_source_tree']);S=Path(C['whole_input_snapshot']);OV=Path(C['private_complete_clone']);G=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest()
def write(n,v):(O/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
def metadata(tag):
 d={'SELECTED':{},'BOUNDARY':{}}
 for line in (O/'runs'/tag/'raw.out').read_text().splitlines():
  for mark in d:
   prefix=mark+'|'
   if prefix in line:
    row=json.loads(line.split(prefix,1)[1]);d[mark][row.get('name',row.get('root'))]=row
 return d
base=metadata('BASE-normalized-metadata');owner=metadata('OWNER-metadata');sim=metadata('CANDIDATE-normalized-metadata');prior=metadata('BASE-metadata-v2');earlier=metadata('SIMULATION-metadata');root='Turing.Action.apply_workTapes';consumer='Turing.FinTM.controlAction_apply'
for name in base['SELECTED']:
 assert all(prior['SELECTED'][name][k]==base['SELECTED'][name][k] for k in prior['SELECTED'][name])
 assert all(earlier['SELECTED'][name][k]==sim['SELECTED'][name][k] for k in earlier['SELECTED'][name])
 assert base['SELECTED'][name]['typeExpr_canonicalLevelParameters']==sim['SELECTED'][name]['typeExpr_canonicalLevelParameters']
assert base['SELECTED'][consumer]==sim['SELECTED'][consumer]
assert base['BOUNDARY'][root]['ordinary_foreign_heads']==['Turing.Action.apply','Turing.Cfg.workTapeSymbols']
assert owner['BOUNDARY'][root]['ordinary_foreign_heads']==sim['BOUNDARY'][root]['ordinary_foreign_heads']==[]
attrs=['name','nameCount','kind','private','internal','typeIsProp','unsafe','partial','reducibility','simp','unfold','protected','instancePriority','axioms'];assert all(base['SELECTED'][root][k]==sim['SELECTED'][root][k] for k in attrs)
assert base['SELECTED'][root]['levelParams']==['u_1','u_2'] and sim['SELECTED'][root]['levelParams']==['u_3','u_4']
assert base['SELECTED'][root]['owner']=='TCSlib.Complexity.TuringMachine.Simulation';assert sim['SELECTED'][root]['owner']=='TCSlib.Complexity.TuringMachine.Configuration'
for tag,d in [('BASE',base),('OWNER',owner),('SIMULATION',sim)]:write('SELECTED-'+tag+'.json',d)
write('SELECTED-CHECKS.json',{'source':C['source'],'reader':root,'representative_Simulation_consumer':consumer,'checked_exact_metadata_fields':attrs,'all_checked_fields_literal_equal':True,'full_type_Expr_exact_after_Lean_executed_universe_parameter_canonicalization':True,'literal_level_parameter_names_equal':False,'BASE_level_parameters':['u_1','u_2'],'CANDIDATE_level_parameters':['u_3','u_4'],'moved_reader_owner_only_intentional_module_change':['TCSlib.Complexity.TuringMachine.Simulation','TCSlib.Complexity.TuringMachine.Configuration'],'source_complete_doc_name_statement_proof_byte_exact':True,'literal_compiled_proof_Expr_equal':False,'compiled_proof_after_level_canonicalization_has_only_five_lambda_binder_name_differences':True,'compiled_proof_alpha_comparison':'COMPILED-PROOF-ALPHA-BOUNDARY.json','representative_consumer_full_metadata_type_value_literal_exact':True,'source_and_environment_reader_name_counts_BASE_and_CANDIDATE_all_one':True})
write('RULE10-FOOTPRINT.json',{'reader':root,'BASE_owner':'TCSlib.Complexity.TuringMachine.Simulation','BASE_ordinary_foreign_heads':base['BOUNDARY'][root]['ordinary_foreign_heads'],'CANDIDATE_owner':'TCSlib.Complexity.TuringMachine.Configuration','CANDIDATE_ordinary_foreign_heads':[],'CANDIDATE_definitions_read_by_explicit_simp_arguments':[{'name':'Turing.Action.apply','owner':'TCSlib.Complexity.TuringMachine.Configuration','same_file_after_move':True},{'name':'Turing.Cfg.workTapeSymbols','owner':'TCSlib.Complexity.TuringMachine.Configuration','same_file_after_move':True}],'source_proof_argument_rows':[{'source':'simp [Action.apply, hw, Cfg.workTapeSymbols]','definition_arguments':['Turing.Action.apply','Turing.Cfg.workTapeSymbols'],'local_hypothesis_arguments':['hw']},{'source':'simp [Action.apply, hw]','definition_arguments':['Turing.Action.apply'],'local_hypothesis_arguments':['hw']}],'foreign_TCSlib_definition_values_traversed':False,'other_theorem_proof_values_traversed':False,'Configuration_has_no_TCSlib_imports':True,'guard_controls_required_for_selected_moved_reader':0,'seal_execution_claimed':False,'zero_guard_reason':'The owner-native selected-reader footprint has zero ordinary foreign TCSlib heads. Both explicit unfolded definitions are same-file after this exact proposed move. No seal/control execution is invented for an empty guard population.','Simulation_consumer_is_unchanged_and_imports_moved_theorem':True,'consumer_footprint_boundary':'The consumer statement/type traversal still mentions imported Action.apply, moveInputPos and Cfg.workTapeSymbols through published theorem types. Its proof bytes and compiled metadata remain exact; this proposal does not claim to clear every pre-existing Simulation Rule10 read.'})
# Source tree/freeze verification including all old owner text and full source population.
rows=[]
for raw in G('ls-tree','-r','-z',C['source'],'--','TCSlib','TCSlib.lean').split(b'\0'):
 if not raw:continue
 spec,path=raw.split(b'\t',1);mode,kind,oid=spec.split();path=path.decode()
 if kind!=b'blob' or not path.endswith('.lean'):continue
 b=(W/path).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();changed=blob!=oid.decode()
 if changed:
  expected=(O/'source'/'CANDIDATE'/(path+'.txt')).read_bytes();assert b==expected
 rows.append({'path':path,'source_Git_blob':oid.decode(),'actual_private_git_blob':blob,'actual_private_SHA256':H(b),'proposal_changed':changed})
assert len(rows)==930;changed=[r['path'] for r in rows if r['proposal_changed']];assert changed==['TCSlib/Complexity/TuringMachine/Configuration.lean','TCSlib/Complexity/TuringMachine/Simulation.lean']
write('SOURCE930-private-final.json',rows)
all_source=[]
for raw in G('ls-tree','-r','-z',C['source']).split(b'\0'):
 if not raw:continue
 spec,path=raw.split(b'\t',1);mode,kind,oid=spec.split();path=path.decode()
 if kind==b'blob' and path.endswith('.lean'):all_source.append({'path':path,'Git_blob':oid.decode(),'in_extracted_TCSlib_source_population':path.startswith('TCSlib/') or path=='TCSlib.lean'})
assert len(all_source)==1003
write('SOURCE1003-current-Git-bindings.json',all_source)
objects=[]
for f in sorted(S.rglob('*.olean')):objects.append({'path':str(f.relative_to(S)),'bytes':f.stat().st_size,'SHA256':H(f.read_bytes())})
assert objects==json.loads((O/'INPUT895-original-before.json').read_text());write('INPUT895-original-after.json',objects)
output=[]
for f in sorted(OV.rglob('*.olean')):output.append({'path':str(f.relative_to(OV)),'bytes':f.stat().st_size,'SHA256':H(f.read_bytes())})
assert len(output)==895;old={r['path']:r for r in objects};new={r['path']:r for r in output};assert set(old)==set(new);changed_objects=[p for p in old if old[p]!=new[p]];assert changed_objects==['TCSlib/Complexity/TuringMachine/Configuration.olean','TCSlib/Complexity/TuringMachine/Simulation.olean'];write('OUTPUT895-private-final.json',output)
write('OBJECT-CHECKS.json',{'physical_input_original_before_after_exact':True,'input_physical_olean_count':895,'private_clone_all_895_exact_before_first_check':True,'output_physical_olean_count':895,'same_complete_object_path_population':True,'only_changed_private_objects':changed_objects,'other_893_objects_byte_exact_input':True,'candidate_phase_objects_restored_byte_exact_after_normalization_comparison':True,'original_snapshot_written':False,'runtime':C['runtime']})
# Receipts include the superseded metadata-parser failure as an explicit disposition.
runs=[]
for d in sorted((O/'runs').iterdir()):
 if not d.is_dir():continue
 r=json.loads((d/'run.json').read_text());out=(d/'raw.out').read_text();assert 'setpriority' not in out and 'Operation not permitted' not in out
 r['disposition']='Superseded metadata probe syntax failure: reserved identifier matches was changed to nameHits; library baseline native check passed and every final probe passed.' if r['actual_exit'] else 'Completed bounded native/metadata/explicit-argument check.'
 if r['actual_exit']:assert d.name=='BASE-metadata' and r['actual_exit']==1
 runs.append(r)
assert sum(r['actual_exit']==0 for r in runs)==10 and len(runs)==11;write('ACTUAL-RUN-INDEX.json',runs)
warning=(O/'runs/03-OWNER-Configuration-native/raw.out').read_text();nums=[int(m.group(1)) for m in re.finditer(r'Configuration\.lean:(\d+):\d+: warning:',warning)];assert nums==[157,160,175]
basecfg=(O/'source/BASE/TCSlib/Complexity/TuringMachine/Configuration.lean.txt').read_text();candcfg=(O/'source/CANDIDATE/TCSlib/Complexity/TuringMachine/Configuration.lean.txt').read_text();assert basecfg.splitlines()[:261]==candcfg.splitlines()[:261]
write('WARNINGS-DISPOSITION.json',{'candidate_Configuration_warning_lines':nums,'all_in_unchanged_source_prefix_before_insertion':True,'prefix_lines_1_through_261_byte_equal':True,'warning_text':warning,'fresh_BASE_Configuration_source_run_claimed':False,'metadata_initial_syntax_failure_retained':True,'final_probes_zero_errors':True})
now=G('rev-parse','origin/pr/251^{commit}').decode().strip();G('cat-file','-e',now+'^{commit}');assert now==C['source']
summary={'source':C['source'],'frozen_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proposal':'Exact existing Turing.Action.apply_workTapes chunk moved from Simulation to Configuration, preserving imports and all other old owner text.','candidate_native_Configuration_pass':True,'candidate_native_full_Simulation_pass':True,'baseline_current_Simulation_native_pass':True,'owner_native_explicit_generic_arguments_pass':True,'selected_type_alpha_exact':True,'AX_privacy_checked_attributes_literal_exact':True,'selected_reader_foreign_ordinary_heads_BASE_CANDIDATE':[2,0],'selected_source_and_environment_name_count':1,'raw_compiled_Expr_identity_claimed':False,'automatic_universe_and_lambda_binder_name_differences_fully_retained':True,'representative_Simulation_consumer_full_metadata_exact':True,'tracked_all_Lean_Git_binding_count':1003,'private_extracted_TCSlib_source_count':930,'private_extracted_TCSlib_sources_only_two_files_changed':True,'whole_MAC8_original895_objects_unchanged':True,'private_complete_output895_only_two_objects_changed':True,'successful_checks':10,'superseded_metadata_syntax_attempts':1,'Lean_runs_sequential_one_own_process_with_verified_nice10_j4_helpers_shared_local3_locks':True,'full_downstream_replay_or_copy_screen_run':False,'checkout_source_Git_R_X_adoption_mutation_or_decision':False,'needs_Seyoon_home_change_ruling':True,'retained_stale_Configuration_header_prose_disclosed':True};write('RECEIPT.json',summary)
(O/'PROPOSAL.md').write_text('''# Exact Action.apply_workTapes home-move feasibility

The bounded private proposal is feasible: move the existing complete `Turing.Action.apply_workTapes` doc/name/statement/proof chunk from `Simulation.lean` beside `Action.apply` in `Configuration.lean`. `PROPOSED-EXACT-MOVE.patch` is the concrete candidate against actual #251 source `0f926779de590194f5222277dc038d2ad097ff91`. This has **not** been adopted in any checkout; the home change needs Seyoon’s ruling.

An inverse move recovers every byte of both original files. Imports, old headers, definitions, attributes, every other proof, and the now-empty `namespace Turing` wrapper in Simulation are preserved. The reader has one source declaration and one environment entry; no alias or duplicate is retained. The unchanged Configuration header/API prose still says the work-tape equation is in Simulation. That stale prose is deliberately disclosed and left intact under the exact-preservation constraint.

The actual current Simulation baseline compiles. The exact candidate Configuration compiles with its existing imports, and the full candidate Simulation compiles after importing that equation from Configuration. A fully explicit generic `@Turing.Action.apply_workTapes k Symbol State input a c i` use passes in the Configuration-only import context. The other three TCSlib modules in Simulation’s four-module import closure match MAC8 sources exactly; no import is added.

The complete selected type is exact after Lean-executed canonicalization of automatic universe parameters. Source context changes their generated names `u_1/u_2` to `u_3/u_4`; literal raw `typeExpr`/level-name equality is **not** claimed. The exact source proof is preserved. After universe canonicalization, the compiled proof differs at exactly five lambda binder Name fields (module hygiene labels/counters); all other expression data matches. Full raw values and the complete 3.7 KB diff are retained in the metadata and `COMPILED-PROOF-DIFF.txt`, with the explicit alpha boundary in JSON.

AX remains exactly `[propext, Classical.choice, Quot.sound]`. The declaration remains a public safe theorem, non-simp, non-unfold, unprotected and non-instance, with one name entry. All checked kind/privacy/reducibility/attribute metadata is literal-equal. The representative existing Simulation consumer `Turing.FinTM.controlAction_apply` retains its entire compiled metadata, type and proof expression exactly while consuming the moved equation.

The selected reader’s ordinary foreign TCSlib footprint falls from the two Configuration definitions `Action.apply` and `Cfg.workTapeSymbols` to zero, since both are now same-file. Those are also its only explicit definition arguments in the two simp calls; `hw` is a local hypothesis. No foreign definition or other theorem proof value was traversed by the footprint check. The empty ordinary-foreign guard population requires zero controls; no seal execution is invented. This does not assert that every pre-existing Simulation proof meets Rule10.

All Lean work was sequential, one own process at a time, through the verified approved helpers (`nice -n10`, `lean -j4`, shared local3/machine5 lock discipline) in one complete cloned MAC8 tree. All895 original objects are byte-identical before/after; the private complete895 output changes only Configuration/Simulation objects. Ten final native/metadata/argument checks pass. One initial metadata syntax failure using the reserved identifier `matches` is preserved and explicitly superseded. Three Configuration linter warnings occur in its unchanged prefix before the insertion; no fresh BASE-Configuration run is claimed for those warnings.

This is a bounded source/context proposal. No full downstream replay, copy screen, gate clearance, source adoption, Git/R/X mutation, commit, push, dispatch, design or debt decision was performed. The files contain complete selected metadata, explicit arguments, source/import/object bindings and execution receipts for review.
''')
print(json.dumps(summary,indent=2))
