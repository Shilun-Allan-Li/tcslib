"""Read-only reconciliation of our actual source, raw native logs and paired controls."""
from pathlib import Path
import datetime, hashlib, json, re
out=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
write=lambda n,v:(out/n).write_text(json.dumps(v,indent=2)+'\n')
context=json.loads((out/'context.json').read_text())
source=Path(context['worktree'])/'TCSlib/Complexity/TuringMachine/Finite.lean'
actual=(out/'actual-Finite.lean.txt').read_bytes()
before=(out/'before-Finite.lean.txt').read_bytes()
insert=(out/'inserted-approved-theorem.lean.txt').read_bytes()
assert source.read_bytes()==actual
assert actual.count(insert)==1 and actual.replace(insert,b'',1)==before
assert H(actual)=='e870a56d345d53969a7fa1cd2741476f9f076c517812ce20cea0c0f81b1b59be'
for name in ['Actual-module','Finite-newsection-sealed','Metadata','Controls-unsealed','Controls-sealed']:
 r=json.loads((out/(name+'-run.json')).read_text())
 assert r['input_source_stable'] and H((out/(name+'.out')).read_bytes())==r['output_sha256']
 assert H(Path(r['input_path']).read_bytes())==r['input_sha256']
 assert r['exit']==(1 if name=='Controls-sealed' else 0)
 assert r['errors']==(8 if name=='Controls-sealed' else 0)
sealed=(out/'Controls-sealed.lean.txt').read_text()
unsealed=(out/'Controls-unsealed.lean.txt').read_text()
guard='attribute [local irreducible] Turing.MultiTapeTM.step Turing.MultiTapeTM.runFrom\n'
assert sealed.count(guard)==1 and sealed.replace(guard,'',1)==unsealed
for text in [sealed,unsealed]:
 assert 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg' in text
starts=[i for i,l in enumerate(sealed.splitlines(),1) if l.startswith('example')]
assert len(starts)==8
ends=[n-1 for n in starts[1:]]+[len(sealed.splitlines())]
raw=(out/'Controls-sealed.out').read_text()
diags=[]
pattern=r'^([^\n]+\.lean):(\d+):(\d+): error(?:\([^)]*\))?: ([^\n]*)'
for m in re.finditer(pattern,raw,re.M):
 line=int(m[2]);owners=[i for i,(a,b) in enumerate(zip(starts,ends)) if a<=line<=b]
 assert len(owners)==1 and m[4].startswith('Tactic `rfl` failed:')
 diags.append({'line':line,'column':int(m[3]),'control_index':owners[0]+1,'message':m[4]})
labels=[('step','pointwise_delta'),('step','abstracted_delta'),('step','pointwise_whole_equation'),('step','abstracted_whole_equation'),('runFrom','pointwise_delta'),('runFrom','abstracted_delta'),('runFrom','pointwise_whole_equation'),('runFrom','abstracted_whole_equation')]
def coverage(ds):return len(ds)==8 and sorted(d['control_index'] for d in ds)==list(range(1,9))
assert coverage(diags)
synthetic=[diags[0]]+diags[:-1]
assert len(synthetic)==len(diags) and not coverage(synthetic)
controls=[{'index':i+1,'definition':'Turing.MultiTapeTM.'+d,'mode':mode,'line_interval':[a,b],'errors':[x for x in diags if x['control_index']==i+1]} for i,((d,mode),a,b) in enumerate(zip(labels,starts,ends))]
write('controls-verification.json',{'unsealed_exit':0,'unsealed_errors':0,'sealed_exit':1,'sealed_errors':8,'exact_inputs_differ_only_by_two_definition_opacity_command':True,'default_three_simp_removals_in_both':True,'each_of_eight_own_intervals_has_one_rfl_diagnostic':coverage(diags),'same_count_synthetic_duplicate_first_drop_last_rejected':not coverage(synthetic),'controls':controls,'unsealed_warning':'Unused lambda-binder S at unchanged control line19; no warning in actual new theorem.'})
meta=(out/'Metadata.out').read_text()
root='Turing.MultiTapeTM.exists_first_entry_of_fixed'
rootline=next(l for l in meta.splitlines() if l.startswith('ROOT|'))
assert rootline==f'ROOT|{root}|owner=TCSlib.Complexity.TuringMachine.Finite|kind=theorem|private=false|internal=false|simp=false|unfold=false'
owner=[]
for l in meta.splitlines():
 if l.startswith('OWNERCI|'):
  fs=l.split('|');owner.append({'name':fs[1],**dict(s.split('=',1) for s in fs[2:])})
assert len(owner)==len({r['name'] for r in owner})
ax=[]
for l in meta.splitlines():
 if l.startswith('AX|'):
  _,n,k,a=l.split('|');axs=a.strip('[]').split(', ') if a!='[]' else []
  assert set(axs)<={'propext','Classical.choice','Quot.sound'}
  ax.append({'name':n,'kind':k.split('=',1)[1],'axioms':axs})
assert len(ax)==1 and ax[0]['name']==root
assert [r['name'] for r in owner if r['name']==root or r['name'].startswith(root+'.')]==[root]
foreign=[]
for l in meta.splitlines():
 if l.startswith('DEF|'):
  _,n,d,home,h=l.split('|');foreign.append({'proof_root':n,'name':d,'owner':home,'hints':h.split('=',1)[1]})
ordinary=[r for r in foreign if r['hints']!='abbrev']
assert {r['name'] for r in ordinary}=={'Turing.MultiTapeTM.step','Turing.MultiTapeTM.runFrom'}
assert [r['name'] for r in foreign if r['hints']=='abbrev']==['Turing.Cfg.state']
write('metadata-verification.json',{'root':root,'home':'TCSlib.Complexity.TuringMachine.Finite','public':True,'internal':False,'simp':False,'unfold':False,'new_root_and_descendants':ax,'descendant_count':0,'foreign_TCSlib_defs_type_and_value':foreign,'all_ordinary_foreign_defs_sealed':True,'projection_abbrev_exclusions':['Turing.Cfg.state'],'unfiltered_Finite_owner_constant_count':len(owner),'unfiltered_nonprivate_count':sum(r['private']=='false' for r in owner),'unfiltered_public_noninternal_count':sum(r['private']=='false' and r['internal']=='false' for r in owner),'owner_constants':owner,'scope':'Compiled owner after our single-module check only; no baseline compiled delta or integrated5module-chain claim.'})
write('tactic-arguments.json',{'scope':'Exact approved new theorem, full source inspection; proof-local equality arguments are permitted.','explicit_rewrite_lists':[['hT'],['hT'],['runFrom_succ_eq_step','hfixed'],['Nat.add_sub_of_le ht','hT','hconst']],'published_equation_or_fact_arguments':['Turing.MultiTapeTM.runFrom_zero','Turing.MultiTapeTM.runFrom_succ_eq_step','Nat.add_sub_of_le'],'proof_local_equalities':['hT','hfixed','hconst'],'other_explicit_operations':'Nat.find chooses a witness; Nat.find_min, Nat.find_min\u0027 and Nat.find_spec are public facts; tm.runFrom_add composes the run. No named foreign definition is passed as a simp/rw/unfold argument.','no_simp_dsimp_unfold_change_delta_transparency_escape_in_new_proof':True,'body_and_header_guarded_before_doc':True,'ordinary_foreign_defs':['Turing.MultiTapeTM.step','Turing.MultiTapeTM.runFrom'],'default_simp_rules_removed':['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg']})
write('final-receipt.json',{'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':str(source),'source_sha256':H(actual),'source_is_exact_saved_actual_bytes':True,'old_source_sha256':H(before),'single_addition':root,'old_bytes_exact_after_removing_only_insertion':True,'approved_header_and_proof_exact':True,'actual_full_module':{'exit':0,'errors':0,'warnings':2,'warning_scope':'Both unused simp arguments hi/hw at untouched oldline178; none in inserted theorem; no fresh baseline-native warning comparison claimed.'},'new_section_strong_seal':{'exit':0,'errors':0,'warnings':2,'ordinary_foreign_defs':2,'default_simp_removals':3,'guard_before_doc_header_body':True},'fresh_paired_controls':{'unsealed_exit':0,'sealed_exit':1,'controls':8,'expected_failures':8,'one_per_interval':True,'same_count_synthetic_mismatch_rejected':True},'actual_owner_metadata':{'exit':0,'errors':0,'warnings':0,'roots':1,'descendants':0,'standard_axioms_only':True,'public_noninternal_non_simp':True},'private_complete_snapshot_context':context,'no_integrated_chain_or_replay_claim':True,'no_other_source_owned_or_edited':True,'no_Git_mutation_commit_push_screen_cache_or_shared_snapshot_output':True,'outstanding_work':'Root will check actual integrated five-module chain, full compiled API delta, merged-tree replay and gate119; these isolated passes do not clear a merge.'})
print(json.dumps({'source_sha256':H(actual),'owner_constants':len(owner),'controls':len(controls),'ordinary_foreign_defs':len(ordinary),'all_assertions_pass':True},indent=2))
