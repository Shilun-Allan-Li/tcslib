from pathlib import Path
import json,hashlib,re
OUT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((OUT/'context.json').read_text())
before=(OUT/'Encoding-before.lean.txt').read_text();after=(OUT/'Encoding-after.lean.txt').read_text()
start=after.index('/-- The diagonal pairing machine uses zero work-tape space on every input at every time.')
end=after.index('/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/',start)
added=after[start:end]
assert after[:start]+after[end:]==before
assert added.count('theorem ')==1 and 'private' not in added and '@[simp]' not in added
assert 'theorem pairDiagTM_spaceUsed (x : List Bool) (t : ℕ) :\n    pairDiagTM.tm.spaceUsed (pairDiagTM.tm.initCfg x) t = 0 := by\n  exact MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl' in added
assert sha(Path(c['owned_source']))==c['after_sha256']==sha(OUT/'Encoding-after.lean.txt')
assert len(re.findall(r'\bsorry\b',before))==len(re.findall(r'\bsorry\b',after))==1
assert not re.search(r'\b(sorry|admit|unsafe|unfold)\b',added)
assert [l for l in before.splitlines() if l.startswith('import ')]==[l for l in after.splitlines() if l.startswith('import ')]
sealed=(OUT/'Owner-sealed.lean.txt').read_text();native=(OUT/'Owner-native.lean.txt').read_text()
owner_guard=(OUT/'owner-guard.txt').read_text();consumer_guard=(OUT/'consumer-guard.txt').read_text()
clean=sealed.replace(owner_guard,'').replace('end PairDiagSpaceOwnerSeal\n','').replace('\n'+consumer_guard,'')
assert clean==native
assert sealed.index(owner_guard)<sealed.index('/-- The diagonal pairing machine uses zero work-tape space')
raw=(OUT/'Owner-sealed.out').read_text();roots=re.findall(r'^ROOT\|([^|]+)\|private=(\w+)',raw,re.M)
axs=[{'name':n,'kind':k,'axioms':[x.strip() for x in a.split(',') if x.strip()]} for n,k,a in re.findall(r'^PROOFAX\|([^|]+)\|kind=([^|]+)\|\[([^\]]*)\]',raw,re.M)]
assert len(roots)==2 and len(axs)==2
assert {n for n,_ in roots}=={r['name'] for r in axs}
assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in axs)
foreign=[dict(zip(['root','name','owner','hints'],x)) for x in re.findall(r'^FOREIGNDEF\|([^|]+)\|([^|]+)\|([^|]+)\|hints=(\w+)$',raw,re.M)]
regular=sorted({r['name'] for r in foreign if r['hints']=='regular'});assert regular==['Turing.MultiTapeTM.initCfg','Turing.MultiTapeTM.spaceUsed']
for name in ['Owner-native','Owner-sealed']:
 r=json.loads((OUT/(name+'-run.json')).read_text());assert (r['exit'],r['errors'])==(0,0)
assert json.loads((OUT/'control-check.json').read_text())['pointwise_and_abstracted_pairs']==8
snap=json.loads((OUT/'snapshot-inputs.json').read_text())
for rel,r in snap['modules'].items():assert sha(Path(snap['snapshot'])/rel)==r['sha256']
attempts=[]
for p in sorted(OUT.glob('*-run.json')):
 r=json.loads(p.read_text());name=p.name.removesuffix('-run.json');text=(OUT/(name+'.out')).read_text()
 attempts.append({'name':name,**{k:r[k] for k in ['exit','errors','seconds','input_sha256','output_sha256']},'warnings':len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M))})
result={'status':'One approved source theorem implemented; bounded native/seal/control checks pass; not integrated replay/gate clearance','one_source_addition_only_removal_reconstructs_before':True,'imports_existing_source_bytes_and_machine_table_frozen':True,'production_new_theorems':1,'production_new_helpers':0,'production_new_imports':0,'production_new_simp_attributes':0,'owner_foreign_regular_defs':regular,'conservative_additional_guard':'Turing.Cfg.init','same_home_machine_read':'pairDiagTM k=0 by rfl only in approved owner proof; actual consumer seals pairDiagTM','public_projection_abbrevs':sorted({r['name'] for r in foreign if r['hints']=='abbrev'}),'roots':roots,'axiom_roots_and_descendants':axs,'new_source_root_descendants':0,'consumer_root_descendants':0,'all_selected_standard_axioms':True,'exact_guard_removal_native_identity':True,'actual_source_after_sha256':c['after_sha256'],'actual_source_stable_at_check':True,'baseline_raw_sorry_tokens':1,'after_raw_sorry_tokens':1,'inherited_admission':'Turing.pairDiagTM_computes; source line507→514; new theorem/consumer do not depend on sorryAx','attempts':attempts,'failed_proof_attempts':0,'expected_negative_control_errors':8,'no_explicit_foreign_definition_unfold_arguments':True,'no_snapshot_compiledoutput_Git_commit_push_changes':True}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'foreign-inventory.json').write_text(json.dumps(foreign,indent=2)+'\n')
print(json.dumps({'actual_source_sha256':c['after_sha256'],'new_root_axioms':axs[0]['axioms'],'roots':len(roots),'descendants':0,'raw_sorry_before_after':[1,1],'attempts':len(attempts)},indent=2))
