from pathlib import Path
import json,hashlib,re,subprocess,datetime,difflib
O=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup/review/round3-image-repoint')
C=json.loads((O/'context.json').read_text());W=Path(C['worktree'])
sha=lambda b:hashlib.sha256(b).hexdigest()
before=(O/'Tautology-before.lean.txt').read_bytes();after=(W/'TCSlib/Complexity/ClassNP/Tautology.lean').read_bytes()
assert after==(O/'Tautology-proposed.lean.txt').read_bytes()
old=(O/'target-before.lean.txt').read_bytes();new=(O/'target-after.lean.txt').read_bytes();header=(O/'full-header.lean.txt').read_bytes()
assert before.count(old)==after.count(new)==1
assert after.replace(new,old,1)==before
assert header in old and header in new
imports=lambda b:re.findall(rb'^import .*$',b,re.M)
assert imports(before)==imports(after)
meta=(O/'metadata-append.lean.txt').read_bytes()
native=(O/'Tautology-actual-native-v1.lean.txt').read_bytes();sealed=(O/'Tautology-actual-sealed-v1.lean.txt').read_bytes()
assert native==after+meta
ins=json.loads((O/'instrumentation.json').read_text())
guard=ins['guard'].encode();suffix=ins['suffix'].encode()
assert sealed==after.replace(new,guard+new+suffix,1)+meta
names=(O/'guard-definitions.txt').read_text().splitlines();assert len(names)==14
results=[]
metadata={}
for name in ['Hypothetical-native-v1','Hypothetical-sealed-v1','Tautology-actual-native-v1','Tautology-actual-sealed-v1']:
    rr=json.loads((O/(name+'-run.json')).read_text());data=(O/(name+'.out')).read_bytes();text=data.decode()
    assert (rr['exit'],rr['errors'])==(0,0)
    assert sha(data)==rr['output_sha256'] and sha((O/(name+'.lean.txt')).read_bytes())==rr['input_sha256']
    roots=[line.split('|') for line in text.splitlines() if line.startswith('ROOT|')]
    ax=[line.split('|') for line in text.splitlines() if line.startswith('PROOFAX|')]
    defs=[line.split('|') for line in text.splitlines() if line.startswith('FOREIGNDEF|')]
    cited=[line.split('|') for line in text.splitlines() if line.startswith('CITED|')]
    assert len(roots)==len(ax)==1 and roots[0][2]=='private=true'
    assert ax[0][3]=='[propext, Classical.choice, Quot.sound]'
    assert {row[2] for row in defs}=={'Turing.FinTM.ComputesFunInTime','Turing.FinTM.ComputesInTime'}
    assert all(row[2] in names and row[-1]=='hints=regular' for row in defs)
    assert {row[2] for row in cited}=={'Turing.FinTM','Turing.FinTM.ComputesFunInTime','Turing.FinTM.ComputesInTime','Turing.FinTM.exists_comp_on_image'}
    metadata[name]={'roots':roots,'root_and_descendant_axioms':ax,'direct_cited':cited,'direct_foreign_ordinary_definitions':defs,'generated_descendants':0,'plain_elaboration_private_name_scope':'_stdin environment; no installed compiled module emitted'}
    results.append({'name':name,'exit':rr['exit'],'errors':rr['errors'],'seconds':rr['seconds'],'source_sha256':rr['input_sha256'],'log_sha256':rr['output_sha256']})
assert metadata['Tautology-actual-native-v1']==metadata['Tautology-actual-sealed-v1']
(O/'compiled-target-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
controls=json.loads((O/'control-check.json').read_text());assert controls['definitions']==14 and controls['pointwise_and_abstracted_pairs']==28 and controls['all_exact_multiplicities_match']
for rel,pin in C['source_pins'].items():
    if rel.endswith('/Tautology.lean'):continue
    assert sha((W/rel).read_bytes())==pin['sha256'],rel
delta={'source':'TCSlib/Complexity/ClassNP/Tautology.lean','initial_execution_head':C['source_head_at_preparation'],'head_at_finalization':subprocess.check_output(['git','-C',str(W),'rev-parse','HEAD']).decode().strip(),'before_bytes':len(before),'after_bytes':len(after),'before_sha256':sha(before),'after_sha256':sha(after),'full_private_header_sha256':sha(header),'full_private_header_identical':True,'exact_one_doc_and_proof_block_replacement_recovers_every_other_byte':True,'all_public_headers_definitions_tables_imports_order_attributes_unchanged':True,'source_imports':[x.decode() for x in imports(after)],'import_closure_delta':[],'import_closure_delta_basis':'Exact import list and all dependency source bytes untouched by this edit; no graph rerun claimed. MSG6 is the completed read-only dependency snapshot.','SAT_and_Hardness_unchanged':True,'target_line':after[:after.index(b'private lemma taut_comp_on_image')].count(b'\n')+1,'callee':'Turing.FinTM.exists_comp_on_image','callee_source_home':'TCSlib/Complexity/TuringMachine/Composition.lean','callee_line':513,'private_declaration_retained_as_one-line_adapter':True,'no_new_host_API_import_statement_debt':True,'status_at_finalization':subprocess.check_output(['git','-C',str(W),'status','--porcelain']).decode()}
(O/'source-freeze.json').write_text(json.dumps(delta,indent=2)+'\n')
(O/'reverse.patch').write_text(''.join(difflib.unified_diff(after.decode().splitlines(True),before.decode().splitlines(True),fromfile='a/TCSlib/Complexity/ClassNP/Tautology.lean',tofile='b/TCSlib/Complexity/ClassNP/Tautology.lean')))
comp=(W/'TCSlib/Complexity/TuringMachine/Composition.lean').read_text();a=comp.index('/-- **Composition with a second machine correct only on the image.**');z=comp.index('/-- **The buffered composition\'s halting relation**',a)
(O/'canonical-exists-comp-on-image.lean.txt').write_text(comp[a:z])
verification={'native_and_seal_runs':results,'controls':controls,'full_source_exactly_pinned':True,'all_explicit_changed_proof_arguments_reviewed':True,'explicit_argument_scan':'Only exact FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU. No rw/simp/unfold/change/Def argument, compiler-generated equation or private alias.','direct_ordinary_inventory_complete_for_selected_header_and_value':True,'inventory':'Both directly reached foreign ordinary TCSlib definitions are guarded; the fourteen-definition guard also covers model operations without recursively opening the imported theorem proof. FinTM itself is an inductive structure, not a guarded ordinary definition.','guard_before_doc_header_and_body':True,'fresh_control_imports_exact_actual_imports':True,'default_model_simp_rules_removed':ins['default_simp_removed'],'no_bare_Lean_no_Lake_no_compiled_output_no_screen_no_Git_mutation':True,'source_unchanged_legacy_regions_not_claimed_sealed':True,'full_module_census_and_merged_chain_left_to_parent':True}
(O/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
(O/'README.md').write_text('''# Tautology image-composition repoint

**Not yet clear to merge: #215** — this is the scoped repair evidence; root owns the downstream replay, final screen, audit and merge status.

The authorized edit is complete in `TCSlib/Complexity/ClassNP/Tautology.lean`: private `taut_comp_on_image` now calls existing public `Turing.FinTM.exists_comp_on_image` directly. Its exact full header, time coefficient2 and all other source bytes are preserved, except the adjacent doc/sketch updated to describe reuse. No new import, public API, executable host, statement, attribute or debt acknowledgment. The private adapter name remains for its existing caller.

Final source SHA256: `59ee3b71fb6b9a2cfb90d6ffd239a0858f683c1daca4c2c0167db9877ed9b8a8`,79,808 bytes. Before: `0b85b289abd864b1f63a9dcdc7f47fdb9b68c0544e57e4de63f0d35dbc09c8a5`,80,849 bytes. SAT stays `682df0cd83abed16dac1e44768bee40a1691030eaeab1cf56373fa0677dbc6ba`; Hardness stays `3c41a6aca1ed4e24b08330b7819a4d36ce0e695be4a71b11382c346e39499952`.

## Executed checks

All runs used only the managed plain wrapper, complete read-only MSG6, local budget3/global cap5, one own Lean process at a time. No compiled output was emitted.

- Exact-header hypothetical native: PASS,10.05s; hypothetical14-definition seal: PASS,9.56s. Both completed before actual source edit.
- Complete exact actual Tautology source native: PASS,10.43s,0 errors; complete source with changed section guarded: PASS,10.03s,0 errors. Guard precedes docstring/header/body; default `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg` simp rules removed. Removing guard instrumentation/metadata recovers exact actual bytes.
- Fresh28 controls over14 ordinary model definitions:28 kernel-checked pointwise/abstracted positive passes, then exactly28 negative failures at the same identities. Checker verifies multiplicities/diagnostics/exits and rejects four corrupted-evidence cases. Full raw outputs are retained; the tool display's negative-output preview was capped, not the stored log.
- Selected private root and all actual prefix descendants in each full-source elaboration: one theorem, zero generated descendants; exact standard axioms `propext`, `Classical.choice`, `Quot.sound`. Direct TCSlib references: `FinTM`, the two computation predicates and public `exists_comp_on_image`. Both ordinary predicates are guarded; no foreign executable definition appears in the new proof. Exact argument scan contains only the public theorem application.

Metadata private names are the plain elaboration's `_stdin` identities, preserved verbatim. This is not a claim to have installed/replayed the actual named module or globally audited legacy declarations; parent will run the MSG7 downstream chain and compiled census. The imported canonical theorem's internal proof is not recursively re-audited here.

## Context and freeze

Execution source HEAD was `63a3ce018e96c8c114b9c82f8d5fce6021c7d03c`. Contrary to an earlier dependency suggestion, Tautology explicitly imports Hardness at line10. Root acknowledged this correction; all checks use completed MSG6, after its26-module chain passed, rather than claim MSG5 had identical dependencies. Before editing, the worktree was clean and root released the edit after MSG6 completion. Only Tautology was dirtied. No source changed during any run.

`source-freeze.json`, complete before/after sources, forward/reverse patches, full header, exact instrumentation and all commands/receipts are retained. Restoring the old doc/proof block recovers every baseline byte. Callee source quote and owner hash are retained; source/import closure delta is empty by byte identity, not a newly executed graph count. No public equation materialization or new reader was needed.

No Lean failure occurred except the28 deliberately failing negative controls. Initial source-home guesses failed read-only and were corrected using the file inventory; those attempts are recorded. No screen, snapshot/cache change, Git mutation, commit or push was performed. Broad remaining image-family disposition is a separate source review owned by root/its other reviewer.
''')
(O/'finalize.py').write_bytes(Path(__file__).read_bytes())
files=[]
for p in sorted(O.iterdir()):
    if p.name=='MANIFEST.json':continue
    assert p.is_file() and not p.is_symlink(),p
    b=p.read_bytes();files.append({'path':p.name,'bytes':len(b),'sha256':sha(b)})
m={'frozen_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head_at_execution':C['source_head_at_preparation'],'actual_source_sha256':sha(after),'read_only_snapshot':'oleans-msg6','scope':'One private Tautology proof/sketch mechanical repoint; no gate clearance','payload_files':len(files),'payload_bytes':sum(x['bytes'] for x in files),'files':files}
(O/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'out':str(O),'manifest_sha256':sha((O/'MANIFEST.json').read_bytes()),'payload_files':len(files),'payload_bytes':m['payload_bytes'],'source_sha256':sha(after),'line':delta['target_line']},indent=2))
