from pathlib import Path
import json,re,hashlib,shutil,datetime
O=Path('/private/tmp/ab34-nat-reader-closure-refinement');P=O/'project';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();context=json.loads((O/'guard-context.json').read_text());expected={(r['definition'],r['mode']) for r in context['fresh_paired_control_identities']};assert len(expected)==6
pos=re.findall(r'CONTROL\|([^|\n]+)\|([^|\n]+)\|PASS\|kernelChecked=(\S+)',(O/'ControlsNative-attempt2.log').read_text());neg=re.findall(r'CONTROL\|([^|\n]+)\|([^|\n]+)\|FAIL',(O/'ControlsSealed-attempt2.log').read_text());assert len(pos)==len(neg)==6 and {(a,b) for a,b,c in pos}==set(neg)==expected and {c for a,b,c in pos}=={r['kernel_name'] for r in context['fresh_paired_control_identities']}
checks=[]
for stem,attempt,exit,errors in [('OwnerNative','attempt1',0,0),('OwnerInventory','attempt1',0,0),('ScopeGuardNative','attempt1',0,0),('ScopeSealed','attempt1',0,0),('ControlsNative','attempt2',0,0),('ControlsSealed','attempt2',1,6),('IncFixedStatus','attempt1',0,0)]:
 r=json.loads((O/(stem+'-'+attempt+'.json')).read_text());assert (r['exit'],r['errors'],r['warnings'],r['sorry_warnings'])==(exit,errors,0,0);assert r['source_sha256']==h(O/(stem+'.lean.txt')) and r['raw_sha256']==h(O/(stem+'-'+attempt+'.log')) and r['source_unchanged'];checks.append({'check':stem,'receipt':stem+'-'+attempt+'.json','exit':exit,'errors':errors,'warnings':0,'sorry_warnings':0})
inv=(O/'OwnerInventory-attempt1.log').read_text();defs=[json.loads(l.split('DEF|',1)[1]) for l in inv.splitlines() if l.startswith('DEF|')];theorems=[json.loads(l.split('THEOREM_BOUNDARY|',1)[1]) for l in inv.splitlines() if l.startswith('THEOREM_BOUNDARY|')];ax=json.loads(next(l.split('AX|',1)[1] for l in inv.splitlines() if l.startswith('AX|')));assert set(ax['axioms'])==set(['propext','Classical.choice','Quot.sound']);assert ax['private'] and not ax['simp_lemma'] and not ax['simp_unfold'];(O/'full-target-foreign-head-inventory.json').write_text(json.dumps({'root':'Turing.MachineFormat.canonOffset_spec','ordinary_imported_TCS_heads':['Turing.codeBitsNat','Turing.incFixed'],'focused_Mathlib_head':'Nat.bit','guard_union':context['guard_names'],'default_simp_definitions_removed':[],'all_definition_records':defs,'all_theorem_boundaries':theorems,'same_owner_theorem_and_definition_types_values_traversed':True,'imported_theorem_proof_values_not_traversed':True,'projection_and_kernel_abbrev_exclusions_explicit_in_records':True,'root_compiled_metadata_synthetic_owner':ax,'earlier_same_owner_helper_proof_bodies_not_claimed_sealed':True},indent=2,ensure_ascii=False)+'\n');(O/'control-pair-results.json').write_text(json.dumps([dict(r,positive_kernel_checked=True,negative_same_identity_failed=True) for r in context['fresh_paired_control_identities']],indent=2)+'\n')
a=(O/'owner-before.lean.txt').read_text();b=(O/'owner-proposed.lean.txt').read_text();old='    change Nat.bit true (codeBitsNat w.length.bits + 1) = _\n';new='    rw [← codeBitsNat_eq]\n';assert a.count(old)==1 and b==a.replace(old,new,1);assert '    simp only [Nat.bit_val, Bool.toNat_true]\n' in b;assert h(O/'owner-proposed.lean.txt')=='8f1b19cf6893b7129e6d98ced5572633f6ed04a1b2fcd5767d04e136e7cef9c8';(O/'source-freeze.json').write_text(json.dumps({'actual_old_PR_head':'d725e9fa76c81623e95c350250853bec511ddc3c','proposed_owner_sha256':h(O/'owner-proposed.lean.txt'),'exactly_one_change_line_replaced_by_public_theorem_rewrite':True,'all_existing_headers_docstrings_names_imports_attributes_definitions_and_other_bytes_exact':True,'new_API_import_header_definition_or_mathematical_fill':False,'Nat_bit_val_replacement_retained':True,'complete_target_header_body_inside_seal':True,'same_original_library_imports_in_full_owner_and_scopes':True,'only_inventory_and_control_instrumentation_add_Lean':True},indent=2)+'\n')
for stem in ['ScopeGuardNative','ScopeSealed']:
 raw=(O/(stem+'-attempt1.log')).read_text();assert 'sorryAx' not in raw and 'depends on axioms:' in raw
rows=[]
for r in context['fresh_paired_control_identities']:
 rows.append(dict(r,positive_kernel_name=next(c for a,b,c in pos if a==r['definition'] and b==r['mode']),positive=True,negative=True))
(O/'RESULTS.json').write_text(json.dumps({'status':'FROZEN_PRIVATE_EXISTING_API_REPAIR_PREFLIGHT_PASS_ROOT_ADOPTION_PENDING','checks':checks,'full_target_complete_doc_header_body_native_and_sealed':True,'ordinary_TCS_heads':2,'focused_Mathlib_heads':1,'guard_union_count':3,'default_simp_definitions_removed':0,'positive_kernel_checked_controls':6,'negative_matching_identity_controls':6,'all_control_pairs':rows,'full_target_AX_standard_only':ax['axioms'],'source_owner_sha256':h(O/'owner-proposed.lean.txt'),'no_new_actual_PR_head_full23_replay_metadata_or_33screen_claim':True,'old_d725_full23_screen_packet_is_historical':True,'no_source_Git_canonical_snapshot_or_external_mutation':True,'all_native_jobs_closed':True},indent=2)+'\n')
(O/'explicit-argument-review.md').write_text('''# Full target argument review

| Full target step | Classification |
|---|---|
| `rw [← foldr_bit_eq_ofDigits]` | Existing imported theorem; proof value is a citation boundary. |
| First `change Nat.bit true ((canonCount ...).foldr Nat.bit 0) = _` | Exposes own canonOffset and core list computation. It passes with all3 foreign/focused heads opaque, including incFixed beneath the own canonCount definition. |
| `(canonCount_spec ...).2.2` and `.2.1` | Same-owner private theorem projections. Their type/value footprint is inspected. Their earlier legacy proof bodies are outside this one-target sealing claim. |
| `rw [← codeBitsNat_eq]` | Exact repaired foreign conversion: public CodeParser theorem, line132, rewriting foldr to the named decoder. Foreign codeBitsNat is not unfolded by change. |
| `rw [codeBitsNat_bits]` | Existing imported CodeParser theorem. |
| `simp only [Nat.bit_val, Bool.toNat_true]` | Existing public Mathlib/Core equations; retained Nat.bit repair. |
| `length_bits_le_self` | Existing imported theorem. |
| `simp only [canonOffset, List.length_cons, ...]` | Own definition plus Core list theorem and the same-owner width projection. No imported ordinary definition is explicitly listed. |

The only ordinary foreign TCS heads reached through the target and same-owner
helper types/values are codeBitsNat and incFixed; Nat.bit is the additional
focused Mathlib guard. All3 are guarded before the complete target doc/header/
body. Imported theorem proof values remain boundaries; other Mathlib/Core
internals and earlier same-owner helper proof bodies are not claimed sealed.
No remaining explicit foreign-definition argument appears in the target.
''')
(O/'preparation-notes.json').write_text(json.dumps({'read_only_search_failure':'Initial search guessed nonexistent BinaryIncrement.lean; corrected targeted rg located incFixed in Build/Convention.lean. No Native/source consequence.','control_attempt1':'Four Nat.bit/codeBitsNat generic body controls passed; both generic reflected incFixed body controls failed even natively. They therefore did not establish effectiveness. Original sources under attempt1-controls/ and all actual receipts/logs preserved. No failure hidden or relabeled as pass.','control_attempt2':'Concrete incFixed nil/false-cons equations pass natively and fail under identical guard contexts. Six final positive kernel names and six matching negative identities verified. All three normal statuses semireducible, no transparency/reducibility override. Error placeholders in the intentionally failing negative scratch fixture are not library admissions; proposed full target AX remains standard.','type_and_scope_limit':'Synthetic-owner full type/universes/privacy/simp/AX captured. Actual new-HEAD compiled ABI/full23 replay/new33 screen still require root adoption and matching actual evidence. The full target is sealed; earlier same-owner helper proofs are only traversed for footprint, not claimed sealed.','frozen_old_packet':'/private/tmp/ab34-gate127-ready-draft is immutable old d725 history; the exact additional reader repair has no current published source pin yet.'},indent=2)+'\n')
(O/'README.md').write_text('''# Private full-target canonOffset reader repair

The exact existing-API patch replaces only the foreign-definition conversion
`change Nat.bit true (codeBitsNat w.length.bits + 1) = _` with
`rw [← codeBitsNat_eq]`, retaining the existing Nat.bit_val repair. Source is
relative to actual PR247 head d725e9fa76c81623e95c350250853bec511ddc3c.
Complete before/proposed owner, exact one-line patch and source freeze are given.
Proposed owner SHA256:
8f1b19cf6893b7129e6d98ced5572633f6ed04a1b2fcd5767d04e136e7cef9c8.

The complete owner passes natively against whole MAC8, source9b5, with original
imports and zero errors/warnings/sorry warnings. A full-owner inventory walks
root and same-owner helper theorem/definition types AND values; imported theorem
proof values remain boundaries. Exact ordinary TCS heads are codeBitsNat and
incFixed, plus focused Mathlib Nat.bit. No default-simp definitions to remove.
The COMPLETE target doc/header/body passes both native and sealed owner probes
under all3 guards, with standard AX [propext, Classical.choice, Quot.sound].
Six final kernel-checked controls pass natively and their exact six identities
fail sealed. The two incFixed controls are its nil/false-cons equations. The
initial generic reflected incFixed controls fail even normally; original sources
and failed logs are preserved and not counted as effective evidence. No unsafe
transparency or reducibility override is used. explicit-argument-review.md lists
every target rewrite/simp/change and the precise scope boundaries.

This is the one complete target seal, not a seal of the entire legacy owner or
earlier same-owner helper proofs. The latter are inspected for footprint but
remain unchanged; imported theorem proof values/Core internals stay boundaries.
No new interface/import/header/definition/name/home or mathematical fill.
No actual source/Git/canonical/snapshot mutation, commit, push, screen, full23
replay, actual new-HEAD ABI, dispatch or gate closure. Root adoption/publication
and matching new-source replay/screen/metadata remain necessary. The old frozen
226-file gate127 packet stays immutable historical evidence for d725 only.
Seven accepted SG1 kinds, FE/FH/BLIVE separation,54 named union and nine inherited
Primitives closures retain their bounds; no global absence/debt retirement.

All Native work used approved leanelab, one helper slot, local3/machine5,
j4/nice10. Exact source .lean.txt, commands, receipts, all failed preparations,
complete canonical CodeParser/Convention/Mathlib source and full manifest follow.
''')
# Save execution configuration; disposable project is outside frozen evidence.
C=O/'runtime-configuration';C.mkdir(exist_ok=True);shutil.copy2(P/'lean-toolchain',C/'lean-toolchain');(C/'package-link.json').write_text(json.dumps({'historical_runtime_project':str(P),'packages_target':str((P/'.lake/packages').resolve()),'proof_inputs_all_captured_as_lean_txt':True},indent=2)+'\n');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');shutil.copy2(R/'devtools/seyoon/leanelab.sh',C/'leanelab.sh');runtime=Path('/private/tmp/ab34-nat-reader-closure-refinement-runtime');assert not runtime.exists();shutil.move(str(P),str(runtime))
entries=[]
for p in sorted(O.rglob('*')):
 assert not p.is_symlink(),str(p)
 if p.is_file():entries.append({'path':p.relative_to(O).as_posix(),'bytes':p.stat().st_size,'sha256':h(p)})
(O/'MANIFEST.json').write_text(json.dumps({'status':'FROZEN_PRIVATE_EXISTING_API_REPAIR_PREFLIGHT_ROOT_ADOPTION_PENDING','frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_file_count':len(entries),'payload_bytes':sum(r['bytes'] for r in entries),'manifest_self_excluded':True,'files':entries},indent=2)+'\n')
for r in entries:assert h(O/r['path'])==r['sha256']
print(json.dumps({'path':str(O),'payloads':len(entries),'bytes':sum(r['bytes'] for r in entries),'MANIFEST_sha256':h(O/'MANIFEST.json'),'patch_sha256':h(O/'reader-refinement.patch'),'owner_sha256':h(O/'owner-proposed.lean.txt'),'RESULTS_sha256':h(O/'RESULTS.json'),'complete_target_seal':True,'ordinary_foreign_TCS_heads':2,'focused_Mathlib_heads':1,'paired_controls':6}))
