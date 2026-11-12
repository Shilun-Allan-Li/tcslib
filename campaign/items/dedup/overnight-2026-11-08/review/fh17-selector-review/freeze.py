from pathlib import Path
import json,hashlib,datetime,shutil,subprocess
O=Path(__file__).parent
D=O/'EXPORT'
assert not D.exists()
T=json.loads((O/'TASK.json').read_text())
W=Path(T['source_worktree'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads((O/p).read_text())
assert load('SOURCE-PRESERVATION.json')['PASS']
assert load('ALL17-CODE-PRESERVATION.json')['PASS']
assert load('ALL-ATTEMPT-FULL-HEADERS.json')['attempts']==19
assert load('SEAL-VERIFICATION.json')['PASS']
assert load('EXPLICIT-ARGUMENT-REVIEW.json')['PASS']
assert load('NATIVE-FINAL-OWNERS.json')['PASS']
assert load('MAC8-CONTEXT.json')['PASS']
assert subprocess.check_output(['git','--no-optional-locks','-C',str(W),'rev-parse','HEAD'],text=True).strip()==T['source_head']
patch=O/'remaining13.patch'
summary={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'validation':'PASS bounded to this exact source delta and named guards','source_worktree':str(W),'source_branch':T['source_branch'],'source_HEAD':T['source_head'],'source_uncommitted':True,'baseline_MAC8':T['baseline'],'remaining13_patch_sha256':sha(patch),'all17_since_MAC8_patch_sha256':sha(O/'all17-since-MAC8.patch'),'new_consumers':13,'new_owners':11,'root_existing_consumers':4,'total_inspected_consumers':17,'total_consumer_owners':14,'canonical_home':1,'new_native_actual_checks':19,'unique_final_native_owner_inputs':11,'native_errors':0,'native_declaration_sorry_warnings':0,'complete_guarded_declarations':13,'guard_applications':27,'paired_control_identities':46,'all_complete_headers_including_statement_let_assignments_exact':True,'all_other_START_bytes_recovered_exact':True,'all17_nontarget_code_tokens_and_imports_exact_MAC8':True,'new_public_API_import_statement_name_home_or_debt_permission':False,'new_math_sorry_fills':0,'Git_mutations':0,'full_replay_executed_here':False,'fresh_compiled_metadata_or_AXIOM_census_here':False,'canonical_record_writes':0,'new_audit_dispatch_or_closure':False,'RO1_generic_unlanded_API_consumed':False,'RO1_one_step_chains_existing_acknowledged_kind_retained':True,'all17_count_is_inspected_lower_bound_not_global_absence':True,'next_boundary':'Root owns commit/push, complete final family replay, gate122/PR readiness; Seyoon alone merges/dispatches/rules.'}
(O/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
text='''The remaining thirteen inspected deterministic first-None selectors are re-pointed and validated through the existing Turing.MultiTapeTM.exists_first_halt theorem, with no new public API, import, statement, name, runtime definition, home, route or debt permission. The full family inventory in this packet is seventeen consumers plus the canonical home. No mathematical sorry is filled. Source is still uncommitted over2c85a68a73f74b79ac19ab2f824a17ddf2432962 on codex/ab34-first-halt-reuse; this report does not invent a Git binding for the new delta.

Use remaining13.patch over that exact HEAD. all17-since-MAC8.patch additionally includes root's original four consumers. Complete BASE/START/FINAL source for all fifteen files including the canonical home, complete old/new declaration chunks and literal full headers are retained. The final header verifier uses the outer theorem := by delimiter, so statement let assignments (notably b2_verify_timed) are included. All nineteen native-attempt headers are checked completely. Reversing only the thirteen final chunks recovers every other START byte exactly. Reversing all seventeen consumer chunks recovers all non-target code tokens from MAC8's9b5 baseline; root's prior comment-only changes are explicitly allowed and distinguished from literal byte equality. All fifteen BASE/FINAL import headers are exact. No file outside the eleven newly authorized owner files is edited by this task. Four nondeterministic runWith/HaltsWithin selectors and the mixed-stop WindowRun chunk remain literal unchanged exclusions. These are inspected candidates and a lower bound, not a whole-library absence claim or a cumulative debt rate.

Every new proof was applied alone and checked before proceeding to the next. The nineteen actual native checks cover thirteen new consumer bodies and their subsequent reader repairs in eleven unique owners. All checks exit0/errors0/declaration-sorry warnings0. NATIVE-FINAL-OWNERS.json identifies the actual last successful input for every final owner hash; earlier unchanged inputs retain their real execution timestamps. Complete unfiltered logs, commands, SHA256s, before/after owner files and intermediate chunks are immutable in attempts/. The original selector-only thirteen checks are preserved separately; they are not relabeled as checks of the later reader versions. Root's original three-consumer replay and fourth EXP check remain their own historical executions; no new check of those four owners or a final seventeen-consumer replay is claimed here.

The named guard checks cover every complete docstring/header/body for the thirteen new declarations, including scoped open commands where present: MultiTapeTM.runFrom and MultiTapeTM.step in all eleven owner contexts, and additionally MultiTapeTM.initCfg in Clean. All thirteen scopes pass, with twenty-seven guard applications. Forty-six paired identities are effective: each native named theorem compiles with no kernel errors, while the corresponding sealed file fails at exactly its own rfl source goal lines. Source pairs differ only by the exact irreducibility line. Guard/input/output hashes and whole-source envelope removal are checked independently. Unchanged successful inputs are reused only after literal input SHA correspondence; the final Call input is a fresh actual pass after both forced step unfolds were removed. No unsafe reducibility override or global opacity claim is made. Other inherited foreign-definition closure is outside these selected names; it is not silently declared certified. The full added-command review finds no new foreign/Core/Mathlib definition arguments, and all thirteen complete declarations are scanned for forced unfold/delta/explicit arguments of the named guards, with zero remaining bypasses.

Guard failures were used as evidence, not ignored. Call's old zero/one delta reads are now explicit published runFrom_zero/runFrom_succ_eq_step readers; seven exact overlap regions, including latent downstream sites, are retained for RO1 rebasing. Both old forced MultiTapeTM.step unfolds use step_of_some. Clean uses the published initCfg_with_q₀/runFrom_with_q₀ readers; its retagged visited-set transfer uses mem_visitedByTapeHead_iff and local proven equalities, and its zero/one reads use the existing published equations. These repairs stay inside the same existing two bodies and do not increase the seventeen consumer count. Existing one-step equation chains remain in the already acknowledged RO1 kind pending the generic API/home decision. No unlanded generic API is consumed, and no new waiver follows. Exact Call and Clean before/after data are CALL-RO1-OVERLAP.json, CALL-STEP-READER.json and CLEAN-READERS.json.

MARMTime's first guard fixture incorrectly crossed an open...in command and following namespace transition. That fixture is invalid as source evidence, and is retained with its full source/output and disposition. The corrected fixture envelopes the scoped command, full docstring/header/body and excludes following namespace commands; it actually passes. Preparation-only substitution/path/syntax failures are separately labeled and did not execute Lean or change source. Early guarded source failures and superseded attribute-only Call inputs are retained; the final result uses only exact current-source passing inputs. No failed snapshot exists: all checks use plain leanelab without output objects. The complete current MAC8 map still has895 objects matching the independently frozen MAC8 input and published9b5 adoption.

All elaborations use the approved helper against the complete MAC8 tree, one own Lean process at a time, helper-enforced nice10/-j4 and shared locks under local3/machine5. No lake build, bare Lean invocation, snapshot splicing, source cache mutation, Git operation that writes history/index content, push, canonical record mutation, screen, lint, fresh compiled census/AX scan, full downstream replay or external audit dispatch is performed by this task. Native style messages remain unfiltered and are not represented as zero lint findings. Colleague edits are exactly the parent-authorized mechanical/FYI scope; no outside FYI message is sent here.

The complete disposition table follows; each row's full source, route, unchanged full header, imports and exact hashes are in DISPOSITIONS17-PLUS-CANONICAL.json.

| Consumer | Owner | Disposition |
|---|---|---|
'''
rows=load('DISPOSITIONS17-PLUS-CANONICAL.json')
for row in rows:
    status='Canonical home retained' if row['id']==76 else ('Existing root re-point; no new execution relabeled' if row['id'] in [9,18,19,33] else 'New re-point; actual final native and full named guards pass')
    text+=f"| {row['name']} | {row['path']} | {status} |\n"
text+='''
Validation is ready for root adoption. Root owns committing/pushing this exact delta, the final seventeen-consumer downstream replay, gate122 and PR readiness. Seyoon alone merges/dispatches/rules. **Not yet clear to merge: #242 — final source commit/replay/gate122 remain root-owned.** The separate FE final-validation export remains immutable and is not mixed into this source family.
'''
(O/'REVIEW.md').write_text(text)
ignored={'live','EXPORT'}
D.mkdir()
for p in sorted(O.iterdir()):
    if p.name in ignored:
        continue
    assert not p.is_symlink(),p
    if p.is_dir():shutil.copytree(p,D/p.name)
    else:shutil.copyfile(p,D/p.name)
files=[]
for p in sorted(D.rglob('*')):
    assert not p.is_symlink(),p
    assert p.suffix.lower()!='.pdf',p
    assert not p.name.endswith('.lean'),p
    if p.is_file():files.append({'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':sha(p)})
manifest={'schema':'complete frozen payload; manifest and checksum file exclude themselves','frozen_utc':summary['frozen_utc'],'source_HEAD':T['source_head'],'source_uncommitted_patch_sha256':sha(patch),'payload_files':len(files),'payload_bytes':sum(r['bytes'] for r in files),'no_symlinks_plain_Lean_or_privatePDF':True,'files':files}
(D/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
(D/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in files)+sha(D/'MANIFEST.json')+'  MANIFEST.json\n')
for row in files:assert sha(D/row['path'])==row['sha256']
print(json.dumps({'folder':str(D),'payload_files':len(files),'payload_bytes':manifest['payload_bytes'],'REVIEW_sha256':sha(D/'REVIEW.md'),'MANIFEST_sha256':sha(D/'MANIFEST.json'),'SHA256SUMS_sha256':sha(D/'SHA256SUMS'),'remaining13_patch_sha256':sha(D/'remaining13.patch'),'all17_since_MAC8_patch_sha256':sha(D/'all17-since-MAC8.patch')},indent=2))
