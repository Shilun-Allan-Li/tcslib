from pathlib import Path
import json,hashlib,re,subprocess,datetime,shutil,collections
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
def j(p):return json.loads(Path(p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(O/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
source=j(O/'SOURCE-ENDPOINT.json');rev=source['source'];tree={}
for ln in subprocess.check_output(['git','ls-tree','-r',rev,'--','TCSlib'],cwd=R).decode().splitlines():
 meta,p=ln.split('\t',1)
 if p.endswith('.lean'):tree[p]=meta.split()[2]
assert set(tree)=={x['path'] for x in source['files']}
for x in source['files']:
 b=(O/'source'/(x['path']+'.txt')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==tree[x['path']]==x['git_blob']
maps=j(O/'DRAFT-SOURCE-MAP.json');assert len(maps)==11 and all(x['header_exact'] for x in maps)
native=[]
for p in sorted((O/'native').glob('*-run.json')):
 d=j(p);b=(O/'native'/(d['label']+'.out')).read_bytes();f=O/'project'/d['file'];assert sha(f.read_bytes())==d['input_sha256'];assert sha(b)==d['output_sha256'];assert d['exit']==d['errors']==d['sorry_warnings']==0;native.append(d)
assert len(native)==5
save('NATIVE-RESULTS.json',{'result':'PASS exact final11-root/5-owner body draft','rows':native,'source':rev,'whole_snapshot':'oleans-mac8','one_own_Lean_at_a_time':True,'new_compiled_output_requested':False,'historical_executions_not_relabelled':True})
seals=[];c=[]
for m in j(O/'SEAL-SOURCE-MAP.json'):
 label=m['label'];d=j(O/'sealed-runs'/('FE1Sealed_'+label+'-run.json'));f=O/m['sealed_file'];raw=(O/'sealed-runs'/('FE1Sealed_'+label+'.out')).read_bytes();assert d['input_sha256']==m['sealed_sha256']==sha(f.read_bytes());assert d['output_sha256']==sha(raw);assert d['exit']==d['errors']==d['sorry_warnings']==0;assert m['roundtrip_exact'] and m['guard_before_complete_docstring_header_body'];seals.append(d)
 ns=O/'project'/('FE1Controls_'+label+'_native.lean');ss=O/'project'/('FE1Controls_'+label+'_sealed.lean');nt=ns.read_text();st=ss.read_text();assert re.sub(r'^attribute \[local irreducible\][^\n]*\n','',st,flags=re.M)==nt
 nr=j(O/'sealed-runs'/('FE1Controls_'+label+'_native-run.json'));sr=j(O/'sealed-runs'/('FE1Controls_'+label+'_sealed-run.json'));nb=(O/'sealed-runs'/('FE1Controls_'+label+'_native.out')).read_bytes();sb=(O/'sealed-runs'/('FE1Controls_'+label+'_sealed.out')).read_bytes();assert nr['input_sha256']==sha(ns.read_bytes()) and sr['input_sha256']==sha(ss.read_bytes());assert nr['output_sha256']==sha(nb) and sr['output_sha256']==sha(sb);assert nr['exit']==nr['errors']==0 and sr['exit']==1 and sr['errors']==sr['rfl_errors']==4
 names=re.findall(r'^theorem (FE1_\w+)\b',nt,re.M);assert len(names)==4 and len(set(names))==4
 assert all(re.search(r'^'+re.escape(n)+r'\b',nb.decode(),re.M) for n in names)
 expected_lines=[]
 for x in re.finditer(r'(?ms)^theorem (FE1_\w+)\b.*?:= by rfl',st):expected_lines.append(st.count('\n',0,x.end())+1)
 actual_lines=[int(x) for x in re.findall(r':(\d+):\d+: error: Tactic `rfl` failed',sb.decode())];assert expected_lines==actual_lines,(label,expected_lines,actual_lines)
 c.append({'context':label,'guards':m['guards'],'paired_identities':4,'native_kernel_checked_names':names,'native_exit':nr['exit'],'sealed_exit':sr['exit'],'sealed_rfl_error_lines':actual_lines,'exact_source_pair_and_raw_hashes':True})
assert len(seals)==5 and sum(len(m['targets']) for m in j(O/'SEAL-SOURCE-MAP.json'))==11
save('SEAL-RESULTS.json',{'result':'PASS all11 complete docstring/header/body scopes at2 core API definitions','rows':seals,'scope':'runFrom/step only; not a complete foreign-definition closure seal or global Rule10 clearance'})
# A separate exact generic terminal-action route is guarded at3 additional definitions.
rrows=[]
for label in ['FE1ActionReader_native','FE1ActionReader_sealed','FE1ReaderControls_native','FE1ReaderControls_sealed']:
 d=j(O/'reader-runs'/(label+'-run.json'));f=O/'project'/(label+'.lean');raw=(O/'reader-runs'/(label+'.out')).read_bytes();assert d['input_sha256']==sha(f.read_bytes()) and d['output_sha256']==sha(raw)
 if label!='FE1ReaderControls_sealed':assert d['exit']==d['errors']==0
 else:assert d['exit']==1 and d['errors']==6
 rrows.append(d)
nt=(O/'reader-runs/FE1ReaderControls_native.out').read_text();st=(O/'reader-runs/FE1ReaderControls_sealed.out').read_text();np=re.findall(r'^READER_CONTROL\|([^|]+)\|([^|]+)\|PASS\|kernelChecked=([^\n]+)',nt,re.M);sf=re.findall(r'^READER_CONTROL\|([^|]+)\|([^|]+)\|FAIL$',st,re.M);sd=re.findall(r'error: READER_RFL\|([^|]+)\|([^|]+)\|',st);assert len(np)==len(sf)==len(sd)==6 and [(n,m) for n,m,k in np]==sf==sd and len({k for n,m,k in np})==6
native_ctrl=(O/'project/FE1ReaderControls_native.lean').read_text();sealed_ctrl=(O/'project/FE1ReaderControls_sealed.lean').read_text();assert re.sub(r'^attribute \[local irreducible\][^\n]*\n','',sealed_ctrl,flags=re.M)==native_ctrl
save('READER-RESULTS.json',{'result':'PASS native+3-definition-sealed terminal-action route and6 effective paired controls','rows':rrows,'kernel_checked_identities':np,'ordered_negative_identities':sf,'kernel_error_free_native_required':True,'failed_free-variable_marker_attempt_not_counted':True})
save('CONTROL-VERIFICATION.json',{'result':'PASS26 exact paired identities','owner_import_contexts':c,'core_pairs':20,'terminal_reader_pairs':6,'all_native_exit0_kernel_error_free':True,'all_sealed_failures_match_exact_identity_and_rfl_diagnostic':True,'full_target_guard_applications':22,'full_target_declarations':11,'ordinary_core_guards_unique':2,'additional_terminal_reader_guards_unique':3,'limits':'20 identities are generic controls in each of5 exact owner import contexts;6 additional identities cover3 ordinary terminal-reader definitions. No complete whole-proof foreign-definition-closure claim.'})
# Keep the added argument classifications explicit.
a=j(O/'EXPLICIT-ARGUMENT-REVIEW.json');a['published_or_same_home_or_local_heads'].update({'Action.apply_state':'published field theorem/Configuration','Action.apply_inputPos':'published field theorem/Configuration','Action.apply_workTapes':'published field theorem/Simulation','Action.apply_workTapePos':'published field theorem/Configuration','Action.apply_output':'published field theorem/Configuration','Cfg.workTapeSymbols_eq':'published field theorem/Configuration','Option.getD_none':'Core equation theorem','Function.update_eq_self':'Mathlib theorem','fields.1':'local conjunction component','fields.2':'local conjunction component'});a['reader_corrections']=['InputCall last-step proof explicitly invokes MultiTapeTM.step_of_some.','Comparator final emission explicitly invokes MultiTapeTM.step_of_some and published Action field equations; removed old explicit Action.apply unfolding.'];save('EXPLICIT-ARGUMENT-REVIEW.json',a)
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':rev,'source_endpoint_files':len(source['files']),'code_candidates':90,'extra_helper_dispositions':6,'remaining_FE_LIVE_members':11,'owners':5,'merged_MIG_consumers_already_canonical':5,'all_remaining_replacements':'Turing.MultiTapeTM.exists_first_entry_of_fixed','new_statement_name_import_API_home_design_or_debt_decision':False,'native':'ACTUAL PASS5/0errors/0sorry warnings on exact final body draft','seals':'ACTUAL PASS11 complete declarations at2 ordinary core API guards; source recovery exact','controls':'ACTUAL26 paired identities;20 core-context+6 terminal-reader','generic_terminal_reader':'ACTUAL native+3-definition-sealed PASS','source_worktree_Git_canonical_snapshot_cache_mutation':False,'compiled_output_requested':False,'copy_text_screen_execution':False,'fresh_axiom_census_execution':False,'fresh_replay_execution':False,'sketch_variant':'Comment-only sync; code tokens exact to executed body draft; not relabelled as separately executed','paused_optional_design':'WindowRun mixed physical halt/live-stop interface generalization left unchanged; decision required only if expanding into that separate contract','ready':'Root integration/combined validation/gate remain root-owned; no closure/retirement/merge claim'};save('SUMMARY.json',summary)
report='''# Post-MIG FE-LIVE-1 mechanical cleanup draft

Ready for root integration:11 existing proof/inline-guard implementations in5 files can consume `Turing.MultiTapeTM.exists_first_entry_of_fixed` with every existing statement/name/import/API/home preserved. No new debt acknowledgment or design ruling is required for these11. The native final body candidate passes all5 owners; bounded opacity and all26 effective paired controls pass. Source worktrees and canonical records are unchanged.

Source is `9b5dcf46408db681bcbc721930ef2203fa6bc47d`, imported against root-authorized completeMAC8. `SOURCE-ENDPOINT.json` independently binds all929 `TCSlib/` Lean paths, byte counts, SHA256s and Git blobs; all source evidence is `.lean.txt`. `DISPOSITIONS.json` gives uncapped dispositions for all90 lexical code candidates, with complete blocks/hits/hashes;6 further helper dispositions and all raw/prose/alternate-closing searches are retained. This is candidate enumeration plus inspection, not exhaustive semantic absence.

## Proposed implementation

Use `fe-live11-with-sketches.patch`. Its body component is `fe-live11-body-draft.patch`, and the subsequent comment-only synchronization is `sketch-sync-after-body.patch`. Executed native/seal inputs bind to the body component; the sketch variant has exact comment-stripped code-token equality, not a separately invented execution. `SOURCE-FREEZE.json` and `DRAFT-SOURCE-MAP.json` preserve every complete old/new header and source chunk hash; restoring old chunks recovers all other source bytes exactly.

- Hardness: `clBank_first`, `clCopy_first`, `clRow_first`, `clCmp_first`, `clFirst`, plus the inline wider verdict guard in `clA5Compare_compute`.
- ExhaustiveReplay: `xr_firstArrival` and `xr_firstArrival'`.
- EXP: `enumCont_first_anchor`, preserving stopped-to-active prefix transfer.
- InputLength: the inline completed-return cut in `exists_inputLengthTM`, preserving all original counting/head/framing arguments.
- InputCall: `inputSeekRewind_run`, preserving the exact parked endpoint and all prefix head bounds.

The comparator predicate includes both completed verdicts. Positive variants preserve their existing initial exclusion; a first wide-predicate time equals the prior singleton cut when that caller requires the same time. The exact route/premise/deadline table is INVENTORY.md and DISPOSITIONS.json. Five merged MIG consumers already call the canonical theorem and receive no patch. First-None halt selectors remain outside this task and do not overlap the separately assigned SAT/Hardness work.

## Executed evidence and limits

All tests use the approved leanelab helper against the wholeMAC8 snapshot, one own Lean process at a time, through shared locks/local3/machine5 with helper-enforced-j4/nice10 and no compiled output requested. Full logs and exact input/output hashes are preserved.

Native: actual PASS5 owners on the exact final11-root body draft,0 errors/0 declaration-sorry warnings. Earlier unchanged owner inputs retain their actual executions; failed drafts and the initial filesystem-blocked launcher wait are retained separately and never counted as passes. Full-file inherited linter messages remain unfiltered; no new canonical lint run is claimed.

Opacity: actual PASS for11 complete docstring/header/body declaration scopes with `MultiTapeTM.runFrom` and `MultiTapeTM.step` opaque (22 local guard applications). Each of5 exact owner import contexts has4 exact paired control identities: native kernel-checked declarations, matching sealed rfl failures and exact source pairing—20 identities total. A separate generic terminal-action route passes native and sealed with `Action.apply`, `Cfg.workTapeSymbols`, `moveInputPos` opaque/default Action simp removed, plus6 exact paired identities—26 total. Complete literal source recovery is checked. These are bounded checks, not all foreign-definition closure seals or global Rule10 approval.

The guarded checks exposed two inherited implicit step reads inside touched declarations. Their mechanical fixes use existing `step_of_some` and Action field equations; the comparator's former explicit Action.apply unfolding is removed. The changed-hunk explicit-argument review finds0 forbidden foreign/Core/Mathlib definition arguments. Unchanged legacy operational portions remain explicitly bounded: comparator preparation/mapState material and InputLength's prior counting/rewind/Cfg.inputSymbol argument are not represented as newly globally cleared proofs. Imported theorem proof values were not expanded/rendered. No fresh compiled census, all-axiom scan, replay, copy-text screen or lint execution is claimed here.

Failed fixture placement (guards between a docstring and lemma) and the ordinary-reader control preparation with unbound telescope variables are preserved. Their PASS-like markers do not qualify as evidence: final controls require actual exit0 and kernel-error-free positive output. Final check summaries use only corrected inputs and matching source hashes.

## Disposition and next boundary

FE-LIVE-1 remains the already acknowledged fixed-live-stop kind, maintainer-owned in next12.2c after activeMIG-1 and before further SAT/Hardness fills. The proposed11 retirements are contingent on integration, gate and Seyoon's merge; they do not create future-copy permission or approve another family. Current family census here is only an inspected lower bound, not a cumulative debt rate or a whole-library absence claim.

The mixed physical halt/live-stop minimum in `WindowRun.exists_windowRunnerTM` is left unchanged: its exposed contract mixes None with live exits and does not provide the fixed-live-stop premise/known live endpoint needed by this theorem. A broader first-stop API/contract generalization is a separate paused design question if root chooses to pursue it. Nonabsorbing positive returns, pure data minima, first-None and nondeterministic branch/depth selection have explicit out-of-family dispositions.

Root owns exact patch adoption, combination with the disjoint mechanical work, fresh joint validation, canonical records and morning Codex gate preparation. Seyoon alone merges/dispatches/rules. This report performs no gate closure, retirement, audit dispatch or merge.
'''
(O/'REVIEW.md').write_text(report)
# Export a complete durable artifact with source evidence as text; never copy the live project/package symlink.
E=O/'EXPORT';assert not E.exists(),'Frozen export already exists; do not overwrite'
E.mkdir()
for p in O.iterdir():
 if p.name in ['project','EXPORT']:continue
 if p.is_dir():shutil.copytree(p,E/p.name,symlinks=True)
 else:shutil.copy2(p,E/p.name)
for p in E.rglob('*'):
 assert not p.is_symlink(),p
 assert not p.is_file() or p.suffix!='.lean',p
 if p.is_file():p.read_text()
files=[{'path':str(p.relative_to(E)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(E.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','SHA256SUMS']]
manifest={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':rev,'result':'Frozen11-member/5-owner mechanical draft and complete bounded inventory/evidence','files':files,'excludes':['MANIFEST.json','SHA256SUMS'],'live_project_not_exported':True,'all_source_evidence_lean_txt':True,'no_source_or_Git_or_canonical_mutation':True};(E/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n');(E/'SHA256SUMS').write_text(''.join(f"{x['sha256']}  {x['path']}\n" for x in files)+sha((E/'MANIFEST.json').read_bytes())+'  MANIFEST.json\n')
print(json.dumps({'EXPORT':str(E),'files':len(files),'REVIEW_sha256':sha((E/'REVIEW.md').read_bytes()),'MANIFEST_sha256':sha((E/'MANIFEST.json').read_bytes()),'combined_patch_sha256':sha((E/'fe-live11-with-sketches.patch').read_bytes()),'source':rev,'native':'PASS5','scoped_seals':'PASS11','paired_controls':26},indent=2))
