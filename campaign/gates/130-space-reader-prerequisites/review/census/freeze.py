from pathlib import Path
import json,hashlib,collections,subprocess,datetime,re
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((O/n).read_text())
def write(n,v): (O/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
summary=read('SUMMARY.json');dispo=read('DISPOSITION-SUMMARY.json');cov=read('REF-COVERAGE.json');aliases=read('REF-ALIASES.json');bind=read('RELEVANT-SOURCE-BINDINGS.json');cs=read('CANDIDATES.json');cm={r['sha256_without_capture_LF']:r for r in read('CANDIDATE-CHUNKS.json')};by={r['source_blob_or_working_key']:r for r in bind};allrows=read('CANDIDATE-DISPOSITIONS.json');byhash={r['chunk_SHA256_without_capture_LF']:r for r in allrows};prs=read('OPEN-PRS-VERIFIED.json');f5=read('APPROVED-FIVE-BINDING.json');g129=read('GATE129-ALIGNMENT.json')
percommit=collections.defaultdict(set)
for c in cs:
 for b in by[c['source_blob']]['source_bindings']:
  if b['kind']=='ref_source':
   for rev in b['commits']:percommit[rev].add(c['chunk_sha256_without_capture_LF'])
five={r['chunk_SHA256_without_capture_LF']:r['name'] for r in f5['readers']};three={r['chunk_SHA256_without_capture_LF']:r['name'] for r in g129['three_readers']};rows=[]
for p in prs:
 current=g('rev-parse',p['verified_ref']+'^{commit}').decode().strip();g('cat-file','-e',current+'^{commit}');assert current==p['verified_source'],(p['number'],current)
 hs=sorted(percommit[current]);rows.append({'PR':p['number'],'provided_snapshot_source':current,'fetched_ref':p['verified_ref'],'named_head':p['head'],'pin_revalidated_at_freeze':True,'all_relevant_candidate_chunk_SHA256s':hs,'relevant_candidate_chunks':len(hs),'exact_gate130_reader_names':[five[h] for h in hs if h in five],'exact_gate129_reader_names':[three[h] for h in hs if h in three],'disposition':'Provided 16-PR snapshot source inspected by name and statement/body shape. No newly identified independent public twin; #248 carries the established controlAction_def peer and #251 the approved three readers.'})
write('OPEN-PR-CANDIDATE-COVERAGE.json',{'scope':'Exactly the 16 PR pins supplied in OPEN-PRS-RECEIVED.json, independently revalidated against local fetched refs at initial capture and freeze. Not a claim about all live GitHub PRs after the inventory timestamp. Own subsequently created #252 is separately bound, not silently folded into a new global open-PR count.','capture_started_UTC':summary['started_UTC'],'capture_finished_UTC':summary['finished_UTC'],'freeze_pin_recheck_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'PRs':rows})
own=f5['source'];actual=g('rev-parse','refs/heads/codex/ab34-space-readers^{commit}').decode().strip();g('cat-file','-e',actual+'^{commit}');assert actual==own
remote=g('rev-parse','refs/remotes/origin/codex/ab34-space-readers^{commit}').decode().strip();assert remote==own
pr252=subprocess.run(['git','--no-optional-locks','-C',str(R),'rev-parse','--verify','refs/remotes/origin/pr/252^{commit}'],stdout=subprocess.PIPE,stderr=subprocess.PIPE);fetch252=pr252.stdout.decode().strip() if pr252.returncode==0 else None
if fetch252 is not None:assert fetch252==own;g('cat-file','-e',fetch252+'^{commit}')
write('OWN-PR252-SOURCE-BINDING.json',{'PR':252,'PR_number_provenance':'Parent explicitly reported subsequently created #252 in task steering; reviewer did not query GitHub or mutate refs.','authorized_source':own,'local_branch':'refs/heads/codex/ab34-space-readers','remote_named_ref':'refs/remotes/origin/codex/ab34-space-readers','local_remote_heads_exact':True,'fetched_numeric_PR252_ref_source_if_present':fetch252,'already_in_initial_587_ref_census':True,'five_complete_reader_chunks_exact_approved_API_only_patch_insertions':True,'reader_bindings_file':'APPROVED-FIVE-BINDING.json','independent_source_twin':False,'scope':'Own authorized implementation is distinct from the supplied earlier 16-PR inventory, not a newly discovered competing public API.'})
# Explicitly enumerate named prepared/delivery ref sources as well as all-ref coverage.
prep=[]
for row in cov['commit_source_trees']:
 matches=[r for r in row['aliases'] if r.startswith(('refs/delivery/','refs/deliv/','refs/deliver/','refs/fills/','refs/f6/','refs/f7/','refs/review/')) or any(x in r for x in ['/landing','-landing','/fill/','/fills/','/prepared/','current7-final','current8-final'])]
 if matches:prep.append({'source':row['commit'],'matching_named_prepared_delivery_refs':matches,'all_aliases':row['aliases'],'TCSlib_Lean_files':row['TCSlib_Lean_count'],'all_relevant_candidate_chunk_SHA256s':sorted(percommit[row['commit']])})
write('PREPARED-DELIVERY-REF-COVERAGE.json',{'named_sources':prep,'selection_rule':'An additional index of aliases containing prepared/delivery/landing/fill naming, plus captured current7/current8. This is not the census filter: every available ref name was included regardless of naming.','all_refs_and_tree_bindings':'REF-COVERAGE.json','source_path_scope':'TCSlib/**/*.lean plus TCSlib.lean for all available ref/worktree HEAD trees; current records campaign loose source/patch data also searched. Exchange orphan trees with no TCSlib source have zero source files; archives and unavailable remote revisions are outside this source-text census.'})
# Final concise gate129 live-name/chunk check, separate from gate130.
three_live=[]
for h,name in three.items():
 carriers=[]
 for c in cs:
  if c['chunk_sha256_without_capture_LF']!=h:continue
  for b in by[c['source_blob']]['source_bindings']:
   if b['kind']!='ref_source':continue
   for rev in b['commits']:carriers.append((rev,b['path']))
 carriers=sorted(set(carriers));three_live.append({'name':name,'chunk_SHA256_without_capture_LF':h,'live_source_carriers':[{'source':rev,'path':path,'ref_aliases':aliases[rev]} for rev,path in carriers]})
assert len(three_live)==3
for r in three_live:
 n=len(r['live_source_carriers']);assert n==(2 if r['name']=='Turing.FinTM.controlAction_def' else 1),(r['name'],n)
write('GATE129-FINAL-LIVE-NAME-CHECK.json',{'bounded_16_PR_snapshot_source':'OPEN-PR-CANDIDATE-COVERAGE.json','current_251_source':g129['heads']['origin/pr/251'],'known_248_peer_source':g129['heads']['origin/pr/248'],'current_three_reader_chunks_exact_prior_approved_alignment':True,'full_controlAction_def_doc_name_statement_proof_exact_peer':True,'three_readers':three_live,'new_independent_public_twin_identified_in_this_census':False,'limits':'Current #251 owner files contain later mechanical proof repairs; only reader-chunk equality with approved alignment is asserted. No Lean, metadata, seal, screen, replay, peer merge, debt, naming, gate-status or merge decision.'})
(O/'GATE129-FINAL-LIVE-NAME-CHECK.md').write_text('''# Gate129 final source check

The bounded 16-PR snapshot is `OPEN-PR-CANDIDATE-COVERAGE.json`; it is not a new live GitHub inventory. Current #251 is `0f926779de590194f5222277dc038d2ad097ff91` and the established #248 peer remains `32b827c017bc321ea40577bc8f27131df2c35e1a`.

All three current #251 reader chunks exactly retain the approved alignment. The complete doc/name/statement/proof chunk of `Turing.FinTM.controlAction_def` is byte-identical to #248, SHA256 `ec9b6ee89ce4d3119c1f45f4fcdd5195a2081d33af9026ac43de8969a77d9cb7`. Its only captured live carriers are those two source heads. `Turing.inputMoveAction_eq` and `Turing.inputFoldTM_tr_bwd` have only #251 live carriers in this census. No new independent public reader twin was identified within the recorded name/shape enumeration.

The owner files have later mechanical proof repairs, so whole-owner equality with the earlier aligned source is not claimed. This is source inspection only, with no Lean, metadata, seal, screen, replay, peer-merge or gate/merge-status claim. Complete chunks and all ref bindings are in `GATE129-ALIGNMENT.json` and `GATE129-FINAL-LIVE-NAME-CHECK.json`.
''')
# Ref fence; preserve any changes as data instead of relabelling the initial population.
latest=g('for-each-ref','--format=%(refname) %(objectname)').decode();initial=(O/'ALL-REFS.raw.txt').read_text();(O/'ALL-REFS.freeze.raw.txt').write_text(latest)
write('FINAL-BOUNDS.json',{'freeze_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'initial_all_ref_names':summary['all_available_ref_names'],'initial_unique_source_heads_including_worktree_HEADs':summary['unique_commit_heads_including_worktree_HEADs'],'refs_stable_during_initial_capture':summary['refs_unchanged_during_snapshot'],'refs_still_equal_at_freeze':latest==initial,'provided_16_PR_pins_revalidated_at_freeze':True,'own_authorized_252_source_bound_separately':True,'legacy_worktree_working_byte_read_errors':len(cov['worktree_read_errors']),'legacy_worktree_committed_HEAD_objects_still_included':True,'no_independent_live_GitHub_PR_inventory_query_by_reviewer':True,'current_record_files_bound_to_initial_records_HEAD':summary['records_HEAD']})
review=f'''# Gate130 name and statement-shape census

Within the recorded source-text population, no independent public twin of the five approved readers was identified. The five complete doc/name/statement/proof chunks exactly match the approved API-only patch insertions and occur in live library source only at the authorized #252 implementation `{own}` (`codex/ab34-space-readers`). No name, statement, import, duplication-retention, audit or merge decision is made here.

The names are `Turing.MultiTapeTM.ConfigCount.core_eq`, `Turing.ClockHost.bootCfg_of_halt`, `Turing.ClockHost.runCfg_initCfg`, `Turing.FinTM.sweepRevCfg_state`, and `Turing.FinTM.sweepRevCfg_output`. `APPROVED-FIVE-BINDING.json` freezes their full source/ref/Git-blob/SHA256 bindings and exact approved-patch equality.

The fresh capture ran {summary['started_UTC']} to {summary['finished_UTC']}. It covered all **587** available ref names, **391** distinct source heads including registered worktree HEAD objects, **385** full tree objects, every `TCSlib/**/*.lean` plus `TCSlib.lean` at those heads, **18,106** current-record campaign loose source/patch paths, and **61** dirty/untracked Lean byte files. This produced **6,775** unique source/byte objects (**341,539,296 bytes**), **27,264** uncapped raw hit lines, **15,017** candidate source rows and **1,035** complete distinct candidate chunks. All chunks have dispositions and captures; all **333** parser-skipped prepared source objects (**365** views) are also captured completely. No live TCSlib source file was skipped by the named-declaration parser.

`OPEN-PR-CANDIDATE-COVERAGE.json` explicitly binds the **16 supplied PR pins**, each checked against its fetched ref at capture and freeze. This remains a bounded 16-PR snapshot, not a claim about every current GitHub PR after that inventory. The subsequently created own #252 is bound separately in `OWN-PR252-SOURCE-BINDING.json`. Initial refs stayed fixed during the scan; final fences are retained. Every named prepared/delivery ref was included irrespective of naming, with an additional explicit index in `PREPARED-DELIVERY-REF-COVERAGE.json`.

After capture, the sole changed ref was the campaign records pointer from `ae0fe1899245d40ed8f4e46926d35cfaddb534d6` to `54f964075dacf438a8ef34eeccbc6f5c49943b35`. Its complete TCSlib path/mode/blob listing is byte-identical to the captured head; `POST-CAPTURE-REF-DELTA.json` retains the full changed-path list and both bindings. New records data was not re-enumerated. The 16 supplied PR pins and own #252 source remain exact.\n\nThe earlier 428-ref/298-head prototype searches are prior data, independently hash-checked and bound in `PRIOR-PROTOTYPE-BINDINGS.json`; they are not presented as fresh. Existing core step/run/injectivity/code facts transport or compare opaque cores; boot/attempt contracts state live steps/runs/startup/timeout behavior; reverse-sweep action/run facts change or iterate configurations. Their recorded premises and conclusions differ from the five raw reader equations. Broad four-field and Action-constructor hits were retained and dispositioned. Probe examples, evidence copies and body-only reads are distinguished from independently published reader statements; no debt/repair ruling is inferred.

The separate current gate129 check is `GATE129-FINAL-LIVE-NAME-CHECK.md` and its JSON. It preserves the known exact `controlAction_def` alignment and identifies no new independent twin within this census for the other two reader statements.

Limits: candidate enumeration plus retained statement/chunk inspection, not semantic completeness or global API absence. The reviewer did not query/fetch GitHub. Source/patch text is the population; archives and unavailable revisions are outside it. There are **120** stale legacy worktree Git-link read errors, each preserved in `REF-COVERAGE.json`; their available committed HEAD objects are still included. Current working bytes beyond the exact captured set are not asserted. No received scripts, Lean, screen, lint, seal or replay were executed. Only this fresh private directory was written; no source, Git, R/X, commit, push, dispatch, outside-chat message or decision action occurred.

Full uncapped raw/name/shape data, exact per-candidate dispositions and complete chunks are retained. The 51 MB transient repeated source-location map was replaced by content hashes for all scanned blobs and compact full bindings for every relevant source; no source/candidate binding was silently capped. `MANIFEST.json` and `SHA256SUMS` freeze the packet.
'''
(O/'REVIEW.md').write_text(review)
(O/'README.md').write_text('Read REVIEW.md first. GATE129-FINAL-LIVE-NAME-CHECK.md is the separate concise gate129 result. OPEN-PR-CANDIDATE-COVERAGE.json is the bounded 16-PR snapshot; OWN-PR252-SOURCE-BINDING.json is the separately reported authorized source. Every source/candidate/hit/chunk population is uncapped. Scripts are read-only source review helpers, not Lean/screen execution. enumerate.py creates an intermediate full-location map; finish_review.py replaces it with compact hashes/bindings; freeze.py writes final bounds, review and manifest.\n')
# Inspectable artifact manifest without a circular self-hash.
excludes={'MANIFEST.json','SHA256SUMS','FROZEN.json'};files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in excludes:files.append({'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'SHA256':H(p.read_bytes())})
write('MANIFEST.json',{'frozen_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':files,'file_count':len(files),'total_bytes':sum(f['bytes'] for f in files),'self_hash_policy':'MANIFEST.json, SHA256SUMS and FROZEN.json are excluded to avoid circular hashes; SHA256SUMS additionally covers MANIFEST.json, and FROZEN.json pins both.'})
sums=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ['SHA256SUMS','FROZEN.json']:sums.append(H(p.read_bytes())+'  '+str(p.relative_to(O)))
(O/'SHA256SUMS').write_text('\n'.join(sums)+'\n')
freeze={'directory':str(O),'frozen_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'MANIFEST_SHA256':H((O/'MANIFEST.json').read_bytes()),'SHA256SUMS_SHA256':H((O/'SHA256SUMS').read_bytes()),'REVIEW_SHA256':H((O/'REVIEW.md').read_bytes()),'manifest_artifact_count':len(files),'manifest_total_bytes':sum(f['bytes'] for f in files),'no_new_independent_public_twin_identified_within_recorded_bounds':True,'all16_pins_revalidated':True,'own252_source':own,'current129_source':g129['heads']['origin/pr/251']};write('FROZEN.json',freeze)
print(json.dumps(freeze,indent=2))
