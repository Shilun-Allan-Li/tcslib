from pathlib import Path
import json,hashlib,re,collections,subprocess,ast,datetime
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((O/n).read_text())
def write(n,v): (O/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
manifest=read('SEARCHED-SOURCE-BLOBS.json');assert all('locations' in r for r in manifest),'Run enumerate.py first, then finish_review.py exactly once.'
source={r['source_blob_or_working_key']:r for r in manifest};cs=read('CANDIDATES.json');cm=read('CANDIDATE-CHUNKS.json');raw=read('RAW-HITS.json');unparsed=read('UNPARSED-HIT-SURFACES.json');aliases=read('REF-ALIASES.json');summary=read('SUMMARY.json');cov=read('REF-COVERAGE.json')
bychunk=collections.defaultdict(list)
for r in cs:bychunk[r['chunk_sha256_without_capture_LF']].append(r)
oldpath=Path('/private/tmp/ab34-gate129-preflight/CANDIDATE-DISPOSITIONS162.json');old={r['chunk_sha256_without_capture_LF']:r for r in json.loads(oldpath.read_text())}
ns={'re':re};tree=ast.parse((R/'devtools/seyoon/declfreeze.py').read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),'canonical_parser','exec'),ns)
canonical=[];source130=g('rev-parse','refs/heads/codex/ab34-space-readers^{commit}').decode().strip();g('cat-file','-e',source130+'^{commit}');assert source130 in aliases
families=[('configcount-core-proposal','TCSlib/Complexity/SpaceComplexity/ConfigCount.lean',['Turing.MultiTapeTM.ConfigCount.core_eq']),('ndclock-startup-reader-proposal','TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean',['Turing.ClockHost.bootCfg_of_halt','Turing.ClockHost.runCfg_initCfg']),('singletape-sweep-reader-proposal','TCSlib/Complexity/TuringMachine/Sweep.lean',['Turing.FinTM.sweepRevCfg_state','Turing.FinTM.sweepRevCfg_output'])]
for fam,path,names in families:
 patch=R/'campaign/items/dedup'/fam/'2026-11-08/API-only.patch';pb=patch.read_bytes();added='\n'.join(l[1:] for l in pb.decode().splitlines() if l.startswith('+') and not l.startswith('+++'));addedchunks={n:c for n,p,c in ns['chunks'](added)}
 owner=g('show',source130+':'+path);text=owner.decode();ownerchunks={n:c for n,p,c in ns['chunks'](text)};oid=g('rev-parse',source130+':'+path).decode().strip();g('cat-file','-e',oid)
 for name in names:
  chunk=ownerchunks[name];h=H(chunk.encode());assert chunk==addedchunks[name.split('.')[-1]],name
  carries=sorted({(kind,rev,p) for c in bychunk[h] for kind,rev,p in source[c['source_blob']]['locations'] if kind in ['ref_source','working_bytes']})
  assert carries==[('ref_source',source130,path)],(name,carries)
  canonical.append({'name':name,'home':path,'source':source130,'all_source_aliases':aliases[source130],'owner_Git_blob':oid,'owner_SHA256':H(owner),'source_line':text[:text.find(chunk)].count('\n')+1,'chunk_SHA256_without_capture_LF':h,'capture':'candidate-excerpts/'+h+'.lean.txt','approved_API_patch':str(patch.relative_to(R)),'approved_API_patch_SHA256':H(pb),'complete_doc_name_statement_proof_exact_approved_patch_insertion':True,'independent_live_source_carriers_besides_own_approved_implementation':[]})
assert len(canonical)==5;write('APPROVED-FIVE-BINDING.json',{'source':source130,'readers':canonical,'no_rename_statement_import_or_retention_decision':True})
five={r['chunk_SHA256_without_capture_LF']:r for r in canonical};g129=read('GATE129-ALIGNMENT.json');three={r['chunk_SHA256_without_capture_LF']:r for r in g129['three_readers']}
reasons={
 'core_step':'Transports an assumed equality of cores through one deterministic step; it does not expose the four-field tuple.',
 'core_runFrom':'Transports an assumed core equality through a run; it does not expose the core constructor.',
 'core_injOn':'Rules out equal cores at distinct pre-halt run times, under first-halt hypotheses; it does not expose the tuple.',
 'coreCode_inj':'Infers core equality from bounded finite-code equality; it reads a different code contract and does not give the four-field constructor equation.',
 'boot_step':'Relates a live boot configuration to one yardstick-machine step; it is not a halted-boot assembly equation.',
 'boot_run':'Relates a live boot run to the yardstick run, with liveness premises; it is not a halted-boot assembly equation.',
 'initCfg_eq_bootCfg':'Equates the host initial configuration with bootCfg of the yardstick initial configuration; it is not bootCfg of an arbitrary halted configuration.',
 'run_step':'Gives one clock-host attempt step below the timeout; it is not runCfg assembled from A.tm.initCfg.',
 'run_run':'Gives the clock-host attempt-run simulation under a length bound; it does not expose initialized runCfg assembly.',
 'run_run_zero':'Gives the attempt-run simulation from yardstick position zero; it does not expose runCfg of A.tm.initCfg.',
 'timeout_success':'Gives a host timeout transition for a successful halted attempt with singleton output; it does not expose initialized runCfg.',
 'timeout_fail':'Gives the failing-attempt timeout branch; it does not expose initialized runCfg.',
 'startup':'Produces a host-run arrival at initialized runCfg after a bounded startup; its conclusion still contains opaque runCfg and is not its assembly equation.',
 'oneShot':'Gives termination/output equivalence after a fixed attempt run; it does not expose initialized runCfg assembly.',
 'sweepRevCfg_left':'Gives the result of applying a writing left action to a reverse zipper with a nonempty right list; it is not the raw state/output projection equation.',
 'sweepRevCfg_left_any':'Gives the result of a reverse left action for arbitrary right lists; it is not a state/output field reader.',
 'sweep_run_reverse':'Gives the reverse sweep run and folded list/state evolution under a transition-table premise; it is not the raw configuration field reader.',
 'controlAction_apply':'Gives the effect of an action on a supplied configuration; it does not expose the action constructor itself.',
 'step_of_inputMoveAction':'Gives a machine-step configuration update when a live transition equals inputMoveAction; it does not expose the action constructor.',
 'timed_rewind':'Produces a bounded rewind run from a prescribed two-phase transition table; it is not an action or input-fold table equation.',
 'rewind_heads':'Gives a bounded rewind run and head preservation; it is not an action or backward-fold table equation.',
 'rewind_from_any':'Gives existence of a rewind arrival; it is not an action or backward-fold table equation.',
 'c1rc_widen_record':'Encodes a widened multi-tape action as bit fields; it is unrelated to the input-only action constructor or backward-fold table.',
 'rvc_widen_record':'Relates encoded action widening to a bit-level adapter; it is unrelated to the input-only action constructor or backward-fold table.'}
rows=[];live_statement_rows=[];live_exact=[]
for meta in cm:
 h=meta['sha256_without_capture_LF'];cand=bychunk[h];keys=sorted({c['source_blob'] for c in cand});locs=sorted({tuple(x) for k in keys for x in source[k]['locations']});live=[x for x in locs if x[0] in ['ref_source','working_bytes']];flags=sorted({f for c in cand for f in c['flags']});hd=meta['header'];name=meta['name'];short=name.split('.')[-1].split('#')[0];public=bool(re.match(r'(?:theorem|lemma)\b',hd)) and not meta['private'];prior=None
 if h in five:disp='APPROVED_GATE130_DECLARATION_AND_EVIDENCE_COPIES';reason='The complete approved reader chunk occurs only on the current authorized gate130 implementation in live library source; other carriers are proposal/evidence data. It is not a newly found independent twin.'
 elif h in three:
  disp='CURRENT_GATE129_APPROVED_READER';reason='Current #251 exact approved reader chunk. controlAction_def additionally has the established #248 peer whose complete chunk matches byte-for-byte; the other two have only the current #251 source carrier in this census.'
 elif h in old:
  disp='PRIOR_GATE129_EXACT_CHUNK_DISPOSITION_REUSED';prior={'path':str(oldpath),'SHA256':H(oldpath.read_bytes()),'prior_disposition':old[h]['disposition'],'prior_reason':old[h]['source_inspection_reason']};reason='Exact complete-chunk SHA256 match to prior gate129 inspected data; the current source occurrences and ref aliases are freshly bound. '+old[h]['source_inspection_reason']
 elif not live:disp='PREPARED_PROPOSAL_GUARD_PATCH_OR_EVIDENCE_DATA';reason='All carriers are committed campaign source/probe/patch data, not a separately published TCSlib declaration on an available source head. Complete text is retained; probe equations and copies do not constitute an independent public API.'
 elif re.match(r'(?:def|abbrev|instance|structure|inductive|class)\b',hd) or re.match(r'(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)+(?:def|abbrev|instance|structure|inductive|class)\b',hd):disp='DEFINITION_OR_MACHINE_CONSTRUCTION';reason='Definition, abbreviation, instance or machine-construction entry. It constructs or names data rather than proving an independent public reader equation.'
 elif meta['private']:disp='PRIVATE_AUXILIARY_OR_CONSUMER';reason='Private helper/consumer statement and proof, with its full text preserved. It is not a public API twin of one of the approved reader contracts.'
 elif short in reasons:disp='EXISTING_DIFFERENT_PUBLIC_CONTRACT';reason=reasons[short]
 elif any(re.search(p,hd) for p in [r'\bConfigCount\.core\b',r'\bcore\b',r'\bbootCfg\b',r'\brunCfg\b',r'\bsweepRevCfg\b',r'\bcontrolAction\b',r'\binputMoveAction\b',r'\binputFoldTM\b']):disp='OTHER_PUBLIC_STATEMENT_WITH_DIFFERENT_PREMISES_OR_CONCLUSION';reason='The retained statement concerns a simulation, transition effect, finite-code/invariant or run contract rather than any of the five raw configuration reader equations or the three gate129 reader equations. Subject and premises/conclusion are shown verbatim in the header index.'
 elif 'FOUR_FIELD_EQUALITY_STATEMENT_SHAPE' in flags:disp='UNRELATED_CONFIGURATION_FIELD_OR_RUN_STATEMENT';reason='The broad tuple/field pattern matched a different configuration/record/run contract. The header does not state core assembly, halted bootCfg assembly, initialized runCfg assembly, sweepRevCfg state/output, or either input-action/backward-fold reader.'
 elif 'ACTION_CONSTRUCTOR_STATEMENT_SHAPE' in flags:disp='UNRELATED_ACTION_CONSTRUCTION_OR_ENCODING_STATEMENT';reason='The broad Action constructor pattern matched another transition, action effect or encoding contract; it does not identify the approved controlAction/inputMoveAction constructor or inputFoldTM backward table.'
 else:disp='BODY_ONLY_READING_OR_USE_IN_DIFFERENT_DECLARATION';reason='The search terms occur in a definition/proof body, not in a standalone matching public reader statement. Existing unfolds/citations/inline steps are retained as candidates; this census makes no mechanical-repair or debt ruling.'
 row={'candidate_chunk':len(rows)+1,'name':name,'private':meta['private'],'capture':meta['capture'],'chunk_SHA256_without_capture_LF':h,'header':hd,'lines':meta['lines'],'flags':flags,'source_row_count':len(cand),'source_blob_keys':keys,'live_source_binding_count':len(live),'disposition':disp,'source_inspection_reason':reason}
 if prior:row['prior_exact_chunk_data']=prior
 rows.append(row)
 if live and public and any('STATEMENT' in f for f in flags):live_statement_rows.append(row)
 if public and short in ['core_eq','bootCfg_of_halt','runCfg_initCfg','sweepRevCfg_state','sweepRevCfg_output','controlAction_eq','controlAction_def','inputMoveAction_eq','inputFoldTM_tr_bwd']:
  live_exact.append({'name':name,'chunk_SHA256_without_capture_LF':h,'live_carriers':[{'kind':k,'source':c,'path':p,'ref_aliases':aliases.get(c,[])} for k,c,p in live],'all_source_blob_keys':keys,'disposition':disp})
write('CANDIDATE-DISPOSITIONS.json',rows);write('LIVE-STATEMENT-CANDIDATES.json',live_statement_rows);write('EXACT-NAME-DECLARATIONS.json',live_exact)
# All unparsed relevant surfaces are prepared data (examples, commands, proof excerpts or patch fragments), never live source files.
assert all(all(k=='tracked_prepared_data' for k,c,p in source[r['source_blob']]['locations']) for r in unparsed)
(O/'unparsed-prepared-excerpts').mkdir(exist_ok=True);urows=[]
for key in sorted({r['source_blob'] for r in unparsed}):
 b=g('cat-file','blob',key);assert H(b)==source[key]['SHA256'];fn='unparsed-prepared-excerpts/'+H(b)+'.txt';(O/fn).write_bytes(b)
 urows.append({'source_blob':key,'SHA256':H(b),'capture':fn,'views':[r['view'] for r in unparsed if r['source_blob']==key],'disposition':'PREPARED_EXAMPLE_COMMAND_PROOF_OR_PATCH_FRAGMENT','reason':'The canonical named-declaration parser found no candidate in this view. All carriers are campaign data; no live TCSlib source carrier. Complete raw text and uncapped hit lines are preserved for review.'})
write('UNPARSED-PREPARED-DISPOSITIONS.json',urows)
# Keep full bindings only for all relevant hit/candidate sources. Other scanned blobs retain content hashes and full-location hashes/counts.
relevant={r['source_blob'] for r in cs}|{r['source_blob'] for r in raw}|{r['source_blob'] for r in unparsed};compact=[];binding=[]
for row in manifest:
 locbytes=json.dumps(row['locations'],ensure_ascii=False,separators=(',',':')).encode();rr={k:v for k,v in row.items() if k!='locations'};rr['location_count']=len(row['locations']);rr['sorted_full_location_list_SHA256']=H(locbytes);compact.append(rr)
 if row['source_blob_or_working_key'] in relevant:
  grouped=collections.defaultdict(list)
  for kind,rev,path in row['locations']:grouped[(kind,path)].append(rev)
  binding.append({k:v for k,v in row.items() if k!='locations'}|{'source_bindings':[{'kind':kind,'path':path,'commits':sorted(set(commits))} for (kind,path),commits in sorted(grouped.items())]})
write('SEARCHED-SOURCE-BLOBS.json',compact)
(O/'RELEVANT-SOURCE-BINDINGS.json').write_text(json.dumps(binding,ensure_ascii=False,separators=(',',':'))+'\n')
counts=dict(collections.Counter(r['disposition'] for r in rows));report={'frozen_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate_chunks':len(rows),'candidate_source_rows':len(cs),'all_candidate_rows_dispositioned':True,'disposition_counts':counts,'live_public_statement_candidate_chunks':len(live_statement_rows),'approved_gate130_reader_chunks':len(five),'gate129_current_reader_chunks':len(three),'prior_gate129_exact_chunk_dispositions_reused':sum(r['disposition']=='PRIOR_GATE129_EXACT_CHUNK_DISPOSITION_REUSED' for r in rows),'unparsed_prepared_distinct_source_blobs':len(urows),'unparsed_prepared_views':len(unparsed),'all_unparsed_surfaces_are_prepared_data':True,'new_independent_public_reader_twin_identified':False,'known_peer_controlAction_def_alignment_exact':True,'all_records_ref_source_bindings_derive_from_full_git_hashes_and_checked_objects':True,'boundaries':'Source/name/statement-shape census only. Complete candidate and unparsed relevant texts retained without caps; body-only hits are not given a debt or repair ruling. No Lean, seal, screen, lint, source/Git/R/X mutation, outside-chat message, audit dispatch or merge decision by reviewer.'};write('DISPOSITION-SUMMARY.json',report)
lines=['# Candidate dispositions','',f'All {len(rows)} complete unique chunks have dispositions; {len(cs)} source rows bind them to source blobs and exact refs. The complete headers and texts are in JSON and captures; nothing is silently capped.','']
for r in rows:lines.append(f"- `{r['name']}` `{r['chunk_SHA256_without_capture_LF']}` — {r['disposition']}. {r['source_inspection_reason']}")
(O/'CANDIDATE-DISPOSITIONS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(report,indent=2))
