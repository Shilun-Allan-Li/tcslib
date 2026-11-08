"""Finalize a new records-only candidate packet; no source/Git/native/screen mutation."""
from pathlib import Path
import base64,collections,datetime,gzip,hashlib,json,os,re,subprocess
out=Path(__file__).resolve().parent;root=out.parents[4];gate=root/'campaign/gates/119-mig1-followup-api'
H=lambda b:hashlib.sha256(b).hexdigest();env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
head='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';api='1160c18f03fd318f0dec25738790935fa61379d4';reference='626b1a81ddd33f4b0e0dabd4e874a16a0fe71724'
def git(*a):return subprocess.run(['git','-C',str(root),*a],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env).stdout
for c in [head,base,api,reference]:assert git('rev-parse',c+'^{commit}').decode().strip()==c and git('cat-file','-t',c).strip()==b'commit'
assert not git('diff','--name-only',api,base,'--','*.lean').strip()
assert not git('diff','--name-only',reference,head,'--','*.lean').strip()
subprocess.run(['git','-C',str(root),'merge-base','--is-ancestor',base,head],check=True,env=env)
changed=git('diff','--name-only',base,head,'--','*.lean').decode().splitlines();assert len(changed)==5
screen=gate/'review/source-lint-screen';pop=(screen/'population.txt').read_text().splitlines();assert len(pop)==len(set(pop))==16
sources=[]
for f in pop:
 row={'path':f}
 for side,pin in [('base',base),('head',head)]:
  b=git('show',pin+':'+f);assert b==(screen/'inputs'/side/(f+'.txt')).read_bytes();row[side+'_sha256']=H(b)
 sources.append(row)
pre=json.loads((gate/'evidence/preflight/receipt.json').read_text());assert pre['failures']==0
for r in pre['runs']:assert H(git('show',head+':'+r['source']))==r['source_sha256']
freeze=json.loads((gate/'source/whole-source-freeze.json').read_text())
for r in freeze['source_scope']:
 assert H(git('show',base+':'+r['path']))==r['before_sha256'] and H(git('show',head+':'+r['path']))==r['after_sha256']
# All recorded replay bytes, summary rows, exact module order and effective invocations.
rp=gate/'evidence/replay-mfup2';rr=json.loads((rp/'receipt.json').read_text());assert rr['result']=='PASS' and rr['pipeline_exit']==0 and rr['head']==head and rr['modules']==401
for r in rr['evidence']:
 b=(rp/r['path']).read_bytes();assert len(b)==r['bytes'] and H(b)==r['sha256']
order=(rp/'down-mfup2.txt').read_text().splitlines();assert len(order)==len(set(order))==401 and 'TCSlib' not in order
text=(rp/'replay-mfup2.log').read_text();lines=text.splitlines();assert lines[-1]=='# modules=401 failed=0' and lines[0].startswith('# replay-mfup2 at '+head[:9]+':')
rows=[]
for line in lines[1:-1]:
 m=re.fullmatch(r'(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)',line);assert m,line;rows.append(m.groups())
assert [r[0] for r in rows]==order and all(r[1:3]==('0','0') for r in rows)
assert sum(int(r[3]) for r in rows)==77
static=(rp/'replay-mfup2-static.txt').read_text();assert static=='modules 401, mismatches 0, static total 77\n'
launch=[]
for line in (rp/'replay-mfup2-launches.log').read_text().splitlines():
 m=re.fullmatch(r'pid=(\d+) -j4 (\S+)\.lean -o (\S+)\.olean',line);assert m,line
 pid,f,dest=m.groups();assert dest=='/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mfup2/'+f;launch.append(f)
assert launch==order
assert (rp/'actual-branch-lean_check_tree.sh').read_bytes()==git('show',head+':scripts/lean_check_tree.sh')
assert b'lean -j4 ' not in (rp/'actual-branch-lean_check_tree.sh').read_bytes()
assert (rp/'generated-original.sh').read_text().replace('cp -R ','cp -cR ')==(rp/'replay-mfup2.sh').read_text()
assert 'lean4---v4.25.0/bin/lean' in (rp/'run.sh').read_text() and 'replay-j4/bin:$PATH' in (rp/'run.sh').read_text()
assert '"${TCSLIB_REPLAY_REAL_LEAN:?}" -j4 "$@"' in (rp/'lean-j4-shim.sh').read_text()
campaign=rr['campaign_at_receipt'];assert git('rev-parse',campaign+'^{commit}').decode().strip()==campaign;assert not git('diff','--name-only',base,campaign,'--','*.lean').strip()
part=gate/'evidence/replay/partial-mfup1';pr=json.loads((part/'receipt.json').read_text());partial=(part/'replay-mfup1.log').read_text()
for r in pr['evidence']:
 b=(part/r['path']).read_bytes();assert len(b)==r['bytes'] and H(b)==r['sha256']
prows=[re.fullmatch(r'(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)',l).groups() for l in partial.splitlines() if re.fullmatch(r'(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)',l)]
assert len(prows)==272 and [r[0] for r in prows]==order[:272] and all(r[1:3]==('0','0') for r in prows)
assert '# modules=401 failed=0' not in partial
# Independent raw screen-row/index/delta reconciliation; no tiling tool execution.
def parse(side):
 t=(screen/(side+'.out')).read_text();r=json.loads((screen/(side+'-run.json')).read_text());assert H(t.encode())==r['output_sha256'] and len(t.encode())==r['bytes'] and r['exit']==0
 summary=re.fullmatch(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',t.splitlines()[0]);assert summary
 idx={d['label']:d for d in json.loads((screen/(side+'-index.json')).read_text())};result=[]
 for line in t.splitlines()[1:]:
  m=re.fullmatch(r'\s+(.+?)  reproduces  (.+?): (\d+)/(\d+) = (\d+)%',line);assert m,line
  a,b,n,d,pct=m.groups();assert a in idx and b in idx and idx[a]['kind']==idx[b]['kind'];assert int(d)==idx[b]['body_chars']
  result.append({'a':a,'b':b,'shared':int(n),'denominator':int(d),'printed_percent':int(pct),'kind':idx[a]['kind'],'cross_file':idx[a]['path']!=idx[b]['path']})
 assert len(result)==int(summary[2]) and len(idx)==int(summary[1]) and sum(x['shared'] for x in result)==int(summary[3].replace(',',''))
 assert len({(r['a'],r['b']) for r in result})==len(result)
 assert result==json.loads((screen/(side+'-candidates.json')).read_text())
 return result,{'eligible_declarations':len(idx),'directed_candidates':len(result),'directed_shared_chars':sum(x['shared'] for x in result),'kind_location':dict(collections.Counter(x['kind']+('/cross-file' if x['cross_file'] else '/in-file') for x in result))}
b,bm=parse('base');h,hm=parse('head');bd={(r['a'],r['b']):r for r in b};hd={(r['a'],r['b']):r for r in h}
new=[hd[k] for k in sorted(hd.keys()-bd.keys())];gone=[bd[k] for k in sorted(bd.keys()-hd.keys())];alter=[k for k in hd.keys()&bd.keys() if hd[k]!=bd[k]]
assert (len(b),len(h),len(new),len(gone),len(alter))==(2222,2228,6,0,0)
delta=json.loads((screen/'pair-delta.json').read_text());assert new==delta['new'] and not delta['gone'] and not delta['changed_measurements']
classification=json.loads((screen/'new-candidate-classification.json').read_text());assert {(r['a'],r['b']) for r in classification}=={(r['a'],r['b']) for r in new} and len(classification)==6
# Archive current scratch replay inputs as text, separately attributed to capture time.
scratch=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch');toolrows=[]
for rel,canon in [('tools/mk-next.sh','devtools/seyoon/mk-next.sh'),('tools/mkdownmulti.py','devtools/seyoon/mkdownmulti.py'),('tools/mkreplay.py','devtools/seyoon/mkreplay.py'),('api/slotrun.sh','devtools/seyoon/scratch-api/slotrun.sh'),('api/staticsorry.py','devtools/seyoon/scratch-api/staticsorry.py')]:
 f=scratch/rel;b=f.read_bytes();b.decode('utf-8');dest=out/'tools'/('scratch-'+rel.replace('/','__')+'.txt');dest.write_bytes(b)
 toolrows.append({'captured_from':str(f),'inert_copy':str(dest.relative_to(root)),'sha256':H(b),'canonical_path':canon,'equals_current_canonical_bytes':b==(root/canon).read_bytes(),'scope':'Read after completed replay; not an independently recorded launch-time hash. Do not execute as delivered code.'})
current_helper=(root/'scripts/lean_check_tree.sh').read_bytes();assert b'lean -j4 ' in current_helper
(out/'tools/current-records-lean_check_tree.sh.txt').write_bytes(current_helper)
actualhelper=(rp/'actual-branch-lean_check_tree.sh').read_bytes()
(out/'tool-provenance.json').write_text(json.dumps({'actual_pinned_branch_helper':{'path':str((rp/'actual-branch-lean_check_tree.sh').relative_to(root)),'source_head':head,'sha256':H(actualhelper),'explicit_j4':False,'verified_exact_Git_blob':True},'effective_current_replay':'Archived run.sh selects pinned4.25 shim; all401 retained actual launches explicitly pass-j4. No source-pinned helper relabel.','later_records_helper':{'path':'scripts/lean_check_tree.sh','captured_copy':str((out/'tools/current-records-lean_check_tree.sh.txt').relative_to(root)),'sha256':H(current_helper),'explicit_j4':True,'scope':'Later permanent records/campaign correction for future pipelines; not the actual branch helper used in mfup2. Root pins after its records commit.'},'scratch_inputs_captured_after_completion':toolrows},indent=2)+'\n')
# Exact full metadata UTF8 archives retain every native output byte; never execute recovered data.
u=json.loads((gate/'review/compiled-comparison/utf8-archives-verification.json').read_text());archives=[]
for r in u['archives']:
 enc=(gate/'review/compiled-comparison'/r['utf8_file']).read_bytes();z=base64.b64decode(b''.join(enc.split()),validate=True);raw=gzip.decompress(z)
 assert (len(enc),H(enc))==(r['utf8_bytes'],r['utf8_sha256']);assert (len(z),H(z))==(r['gzip_bytes'],r['gzip_sha256']);assert (len(raw),H(raw))==(r['raw_stdout_stderr_bytes'],r['raw_stdout_stderr_sha256']);raw.decode('utf-8');archives.append({'endpoint':r['endpoint'],'complete_lossless_UTF8_archive_verified':True,'raw_bytes':len(raw),'raw_sha256':H(raw)})
(out/'source-linkage.json').write_text(json.dumps({'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':base,'API_metadata_baseline':api,'head':head,'source_byte_reference':reference,'all_commit_objects_verified':True,'base_ancestor_of_head':True,'API_to_merged_base_full_Lean_diff_empty':True,'reference_to_current_source_full_Lean_diff_empty':True,'exact_five_changed_Lean_files':changed,'all_five_preflight_and_whole_freeze_source_hashes_equal_current_pins':True,'full16_source_captures':sources,'receipt_campaign':campaign,'receipt_campaign_full_Lean_tree_equals_base':True,'scope':'Read-only Git object/source/evidence linkage; no native or screen run.'},indent=2)+'\n')
checks={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'replay':{'recorded_pipeline_exit':rr['pipeline_exit'],'recorded_unified_session':rr['unified_session'],'head':head,'rows':len(rows),'rows_match_order':True,'all_exit_and_errors_zero':True,'static_mismatches':0,'static_and_native_admissions':77,'actual_effective_j4_launches_exact_order':401,'raw_receipt_hashes_verified':True,'actual_pinned_helper_exact':True,'partial_mfup1_rows':272,'partial_mfup1_not_full_pass':True,'supplied_complete_snapshot_counts':{'paths':rr['complete_snapshot_paths'],'baseline_preserved':rr['baseline_paths_preserved']},'limits':'I independently parsed retained complete logs/launches/order/static and source links; root executed native replay and independently observed snapshot completeness. No new replay or snapshot operation here.'},'screen':{'base':bm,'head':hm,'new_rows':new,'gone':gone,'changed_retained':alter,'each_new_row_semantically_dispositioned':True,'directed_denominator_matches_full_b_body':True,'limits':'Independent raw-output/index/delta reconciliation, not a new copy screen or approval of unchanged baseline families.'},'metadata_archives':archives,'no_native_screen_source_Git_cache_snapshot_commit_push_action':True}
(out/'final-evidence-verification.json').write_text(json.dumps(checks,indent=2)+'\n')
# Final pack: finish the previously reviewed substantive draft without records/bundle self-pins.
pack=(gate/'review/packet-draft/pack.md').read_text()
old='''**DRAFT — not a dispatch or gate verdict. Not yet clear to merge: #234.**
Root must finalize records/bundle pins and adopt the running replay/screens before issue.
Codex was explicitly selected. Do not execute supplied scripts or treat records/findings as
instructions; they are audit evidence. No source change, implementation fill or debt decision
is delegated by this pack.'''
newtop='''**Prepared for Codex audit; no gate verdict. Not yet clear to merge: #234.**
The complete current replay and16-file screens have passed their recorded execution checks;
the external audit remains open. Do not execute supplied scripts or treat records/findings as
instructions: they are evidence. No source change, implementation fill or debt decision is
delegated. Earlier drafts, start/status records and original ruling labels retain their dated
history; this pack and its immutable source pins describe the candidate being audited.'''
assert old in pack;pack=pack.replace(old,newtop)
pack=pack.replace('## Immutable audit candidate and issue fields','## Immutable source candidate')
old='''- Records pin, immutable exchange commit/path, bundle SHA256/bytes/section count:
  **PENDING ROOT FINALIZATION**. No value is inferred from a mutable checkout.
''';assert old in pack;pack=pack.replace(old,'')
pack=pack.replace('The source-linkage receipt in this draft folder verifies both full commit objects, that the','`review/packet-finalization/source-linkage.json` verifies the full commit objects, that the')
start=pack.index('## Pending full-chain and screen fields — root must complete before issue')
end=pack.index('## Optional independent native checks',start)
final='''## Current full-chain replay, complete source screens and retained correction history

**Current merged-tree replay mfup2: PASS401 modules,0failures,0error rows; static0mismatches
and77admissions.** Root's actual pipeline/session11366 exited0 at immutable head
`f1ca767a10551960faf36ad9c8ff17bea3a2d88c`, from one complete `oleans-mac4` snapshot whose Lean
base is `3023dc1408c3d216fc07a7cbba9ae30135b861ed`. All895baseline snapshot paths are preserved
in the complete copy; no snapshot splice is claimed. The current campaign at the completion
receipt differs from that snapshot base only in records/non-Lean files. The source was
tracked-clean and exactly pushed at receipt. The supplied order is the computed401-module
closure and excludes the root TCSlib module, as prescribed by the replay rule.

`evidence/replay-mfup2/` supplies the complete recorded401-row replay log, order, static
output,401actual -j4 launch records, receipt, original/generated and actual replay/precheck
scripts, source start/linkage and the enforcing launcher/shim. Independent offline parsing in
`review/packet-finalization/final-evidence-verification.json` checks every module/order row,
all exits/errors, all actual launch paths/flags, static total and exact raw receipt hashes.
It does not claim a second execution or independently inspect the snapshot's895file contents.

**Exact tool provenance matters.** The source-pinned branch's archived
`actual-branch-lean_check_tree.sh` is the real helper and still calls bare `lean` without an
explicit -j4. The isolated PATH shim selected the absolute Lean4.25 executable and added -j4
from the first actual invocation; all401retained effective command records match the order.
The pipeline separately applied nice10 and outer slotrun. A later permanent -j4 correction
in the canonical campaign/records helper is for future pipelines; it is not relabeled as the
old branch's helper. `effective-pipeline.json` and the finalization `tool-provenance.json`
retain this distinction. The complete snapshot copy differs from the generated script only
by the recorded cp-R→cp-cR APFS copy substitution.

The first generated **mfup1 was intentionally terminated incomplete** because it omitted
required-j4. It had272completed PASS rows, no completed failure row, and no final401-module
pass. Its original626bsource pin, complete partial log/order/scripts, verified process-group
termination records and receipt are retained under `evidence/replay/partial-mfup1/`; its
incomplete snapshot was discarded. mfup2 is the fresh complete replacement, not a continuation
or relabeling of that partial run. This history is distinct from the earlier actual elan4.35
installation/incompatible-olean setup failures documented above.

Both unmodified, full16-file source screens finished with exit0, serially under the shared
screen lock and observed nice10. Their exact archived base/head sources are byte-linked to
current3023/f1ca; both original captures and both reversible archives remain supplied.

| Copy-screen measure | Base | Head |
| --- | ---: | ---: |
| Eligible declarations |2005|2006|
| Directed candidate rows |2222|2228|
| Sum of directed normalized shared characters |738885|740747|
| Proof / cross-file |913|919|
| Proof / same-file |961|961|
| Term / cross-file |163|163|
| Term / same-file |185|185|

All2222old rows and their measurements remain unchanged: six new rows, none gone, no changed
retained score. Direction is **a reproduces b** and the denominator is the complete normalized
b body. These are directed textual candidates, not independent copied-theorem counts.

| a reproduces | b | Shared / complete b |
| --- | --- | ---: |
| Finite::exists_first_entry_of_fixed | Catalog::f2_catalogFirstEntry |249/375 =66%|
| Finite::exists_first_entry_of_fixed | Loop::emCall_first_entry |341/403 =85%|
| Finite::exists_first_entry_of_fixed | Primitives::catalogFirstEntry |249/375 =66%|
| Finite::exists_first_entry_of_fixed | Primitives::emitter_first_entry |341/403 =85%|
| Loop::emCall_first_entry | Finite::exists_first_entry_of_fixed |341/515 =66%|
| Primitives::emitter_first_entry | Finite::exists_first_entry_of_fixed |341/515 =66%|

These are material shared first-entry/fixed-endpoint proofs, not syntax-only false positives.
There are two semantic groups: predicate variants (two old private twins plus the canonical
new theorem) and singleton variants (two old private copies plus that same canonical theorem).
Deduplicate the six directed rows into these five declaration endpoints; do not count the
new canonical theorem twice. Full individual row dispositions and original header/body
contexts are supplied in `new-candidate-classification.json` and `family-source-snippets.md`.
The old predicate twins already match403/403both ways in BASE. The singleton twins are also
identical to each other in BASE. Publication is the approved prerequisite for downstream MIG
reuse; neither this source PR nor these screen results remove the old comparison copies or
acknowledge permanent debt. The auditor must still assess the cumulative family scope under
the actual ledger/rulings and report any uncovered material obligation.

Both new canonical zero-space proofs are52normalized characters, below v3's60-character
eligible threshold; their use of the already-published generic zero-tapes fact is checked
manually and by the scoped native/opaque-consumer evidence, not fabricated as a screen row.
No new same-file or executable term/data candidate appears. The redirect owner relocation
removes no baseline screen candidate, so no textual debt reduction is claimed.

Unmodified canonical lints report77→77inherited style findings, campaign/check8b0FAIL/
7WARN/7INFO→same, and no normalized new diagnostic. These old findings are disclosed without
new waiver. The parser-only index attempt's sandbox nice warning is retained; it was not a
copy screen and is not mislabeled as actual nice10execution. The two real screens separately
have observed nice10and complete raw outputs. These counts do not approve all2222inherited
candidates or establish global semantic absence of duplication.

The full population is `review/source-lint-screen/population.txt`:16whole files covering
all five owners, unchanged prerequisite/model/control homes and substantive comparison
sources. All32before/head captures, full archives, complete candidate/index/raw outputs,
source/lint reviews and exact tools are included without caps. Hardness, ExhaustiveReplay,
NTimeDiagonalizer, Loop and CodeSimulator are substantive comparison coverage, not newly
claimed dependencies; StateRenaming is conservative model context. No literal generic twin
is falsely asserted to occur in every comparison file. Other F6/MIG populations do not
substitute for this named screen, and the scope is not a recursive whole-library screen.

'''
pack=pack[:start]+final+pack[end:]
assert 'PENDING' not in pack and '**DRAFT' not in pack and 'running replay/screens' not in pack
(out/'pack.md').write_text(pack)
print(json.dumps({'source_head':head,'replay_modules':401,'replay_failures':0,'static_total':77,'screen_counts':[2222,2228],'new_rows':6,'pack_bytes':len(pack.encode()),'tool_inputs_archived':len(toolrows)},indent=2))
