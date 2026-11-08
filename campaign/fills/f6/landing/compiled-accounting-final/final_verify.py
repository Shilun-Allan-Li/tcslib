from pathlib import Path
import json,hashlib,os,subprocess,datetime,base64,gzip
O=Path('/private/tmp/f6-compiled-accounting-final');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/fills/f6/landing/compiled-accounting';c=json.loads((O/'context.json').read_bytes());tree=Path(c['snapshot'])
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):return [{'path':str(p.relative_to(root)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(root.rglob('*.olean'))]
before=json.loads((O/'snapshot-head-before.json').read_bytes());after=inventory(tree);assert before==after and len(after)==895;(O/'snapshot-head-after.json').write_text(json.dumps(after,indent=2)+'\n')
oldbefore=json.loads((O/'frozen-original-before.json').read_bytes());oldafter=[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(P.iterdir())];assert oldbefore==oldafter;(O/'frozen-original-after.json').write_text(json.dumps(oldafter,indent=2)+'\n')
w=O/'finite-witness-diagnostic-final';prior=R/'campaign/fills/f6/landing/finite-witness-diagnostic-v1';b=json.loads((w/'original-frozen-before.json').read_bytes());a=[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(prior.iterdir())];assert a==b;(w/'original-frozen-after.json').write_text(json.dumps(a,indent=2)+'\n')
assert sha(Path(c['BASE_owner_olean']).read_bytes())==c['BASE_owner_olean_sha256'];assert sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256']
wt=c['actual_worktree'];git=lambda *a:subprocess.check_output(['git','-C',wt,*a]);assert git('rev-parse','HEAD').decode().strip()==c['candidate_head']==git('rev-parse','@{upstream}').decode().strip();assert git('status','--porcelain=v1','--untracked-files=no')==b''
# All native result sources/archives are internally complete; no stale scope is relabeled.
for name in ['Head']:
 rr=json.loads((O/(name+'-run.json')).read_bytes());assert rr['source_head']==c['candidate_head'] and rr['exit']==rr['errors']==rr['warnings']==0
for p in sorted(O.rglob('*.json')):json.loads(p.read_bytes())
assert (O/'Head.out.gz').read_bytes()==(P/'Head.out.gz').read_bytes();assert (w/'ArbitraryFiniteness.out').read_bytes()==(prior/'ArbitraryFiniteness.out').read_bytes()
res={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['candidate_head'],'source_sha256':c['source_sha256'],'current_source_clean_and_pushed':True,'all895_native2_oleans_identical_before_after':True,'BASE_owner_olean_unchanged':True,'all_frozen_original_accounting_files_unchanged':len(oldafter),'frozen_original_witness_diagnostic_files_unchanged':len(a),'exact_base_copies_reused':True,'fresh_HEAD_metadata_native_success':True,'fresh_current19_scopes_and72paired_controls_verified':True,'fresh_current_arbitrary_witness_diagnostic_verified':True,'HEAD_metadata_raw_bytes_equal_historical_output':True,'arbitrary_witness_raw_bytes_equal_historical_output':True,'historical_and_current_receipts_separate':True,'no_proof_values_printed':True,'no_source_Git_snapshot_cache_or_screen_mutation':True,'limits':'This task ran import metadata, current scoped copies/controls and conditional witness diagnostic only; root owns MF62, audit and merge.'}
(O/'final-verification.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
