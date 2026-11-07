"""Verify the final linked source/text-screen evidence, without rerunning tiling or Lean."""
from pathlib import Path
import datetime, hashlib, json, os, re
p=Path(__file__).resolve().parent;old=p.parent/'screen-current25-phase2'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
capture=json.loads((p/'capture.json').read_text());assert capture['count']==25
assert capture['previous136_entry_manifest_verified'] and capture['current_sources_stable_during_capture']
for line in (old/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1);assert sha(old/name)==h
assert len((old/'SHA256SUMS').read_text().splitlines())==136
assert sha(p/'base.out')==sha(old/'base.out') and sha(p/'previous-head.out')==sha(old/'head.out')
assert (p/'copy-text-screen-v3.py.txt').read_bytes()==(old/'copy-text-screen-v3.py.txt').read_bytes()
for row in capture['files']:
 for label in ['base','previous-head','head']:
  assert sha(p/'inputs'/label/(row['path']+'.txt'))==row[label+'_sha256']
assert len(list((p/'inputs').rglob('*.lean.txt')))==75
run=json.loads((p/'head.json').read_text());assert run['exit']==0 and run['fresh_tiling_runs_this_phase']==1
assert run['output_sha256']==sha(p/'head.out') and run['screen_sha256']==sha(p/'copy-text-screen-v3.py.txt')
assert run['command'][:3]==['nice','-n','10'] and '-I' in run['command']
for label,new,gone in [('vs-base',54,1128),('vs-phase2',2,1)]:
 r=json.loads((p/(label+'.json')).read_text());assert r['exit']==0
 assert r['output_sha256']==sha(p/(label+'.out')) and r['pairdiff_sha256']==sha(p/'pairdiff.py.txt')
 text=(p/(label+'.out')).read_text()
 assert len(re.findall(r'^  NEW ',text,re.M))==new
 assert len(re.findall(r'^  GONE ',text,re.M))==gone
 rows=json.loads((p/(label+'-classifications.json')).read_text())
 assert len(rows)==len({(x['target'],x['source']) for x in rows})==new
assert len(json.loads((p/'all-six-tagged-instance-candidates.json').read_text()))==6
qa=json.loads((p/'targeted-reuse.json').read_text());assert len(qa['exact_three_tagged_run_drivers'])==3
assert all(r['uses_Set_MapsTo_iterate'] and r['uses_add_right_iterate'] and not r['contains_induction'] for r in qa['exact_three_tagged_run_drivers'])
assert json.loads((p/'one-body-index-change.json').read_text())['only_changed_normalized_screen_body']==['Primitives.lean::fwdMapVirtual_run']
events=[json.loads(x) for x in (p/'lock-events.jsonl').read_text().splitlines()]
assert [(x['action'],x['label']) for x in events]==[('acquired','final-head'),('released','final-head')]
assert len({x['pid'] for x in events})==1
link=json.loads((p/'pushed-head-linkage.json').read_text())
assert link['commit']=='b1f553b315f31b949076e91119473ce4070e7d53'
assert link['full_commit_and_25_full_blob_objects_verified'] and link['all_25_source_bytes_equal']
assert link['local_tracking_ref_matches'] and link['extra_tiling_runs']==0
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
live={row['path']:sha(wt/row['path']) for row in capture['files']}
assert all(live[row['path']]==row['head_sha256'] for row in capture['files'])
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'fresh_head_screens':1,'baseline_and_phase2_executions_reused':True,
 'all75_source_inputs_raw_outputs_and_tool_hashes_verified':True,'shared_lock_sequence_verified':True,
 'base_candidates':1696,'phase2_candidates':621,'final_candidates':622,
 'all54_baseline_new_and2_phase2_new_edges_classified_once':True,'all_six_tagged_instance_scores_retained':True,
 'exact_three_tagged_drivers_use_existing_iterator_no_induction':True,
 'live_all25_actual_sources_equal_capture':True,'live_hashes':live,
 'previous136_entry_manifest_untouched':True,'pushed_source_commit':link['commit'],
 'read_only_commit_and25_blob_linkage_verified':True,'no_Lean_source_Git_cache_or_snapshot_mutation':True,
 'limits':'Bounded text/source review; no rule-10 seal, semantic-debt approval, replay or gate clearance.'}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='live_hashes'},indent=2))
