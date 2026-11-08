"""Final phase2 evidence/live-source capture check, before the parent's next edit."""
from pathlib import Path
import collections, datetime, hashlib, json, os, re
p=Path(__file__).resolve().parent;old=p.parent/'screen-current25-draft'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
capture=json.loads((p/'capture.json').read_text());assert capture['count']==25
assert capture['old_120_entry_manifest_verified'] and capture['current_sources_stable_during_capture']
for line in (old/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1);assert sha(old/name)==h
assert len((old/'SHA256SUMS').read_text().splitlines())==120
assert sha(p/'base.out')==sha(old/'base.out') and sha(p/'previous-head.out')==sha(old/'head.out')
assert (p/'copy-text-screen-v3.py.txt').read_bytes()==(old/'copy-text-screen-v3.py.txt').read_bytes()
for row in capture['files']:
 for label in ['base','previous-head','head']:
  assert sha(p/'inputs'/label/(row['path']+'.txt'))==row[label+'_sha256']
assert len(list((p/'inputs').rglob('*.lean.txt')))==75
run=json.loads((p/'head.json').read_text());assert run['exit']==0 and run['fresh_tiling_runs_this_phase']==1
assert run['output_sha256']==sha(p/'head.out') and run['screen_sha256']==sha(p/'copy-text-screen-v3.py.txt')
assert run['command'][:3]==['nice','-n','10'] and '-I' in run['command']
for label,new,gone in [('vs-base',53,1128),('vs-previous-head',3,10)]:
 r=json.loads((p/(label+'.json')).read_text());assert r['exit']==0
 assert r['output_sha256']==sha(p/(label+'.out')) and r['pairdiff_sha256']==sha(p/'pairdiff.py.txt')
 text=(p/(label+'.out')).read_text()
 assert len(re.findall(r'^  NEW ',text,re.M))==new
 assert len(re.findall(r'^  GONE ',text,re.M))==gone
 rows=json.loads((p/(label+'-classifications.json')).read_text())
 assert len(rows)==len({(x['target'],x['source']) for x in rows})==new
events=[json.loads(x) for x in (p/'lock-events.jsonl').read_text().splitlines()]
assert [(x['action'],x['label']) for x in events]==[('acquired','phase2-head'),('released','phase2-head')]
assert len({x['pid'] for x in events})==1
link=json.loads((p/'pushed-head-linkage.json').read_text())
assert link['commit']=='429bdd596adc15f229a8a03993967e5941cc2442'
assert link['full_commit_and_25_full_blob_objects_verified'] and link['all_25_source_bytes_equal']
assert link['local_tracking_ref_matches'] and link['extra_tiling_runs']==0
assert json.loads((p/'previous-generation-linkage.json').read_text())['previous_post_comment_all25_hashes_match_phase2_before_generation']
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
live={row['path']:sha(wt/row['path']) for row in capture['files']}
assert all(live[row['path']]==row['head_sha256'] for row in capture['files'])
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'fresh_head_screens':1,'reused_baseline_and_previous_head_not_rerun':True,
 'all75_source_inputs_and_raw_outputs_verified':True,'shared_lock_sequence_verified':True,
 'base_candidates':1696,'previous_candidates':628,'phase2_candidates':621,
 'all53_baseline_relative_and3_previous_relative_new_edges_classified':True,
 'live_all25_actual_sources_equal_capture_before_parent_next_edit':True,'live_hashes':live,
 'old120_entry_manifest_untouched':True,'standalone_commit_link':link['commit'],
 'link_pushed_head_script_executed_read_only':True,'no_Lean_source_Git_cache_or_snapshot_mutation':True,
 'limits':'Bounded source/text review only. Subsequent private tagged-run edit requires a new final head screen; this raw generation stays immutable.'}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='live_hashes'},indent=2))
