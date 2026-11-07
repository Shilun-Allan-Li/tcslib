"""Verify the exact retained draft screen artifacts, without tiling or Lean."""
from pathlib import Path
import collections, hashlib, json, re

p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
capture=json.loads((p/'capture.json').read_text())
assert capture['count']==25 and capture['base_commit_and_all_blob_objects_verified']
assert capture['current_sources_stable_during_capture']
trees=json.loads((p/'trees.json').read_text())
for row in capture['files']:
 for label in ['base','head']:
  q=p/'inputs'/label/(row['path']+'.txt')
  assert sha(q)==row[label+'_sha256']
  assert sha(Path(trees['temporary_root'])/label/row['path'])==row[label+'_sha256']
assert len(list((p/'inputs').rglob('*.lean.txt')))==50
script_sha=sha(p/'copy-text-screen-v3.py.txt')
for label in ['base','head']:
 r=json.loads((p/(label+'.json')).read_text())
 assert r['exit']==0 and r['source_count']==25
 assert r['screen_sha256']==script_sha and r['output_sha256']==sha(p/(label+'.out'))
 assert r['command'][:3]==['nice','-n','10'] and '-I' in r['command']
r=json.loads((p/'pairdiff.json').read_text())
assert r['exit']==0 and r['pairdiff_sha256']==sha(p/'pairdiff.py.txt')
assert r['output_sha256']==sha(p/'pairdiff.out')
text=(p/'pairdiff.out').read_text()
assert text.splitlines()[0]=='head pairs 628; union of earlier 1696; new at head 60; earlier-only 1128'
assert len(re.findall(r'^  NEW ',text,re.M))==60
assert len(re.findall(r'^  GONE ',text,re.M))==1128
events=[json.loads(line) for line in (p/'lock-events.jsonl').read_text().splitlines()]
assert [(r['action'],r['label']) for r in events]==[
 ('acquired','base'),('released','base'),('acquired','head'),('released','head')]
assert len({r['pid'] for r in events})==1
rows=json.loads((p/'new-candidate-classifications.json').read_text())
assert len(rows)==len({r['id'] for r in rows})==60
assert collections.Counter(r['kind']+'/'+('cross' if r['cross_file'] else 'in') for r in rows)=={
 'proof/cross':13,'term/cross':4,'proof/in':42,'term/in':1}
assert len(json.loads((p/'classification-groups.json').read_text()))==16
assert len(json.loads((p/'existing-changed-metrics.json').read_text()))==27
link=json.loads((p/'comment-linkage/equivalence.json').read_text())
assert link['all_comparisons_equal'] and link['source_count']==25 and link['tiling_runs_added']==0
assert link['all_extracted_declarations']==1602 and link['screened_declarations']==1232
assert link['trusted_parser_sha256']==script_sha
assert link['comment_adoption_receipt_sha256']==sha(p/'comment-linkage/comment-cleanup-adoption.json')
for row in link['files']:
 assert sha(p/'comment-linkage/final-actual'/(row['path']+'.txt'))==row['final_actual_sha256']
assert not list(p.rglob('*.lean'))
result={'screens_executed':2,'screen_exits':[0,0],'population_each':25,
        'all_50_original_inputs_and_both_temporary_trees_hash_verified':True,
        'all_raw_output_and_tool_source_hashes_verified':True,
        'serial_shared_lock_acquire_release_verified':True,'stale_reclamations':0,
        'directed_candidates_base':1696,'directed_candidates_head':628,
        'new_directed_candidates':60,'gone_directed_candidates':1128,
        'new_cross_file':17,'new_in_file':43,'all_new_classified_exactly_once':True,
        'existing_changed_metrics_retained':27,
        'post_comment_equivalence_at_recorded_generation_verified':True,
        'no_extra_tiling_for_comment_linkage':True,
        'limitations':'Draft pre-comment raw snapshot plus recorded post-comment equivalent generation only. Later proof edits need a refreshed head screen; no gate/debt/API/replay clearance.'}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
