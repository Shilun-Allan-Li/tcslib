"""Bounded source classification of every final new directed edge, with all tagged-instance scores retained."""
from pathlib import Path
import ast, difflib, json
p=Path(__file__).resolve().parent;old=p.parent/'screen-current25-phase2'
prior={(r['target'],r['source']):r for r in json.loads((old/'vs-base-classifications.json').read_text())}
tagged={'Primitives.lean::fwdMapVirtual_run','VirtualInput.lean::vhostEmitTM_runFrom','Simulation.lean::bufferedSecondCfg_run'}
tag_description=('All three drivers now consume the published Set.MapsTo.iterate/add_right_iterate invariant route and contain no induction. '
 'The remaining material matches are concrete local P declarations, initial-tag membership and one-step tag/equality witnesses supplied to that generic iterator. '
 'They use distinct configuration encoders and published step contracts. The final private-body repoint raises literal instance-template overlap; the full429/426-character scores are retained. '
 'This is generic-proof reuse with residual instance-premise text, not a claim of zero duplication, a new host/API or a human debt waiver; adequacy remains visible for the external gate.')
def classify(row):
 key=(row['target'],row['source'])
 if set(key)<=tagged:
  return dict(row,group='F01',group_title='Three generic tagged-invariant instances; material premise template retained',disposition=tag_description,
              classification_origin='Final source reading and exact-three-driver QA')
 assert key in prior,('unclassified final family',key)
 before=prior[key]
 return dict(row,group=before['group'],group_title=before['group_title'],disposition=before['disposition'],
             classification_origin='Prior phase2 source-read family; both endpoint bodies unchanged',previous_id=before['id'])
results={}
for label,count in [('vs-base',54),('vs-phase2',2)]:
 rows=json.loads((p/(label+'-new-all.json')).read_text());assert len(rows)==count
 result=[classify(r) for r in rows];assert len({(r['target'],r['source']) for r in result})==count
 results[label]=result
 (p/(label+'-classifications.json')).write_text(json.dumps(result,indent=2)+'\n')
groups={}
for row in results['vs-base']:
 key=row['group']
 if key not in groups:groups[key]={'group':key,'title':row['group_title'],'disposition':row['disposition'],'baseline_ids':[],'phase2_ids':[],'cross_file':0}
 groups[key]['baseline_ids'].append(row['id']);groups[key]['cross_file']+=row['cross_file']
for row in results['vs-phase2']:groups[row['group']]['phase2_ids'].append(row['id'])
(p/'classification-groups.json').write_text(json.dumps(list(groups.values()),indent=2)+'\n')
head=json.loads((p/'head-all-candidates.json').read_text())
tag_rows=[r for r in head if {r['target'],r['source']}<=tagged]
assert len(tag_rows)==6
(p/'all-six-tagged-instance-candidates.json').write_text(json.dumps(tag_rows,indent=2)+'\n')
lines=['# Final bounded copy-screen source classification','',
 'All 54 edges new against baseline and both edges new against phase2 are assigned exactly once.',
 'All six directed matches among the three tagged drivers are retained separately, including existing pairs.',
 'This is a bounded source/text review, not debt/API/gate approval.','',
 '| Group | Baseline IDs | Phase2 IDs | Source classification |','| --- | --- | --- | --- |']
for row in groups.values():
 lines.append('| '+row['group']+' — '+row['title']+' | '+', '.join(row['baseline_ids'])+' | '+', '.join(row['phase2_ids'])+' | '+row['disposition']+' |')
(p/'semantic-review.md').write_text('\n'.join(lines)+'\n')

idx={label:json.loads((p/(label+'-screen-index.json')).read_text()) for label in ['previous-head','head']}
assert idx['previous-head'].keys()==idx['head'].keys()
changed=[key for key in idx['head'] if idx['head'][key]['body_sha256']!=idx['previous-head'][key]['body_sha256']]
assert changed==['Primitives.lean::fwdMapVirtual_run']
ns={};tree=ast.parse((p/'copy-text-screen-v3.py.txt').read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['strip','body']],type_ignores=[]),'<reviewed-source-body>','exec'),ns)
def body(label,key):
 r=idx[label][key];raw=(p/'inputs'/label/(r['path']+'.txt')).read_text()[r['raw_start']:r['raw_end']]
 return ns['body'](ns['strip'](raw))
key=changed[0]
diff=''.join(difflib.unified_diff(body('previous-head',key).splitlines(True),body('head',key).splitlines(True),fromfile='phase2 private tagged induction',tofile='final generic invariant instance'))
(p/'private-tagged-body-change.diff.txt').write_text(diff)
print(json.dumps({'classified_vs_base':54,'classified_vs_phase2':2,'groups':len(groups),
 'six_tagged_directed_scores_retained':True,'only_changed_normalized_body':changed},indent=2))
