"""Classify every new phase2 directed edge against both earlier full screens."""
from pathlib import Path
import ast, collections, difflib, json, re
p=Path(__file__).resolve().parent;old=p.parent/'screen-current25-draft'
prior={(r['target'],r['source']):r for r in json.loads((old/'new-candidate-classifications.json').read_text())}
updates={
 'G01':('Factored terminal suffix; remaining mode-specific reader/call packaging',
        'Both current proofs call loop_computes_of_startup once; the old runFrom_add/computation/time-arithmetic suffix is gone. The surviving478-char overlap comprises the common contract arguments, different halted/find summation-reader instantiations and the common helper invocation. It is disclosed as residual call packaging, not called zero textual duplication.'),
 'G04':('Retained moved parser phase/frame relationships',
        'These surviving parser phases have the same deleted Catalog a2_map origins. The substantial backA/backB mirrored induction is now in fwdMap_back, and its two directed old matches are gone. Remaining matches concern distinct suffix/block/emit/setup/frame glue; block already calls first. No general legacy-debt clearance is inferred.'),
 'G08':('Factored canonical field packaging; distinct tape-cell cases remain',
        'Both endpoint proofs now call catalog_ofWords_with_tapes once. Cfg.ext and the four non-tape fields are proved only in that helper; the distinct tape-cell cases still invoke catalog_buffer_clip. The surviving285-char match is tape-reader/update/clip glue, not an unchanged copy of the former full configuration proof.'),
 'G15':('Generic invariant-route instances versus unchanged private tagged run',
        'The two public run readers now use Set.MapsTo.iterate/add_right_iterate with concrete initial/step premises; neither contains induction. Their169-char overlaps with private fwdMapVirtual_run are concrete tag/step-witness and run-successor rewriting premises. The private lemma is unchanged and is not claimed converted by the two-public-consumer patch. The old private-to-public directed matches are gone; reverse matches persist. No broad debt exemption is inferred.')}
new_specific={
 ('Loop.lean::emCall_bank_step','Loop.lean::emCall_bank_initial'):
  ('H01','Client bank-step statement/instantiation versus shortened initial wrapper',
   'bank_step is unchanged and already invokes bank_initial and bank_final. v3 starts bank_initial at let frame := in its TYPE;450 extracted characters include its long specialized configuration equation, while its actual proof only specializes bank_embed. The336-character match is existing statement/client-call material exposed by source shortening, not a copied bank reconstruction proof.'),
 ('Loop.lean::emCall_bank_embed','Loop.lean::emCall_bank_initial'):
  ('H02','Shared bank helper versus its specialization type/call',
   'The294/450 match includes the unchanged let-frame type of bank_initial and the helper contract it specializes. Initial has one bank_embed call; the selected/unselected field proof occurs once in the helper. This is expected provider/consumer statement and call text, not two bank proofs.'),
 ('Loop.lean::loopHost_contracts','Loop.lean::emitLoopTM_computes'):
  ('H03','Retained fuel/orbit/round-assembly scaffold, newly threshold-visible',
   'loopHost_contracts is byte-equivalent in noncomment code to the previous generation. emitLoopTM_computes changes only its terminal/computation suffix to a helper call; the earlier shared fuel/orbit/round assembly is unchanged. Its shorter2057-character denominator now exposes1166 shared characters. Both consume existing prepare, debit/width and mode-specific round contracts; capture/find and forwarding outputs differ. This is a real retained scaffold watch, not new copy introduced by phase2 and not an inferred debt approval.')}

def classify(row):
 key=(row['target'],row['source'])
 if key in new_specific:
  group,title,disposition=new_specific[key]
  return dict(row,group=group,group_title=title,disposition=disposition,classification_origin='fresh phase2 source reading')
 assert key in prior,('unclassified new edge',key)
 previous=prior[key];group=previous['group']
 title,disposition=updates.get(group,(previous['group_title'],previous['disposition']))
 return dict(row,group=group,group_title=title,disposition=disposition,
             previous_classification_id=previous['id'],classification_origin='prior source-read family, refreshed where phase2 changed its endpoints')

classified={}
for label,expected in [('vs-base',53),('vs-previous-head',3)]:
 rows=json.loads((p/(label+'-new-all.json')).read_text());assert len(rows)==expected
 result=[classify(r) for r in rows]
 assert len({(r['target'],r['source']) for r in result})==expected
 classified[label]=result
 (p/(label+'-classifications.json')).write_text(json.dumps(result,indent=2)+'\n')
groups={}
for row in classified['vs-base']:
 key=row['group']
 if key not in groups:groups[key]={'group':key,'title':row['group_title'],'disposition':row['disposition'],'baseline_ids':[],'previous_ids':[],'cross_file':0}
 groups[key]['baseline_ids'].append(row['id']);groups[key]['cross_file']+=row['cross_file']
for row in classified['vs-previous-head']:groups[row['group']]['previous_ids'].append(row['id'])
(p/'classification-groups.json').write_text(json.dumps(list(groups.values()),indent=2)+'\n')
lines=['# Phase2 bounded source classification','',
 'All53 new baseline-relative edges and all3 new previous-head-relative edges are assigned once.',
 'Full scores, source positions and endpoint names are retained in the two classification JSON files.',
 'Prior source-read classifications are explicitly linked and refreshed where phase2 changed the proof.',
 'No debt/API/gate approval is inferred.','',
 '| Group | Baseline IDs | Previous-head IDs | Source classification |', '| --- | --- | --- | --- |']
for group in groups.values():
 lines.append('| '+group['group']+' — '+group['title']+' | '+', '.join(group['baseline_ids'])+' | '+', '.join(group['previous_ids'])+' | '+group['disposition']+' |')
(p/'semantic-review.md').write_text('\n'.join(lines)+'\n')

# Retain the exact noncomment proof change explaining H03, without rerunning matching.
ns={};tree=ast.parse((p/'copy-text-screen-v3.py.txt').read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['strip','body']],type_ignores=[]),'<reviewed-source-body>','exec'),ns)
idx={label:json.loads((p/(label+'-screen-index.json')).read_text()) for label in ['previous-head','head']}
def text(label,key):
 row=idx[label][key];raw=(p/'inputs'/label/(row['path']+'.txt')).read_text()[row['raw_start']:row['raw_end']]
 return ns['strip'](raw)
host='Loop.lean::loopHost_contracts';emit='Loop.lean::emitLoopTM_computes'
assert text('previous-head',host)==text('head',host)
assert text('previous-head','Loop.lean::emCall_bank_step')==text('head','Loop.lean::emCall_bank_step')
diff=''.join(difflib.unified_diff(ns['body'](text('previous-head',emit)).splitlines(True),ns['body'](text('head',emit)).splitlines(True),fromfile='previous noncomment emitting proof',tofile='phase2 noncomment emitting proof'))
(p/'emitting-suffix-change.diff.txt').write_text(diff)
(p/'three-new-edge-source-checks.json').write_text(json.dumps({'bank_step_noncomment_code_unchanged':True,
 'loopHost_contracts_noncomment_code_unchanged':True,'emitting_change_diff':'emitting-suffix-change.diff.txt',
 'H01_H02_include_let_frame_type_tail':True,'no_additional_tiling':True},indent=2)+'\n')
print(json.dumps({'classified_vs_base':53,'classified_vs_previous':3,'groups':len(groups),
                  'new_cross_file_family_vs_previous':0,'all_new_edges_assigned_once':True},indent=2))
