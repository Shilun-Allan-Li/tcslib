"""Classify every raw final candidate after unchanged canonical analysis; never edit scores."""
from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
C=json.loads((OUT/'capture.json').read_text());D=json.loads((OUT/'pair-delta.json').read_text())
B=json.loads((OUT/'base-candidates.json').read_text());H=json.loads((OUT/'head-candidates.json').read_text());old={(x['a'],x['b']):x for x in B}
assert len(B)==647 and sum(x['shared'] for x in B)==172081
assert D['gone']==[] and D['changed_measurements']==[]
known=('Hierarchy.lean::f6_native_halt','UniversalK.lean::ss_inputRewind_done')
assert len(D['new'])==1 and (D['new'][0]['a'],D['new'][0]['b'])==known,D['new']
newrow=D['new'][0];assert (newrow['shared'],newrow['denominator'],newrow['printed_percent'])==(162,321,50)
index={x['label']:x for x in json.loads((OUT/'head-index.json').read_text())}
classified=[]
for x in H:
 key=(x['a'],x['b'])
 if key in old:
  assert x==old[key]
  disposition='Inherited exact raw directed candidate; separately disclosed weighted baseline clusters and ledger scopes. No semantic-copy/debt acceptance inferred.'
  category='inherited_unchanged'
 else:
  assert key==known
  disposition='E3: bounded public stationary-action equation idiom. New proof takes a final halting leaf step; old proof establishes an absorbing LIVE done run. Both consume controlAction_apply/moveInputPos_zero. No exact published complete contract replaces the new leaf proof; no general duplication exemption.'
  category='new_scoped_E3_public_action_idiom'
 classified.append(dict(x,a_path=index[x['a']]['path'],b_path=index[x['b']]['path'],classification=category,disposition=disposition))
assert len(classified)==len(H)==648 and sum(x['shared'] for x in H)==172243
(OUT/'raw-candidate-classification.json').write_text(json.dumps(dict(base=C['base'],head=C['head'],canonical_raw_scores_and_directions_unchanged=True,all_head_rows=classified,inherited_rows=647,new_rows=[dict(newrow,classification='scoped_E3_public_action_idiom')],gone_rows=[],changed_measurements=[],limits='Complete648directed lexical candidates; neither independent semantic-copy count nor accepted debt census. Only the new E3 row receives this bounded semantic disposition. No raw denominator/body extraction/threshold adjustment.'),indent=2)+'\n')
freeze=(ROOT/'devtools/seyoon/declfreeze.py').read_text();ns={};exec(compile(freeze.split('a = chunks(open(sys.argv[1]).read())')[0],'<trusted-chunks>','exec'),ns)
comparisons=[]
for path,name in [('TCSlib/Complexity/SpaceComplexity/Hierarchy.lean','Complexity.f6_native_halt'),('TCSlib/Complexity/TuringMachine/UniversalK.lean','Turing.ss_inputRewind_done')]:
 src=(OUT/'inputs/head'/(path+'.txt')).read_text();chunks={n:t for n,p,t in ns['chunks'](src)};t=chunks[name];comparisons.append(dict(path=path,name=name,line=src[:src.index(t)].count('\n')+1,sha256=hashlib.sha256(t.encode()).hexdigest(),complete_raw_chunk=t))
(OUT/'new-E3-comparison.json').write_text(json.dumps(dict(raw_pair=newrow,complete_compared_chunks=comparisons,disposition='The shared formula is one application of the public controlAction_apply reading with zero input motion. New controlAction0none halts after one leaf step; old controlAction0(some done) has an absorbing live run proved by induction. New prior liveness directly uses runFrom_state_ne_none_of_le. No copied fixed-run host contract or missing exact mechanical re-point was identified. This bounded disposition does not expand an acknowledgment.'),indent=2)+'\n')
print(json.dumps(dict(classified_all_head_rows=len(H),inherited_unchanged=647,new_scoped_E3=1,gone=0,changed_measurements=0,raw_reproduced_chars=172243),indent=2))
