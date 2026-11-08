from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
C=json.loads((OUT/'capture.json').read_text());D=json.loads((OUT/'pair-delta.json').read_text());B=json.loads((OUT/'base-candidates.json').read_text());H=json.loads((OUT/'head-candidates.json').read_text());old={(r['a'],r['b']):r for r in B};index={x['label']:x for x in json.loads((OUT/'head-index.json').read_text())}
assert len(B)==1454 and len(H)==1455 and D['gone']==[] and D['changed_measurements']==[]
known=('Hierarchy.lean::f6_native_halt','UniversalK.lean::ss_inputRewind_done');assert len(D['new'])==1 and (D['new'][0]['a'],D['new'][0]['b'])==known;assert (D['new'][0]['shared'],D['new'][0]['denominator'],D['new'][0]['printed_percent'])==(162,321,50)
base_api=json.loads((OUT/'merged-API-BASE-dispositions.json').read_text());specific={(x['a'],x['b']):x for x in base_api['all_five_concrete_BASE_rows']};classified=[]
for r in H:
 key=(r['a'],r['b'])
 if key in old:
  assert r==old[key];kind='inherited_exact_fresh_BASE_row';note='Exact retained lexical BASE25 row. Weighted baseline clusters and existing named ruling scopes remain explicit; no blanket acceptance or semantic-copy count.'
  if key in specific:kind=specific[key]['classification'];note=specific[key]['disposition']
 else:
  assert key==known;kind='new_bounded_E3_public_action_equation_idiom';note='The shared step reads public controlAction_apply/moveInputPos_zero. New proof takes controlAction0none as its final halting leaf; old proof establishes an absorbing LIVE done run by induction. New prior liveness directly cites runFrom_state_ne_none_of_le. No copied complete fixed-live contract or new debt acknowledgment is inferred.'
 classified.append(dict(r,a_path=index[r['a']]['path'],b_path=index[r['b']]['path'],classification=kind,disposition=note))
assert sum(x['shared'] for x in H)==D['head']['reproduced_chars']==477688
api_heads=[]
for api in json.loads((OUT/'merged-API-BASE-concrete-pairs.json').read_text()):
 labels=set(api['raw_eligible_labels']);headrows=[r for r in H if r['a'] in labels or r['b'] in labels];assert headrows==[{k:v for k,v in x.items() if k not in ['paths','disposition']} for x in api['BASE_candidate_rows']]
 api_heads.append(dict(name=api['name'],HEAD_rows_equal_actual_BASE_rows=True,rows=len(headrows),F6_new_cross_pairs=0))
(OUT/'raw-all-HEAD-classification.json').write_text(json.dumps(dict(base=C['base'],head=C['head'],population=25,all1455_raw_HEAD_rows=classified,all1454_BASE_rows_exact=True,new_rows=D['new'],gone_rows=[],changed_retained_measurements=[],merged_API_HEAD_pair_checks=api_heads,no_new_F6_pair_against_merged_API=True,no_raw_score_or_denominator_change=True,no_new_debt_acknowledgment=True,limits='Complete directed lexical candidates, not independent semantic proof copies, compiled census, accepted debt census or global absence. Prior23 outputs are historical and not a numeric baseline for this expanded25 population.'),indent=2)+'\n')
freeze=(ROOT/'devtools/seyoon/declfreeze.py').read_text();ns={};exec(compile(freeze.split('a = chunks(open(sys.argv[1]).read())')[0],'<trusted-source-chunks>','exec'),ns);parts=[]
for path,name in [('TCSlib/Complexity/SpaceComplexity/Hierarchy.lean','Complexity.f6_native_halt'),('TCSlib/Complexity/TuringMachine/UniversalK.lean','Turing.ss_inputRewind_done')]:
 src=(OUT/'inputs/head'/(path+'.txt')).read_text();chunk={n:t for n,p,t in ns['chunks'](src)}[name];parts.append(dict(path=path,name=name,line=src[:src.index(chunk)].count('\n')+1,sha256=hashlib.sha256(chunk.encode()).hexdigest(),complete_source_chunk=chunk))
previous=json.loads((ROOT/'campaign/fills/f6/landing/source-screen23-resumed/final23-current/new-E3-comparison.json').read_text())['complete_compared_chunks'];assert [x['complete_source_chunk'] for x in parts]==[x['complete_raw_chunk'] for x in previous]
(OUT/'new-E3-source-comparison.json').write_text(json.dumps(dict(actual_new_row=D['new'][0],full_compared_chunks=parts,exact_bytes_equal_prior_fully_read_comparison=True,disposition='Bounded public stationary-action equation idiom, with None-halt distinct from absorbing LIVE done. FE-LIVE-1 is not extended to None-halt and supplies no future-copy permission.'),indent=2)+'\n')
print(json.dumps(dict(all_HEAD_rows_classified=len(H),BASE_rows_exact=len(B),new_E3_rows=1,gone=0,changed_retained=0,merged_API_new_F6_pairs=0,all_compared_new_row_source_bytes_unchanged=True),indent=2))
