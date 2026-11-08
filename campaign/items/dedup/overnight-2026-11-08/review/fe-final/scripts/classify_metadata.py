from pathlib import Path
import json,collections
E=Path('/private/tmp/ab34-fe-live1-final-validation/evidence');M=E/'metadata';a=json.loads((M/'BASE.json').read_text());b=json.loads((M/'HEAD.json').read_text());A={r['name']:r for r in a};B={r['name']:r for r in b};removed=json.loads((M/'REMOVED.json').read_text());changed=json.loads((M/'CHANGED.json').read_text());added=json.loads((M/'ADDED.json').read_text());assert not added
std={'propext','Classical.choice','Quot.sound'};assert all(set(r['axioms'])<=std for r in a+b)
rows=[]
for x in removed:
 assert '._proof_' in x['name'] and x['kind']=='theorem'
 leaf=x['name'].split('.')[-1];source=(E/'source/BASE'/(x['owner'].replace('.','/')+'.lean.txt')).read_text();assert leaf not in source
 rows.append({'operation':'removed','name':x['name'],'classification':'compiler-generated proof auxiliary removed by proof refactoring','authored_API_change':False,'BASE':x,'HEAD':None})
for x in changed:
 assert '._proof_' in x['name'] and x['BASE']['kind']==x['HEAD']['kind']=='theorem'
 assert set(x['differences'])<={'typeExpr','axioms'}
 leaf=x['name'].split('.')[-1]
 for label in ['BASE','HEAD']:assert leaf not in (E/'source'/label/(x[label]['owner'].replace('.','/')+'.lean.txt')).read_text()
 rows.append({'operation':'changed','name':x['name'],'classification':'compiler-generated proof auxiliary reused/renumbered after changed tactic block; exact types and AX retained separately','authored_API_change':False,'difference_fields':list(x['differences']),'BASE':x['BASE'],'HEAD':x['HEAD']})
keys=['owner','kind','private','internal','levelParams','typeExpr','valuePresent','unsafe','partial','kernelHints','reducibility','simp','unfold','protected','instancePriority','axioms']
AA={n:r for n,r in A.items() if '._proof_' not in n};BB={n:r for n,r in B.items() if '._proof_' not in n};assert set(AA)==set(BB)
for n in AA:assert all(AA[n][k]==BB[n][k] for k in keys),n
publicA={n:r for n,r in AA.items() if not r['private']};publicB={n:r for n,r in BB.items() if not r['private']};assert set(publicA)==set(publicB)
res={'PASS':True,'complete_raw_delta_rows':len(rows),'removed':len(removed),'added':len(added),'changed_shared':len(changed),'all_deltas_compiler_generated_proof_auxiliaries':True,'BASE_raw':len(a),'HEAD_raw':len(b),'BASE_generated_proof_auxiliaries':len(A)-len(AA),'HEAD_generated_proof_auxiliaries':len(B)-len(BB),'remaining_owned_constants':len(AA),'remaining_owned_names_types_levels_metadata_AX_exact':True,'remaining_nonprivate_constants':len(publicA),'remaining_nonprivate_names_types_levels_metadata_AX_exact':True,'raw_nonprivate_BASE':sum(not r['private'] for r in a),'raw_nonprivate_HEAD':sum(not r['private'] for r in b),'raw_public_decrease_explanation':'One generated exists_inputLengthTM._proof_1_16 disappears; its raw nonprivate generated cohort decreases78→77. No authored declaration header or public contract changes.','all_owned_axioms_standard_only':True,'axiom_standard_set':sorted(std),'target11_exact_type_and_AX':'TARGET11.json','proof_values_not_rendered':True,'rows':rows};(M/'DISPOSITIONS.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k!='rows'},indent=2))
