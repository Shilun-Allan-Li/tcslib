from pathlib import Path
import json,hashlib
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());runs=json.loads((O/'COLLECTOR-RUNS.json').read_text());assert len(runs)==14 and all(r['exit']==0 and r['errors']==0 for r in runs)
rows=[]
for p in sorted((O/'collector-runs').glob('*-footprints.json')):rows+=json.loads(p.read_text())
assert len(rows)==17;union={};summaries=[]
for row in rows:
 original=next(r for r in pin['roots'] if r['name']==row['suffix'] and r['path'][:-5].replace('/','.')==row['source_owner']);ordinary=[r for r in row['foreign_definition_mentions'] if r['ordinary_guard_target']];excluded=[r for r in row['foreign_definition_mentions'] if not r['ordinary_guard_target']]
 for head in ordinary:union[head['name']]=head
 summaries.append({'id':original['id'],'name':original['name'],'path':original['path'],'root':row['root'],'ordinary_heads':len(ordinary),'ordinary_head_names':[r['name'] for r in ordinary],'excluded_abbrev_or_projection_heads':len(excluded),'excluded_mentions':excluded,'local_ordinary_helpers':len(row['local_definition_helpers']),'local_helper_names':[r['name'] for r in row['local_definition_helpers']],'selected_type_Expr':row['root_type_Expr'],'selected_type_pretty':row['root_type_pretty'],'selected_axioms':row['root_axioms'],'footprint_source_owner':row['source_owner'],'actual_main_module':row['actual_main_module']})
assert all(set(r['selected_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in summaries)
res={'HEAD':pin['HEAD'],'roots':17,'source_owners':14,'actual_current_source_collectors':14,'errors':0,'declaration_sorry_warnings':sum(r['declaration_sorry_warnings'] for r in runs),'ordinary_union':len(union),'ordinary_union_heads':sorted(union),'policy':'Exact root type and proof value mentions; all mentioned constant TYPES; same-owner ordinary definition helper TYPES and VALUES. Imported theorem proof values and foreign definition values are not traversed. Foreign ordinary heads exclude kernel abbrevs and projections, retained separately.','proof_values_rendered':False,'selected_types_and_axioms_actual':True,'selected_axioms_standard_only':True,'rows':sorted(summaries,key=lambda r:r['id'])}
(O/'FOOTPRINTS17.json').write_text(json.dumps(rows,indent=2)+'\n');(O/'FOOTPRINT-SUMMARY.json').write_text(json.dumps(res,indent=2)+'\n');(O/'ORDINARY-UNION.json').write_text(json.dumps([union[n] for n in sorted(union)],indent=2)+'\n');print('17 source roots/14 native collectors; ordinary union='+str(len(union)))
for r in res['rows']:print(r['id'],r['name'],'ordinary',r['ordinary_heads'],'local_helpers',r['local_ordinary_helpers'])
print('Registered definition simplifiers',[(r['name'],r['simp'],r['unfold']) for r in union.values() if r['simp'] or r['unfold']])
