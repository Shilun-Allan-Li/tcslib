from pathlib import Path
import json,shutil
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());F=json.loads((O/'CANDIDATE-FOOTPRINTS5.json').read_text());G=O/'guards';G.mkdir();roots=[];foot=[];union={}
for f in F:
 target=next((r for r in pin['targets'] if r['name']==f['suffix']),None)
 if target:r=dict(target,final_complete_chunk=str((O/target['new_chunk']).resolve()))
 else:
  idx=85 if f['suffix']=='timedCapture_start' else 86;path=f['source_owner'].replace('.','/')+'.lean';chunk=Path('/private/tmp/ab34-gate122-fh10-e0b-frozen/inputs/final403/root-chunks')/str(idx)/'HEAD.lean.txt';r={'id':idx,'name':f['suffix'],'path':path,'final_complete_chunk':str(chunk)}
 roots.append(r);heads=[v for v in f['foreign_definition_mentions'] if v['ordinary_guard_target']];union.update({r['name']:r for r in heads});foot.append({'id':r['id'],'name':r['name'],'path':r['path'],'root':f['root'],'ordinary_heads':len(heads),'ordinary_head_names':sorted(v['name'] for v in heads)})
 p=G/'source'/(r['path']+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((O/'source/CANDIDATE'/(r['path']+'.txt')).read_bytes())
(G/'PIN.json').write_text(json.dumps({'HEAD':pin['HEAD'],'source_worktree':pin['source_worktree'],'private_candidate':True,'roots':roots},indent=2)+'\n');(G/'FOOTPRINT-SUMMARY.json').write_text(json.dumps({'rows':foot},indent=2)+'\n');(G/'ORDINARY-UNION.json').write_text(json.dumps(list(union.values()),indent=2)+'\n')
for script in ['prepare_guards.py','run_guards.py']:shutil.copyfile(Path('/private/tmp/ab34-first-halt-full-boundary')/script,G/script)
B={r['name']:r for r in json.loads((O/'BASE-DEFINITION-IDENTITIES.json').read_text())};H={r['name']:r for r in json.loads((O/'CANDIDATE-DEFINITION-IDENTITIES.json').read_text())};assert set(B)==set(H) and len(H)==23
for name in B:assert B[name]==H[name],name
old=json.loads(Path('/private/tmp/ab34-gate122-fh10-e0b-frozen/inputs/final403/boundary/ORDINARY-UNION22.json').read_text());names={r['name'] for r in old};assert names<set(H) and set(H)-names=={'Turing.pairEncode'};baseobjects=json.loads(Path('/private/tmp/ab34-gate122-fh10-e0b-frozen/anchors/MAC8/object-hashes.json').read_text());currentobjects=json.loads((O/'OUTPUT895.json').read_text());reuse=[]
for name in sorted(H):
 owner=H[name]['owner'];path=owner.replace('.','/')+'.olean';assert baseobjects[path]==currentobjects[path];reuse.append({'name':name,'owner':owner,'type_Expr_exact_BASE_candidate':True,'value_Expr_exact_BASE_candidate':True,'level_params_exact':True,'whole_owner_olean_hash_equal_BASE_candidate':baseobjects[path],'covered_by_actual_old44':name in names})
(O/'CONTROL-REUSE-IDENTITIES23.json').write_text(json.dumps({'all23_full_type_and_value_Expr_strings_exact':True,'old44_positive_negative_pairs_reusable_for_exact22_heads':True,'new_ordinary_head_needing_controls':['Turing.pairEncode'],'body_identity_rows':reuse,'fresh_current_full_Expr_data':'CANDIDATE-DEFINITION-IDENTITIES.json','fresh_BASE_full_Expr_data':'BASE-DEFINITION-IDENTITIES.json'},indent=2)+'\n');print('Prepared five whole-prefix guards; all23 definition type/value Expr and owner object bytes exact;44 old pairs cover22, pairEncode needs2 new pairs.')
