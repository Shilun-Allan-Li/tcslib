"""Source-only verification of the adopted factoring targets; no elaboration or tiling."""
from pathlib import Path
import ast, hashlib, json, re
p=Path(__file__).resolve().parent
ns={};tree=ast.parse((p/'copy-text-screen-v3.py.txt').read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='strip'],type_ignores=[]),'<reviewed-v3-strip>','exec'),ns)
rows={label:json.loads((p/(label+'-declarations.json')).read_text()) for label in ['previous-head','head']}
prefix='TCSlib/Complexity/TuringMachine/'
files={k:prefix+v+'.lean' for k,v in {'loop':'Build/Loop','prim':'Build/Primitives','cat':'Build/Catalog','sim':'Simulation','virtual':'Build/VirtualInput'}.items()}
def find(label,file,name):
 found=[r for r in rows[label] if r['path']==file and r['name']==name];assert len(found)==1,(label,file,name)
 return found[0]
def code(label,file,name):
 r=find(label,file,name);raw=(p/'inputs'/label/(file+'.txt')).read_text()[r['raw_start']:r['raw_end']]
 return ns['strip'](raw)
norm=lambda s:re.sub(r'\s+','',s)
families=[]
for label,file,helper,consumers in [
 ('terminal',files['loop'],'loop_computes_of_startup',['loopHostTM_decides','loopHostTM_finds','emitLoopTM_computes']),
 ('bank frame',files['loop'],'emCall_bank_embed',['emCall_bank_initial','emCall_bank_final']),
 ('work-buffer rewind',files['prim'],'fwdMap_back',['fwdMap_backA','fwdMap_backB']),
 ('canonical endpoint',files['cat'],'catalog_ofWords_with_tapes',['Cfg.ofWords_transfer_endpoint','Cfg.ofWords_copy_endpoint'])]:
 h=find('head',file,helper);assert h['private'] and h['declaration_kind'] in ['theorem','lemma']
 calls=[]
 for name in consumers:
  text=code('head',file,name);count=len(re.findall(r'\b'+re.escape(helper)+r'\b',text))
  assert count==1
  calls.append({'name':name,'line':find('head',file,name)['start_line'],'helper_calls':count})
 families.append({'family':label,'private_proof_helper':helper,'consumers':calls})
retired=['emCall_pair_not_mem','emCall_triple_not_mem']
assert not any(r['path']==files['loop'] and r['name'] in retired for r in rows['head'])
for name in retired:assert not re.search(r'\b'+name+r'\b',(p/'inputs/head'/(files['loop']+'.txt')).read_text())
tagged=[]
for file,name in [(files['sim'],'bufferedSecondCfg_run'),(files['virtual'],'vhostEmitTM_runFrom')]:
 text=code('head',file,name)
 assert 'Set.MapsTo' in text and 'preserve.iterate t initial' in text and 'add_right_iterate' in text
 assert not re.search(r'\binduction\b',text)
 tagged.append({'path':file,'name':name,'uses_Set_MapsTo_iterate':True,'uses_add_right_iterate':True,'contains_induction':False})
private_virtual=code('head',files['prim'],'fwdMapVirtual_run')
private_virtual_unchanged=norm(private_virtual)==norm(code('previous-head',files['prim'],'fwdMapVirtual_run'))
assert private_virtual_unchanged
pending=[]
for file,name in [(files['loop'],'emCall_first_entry'),(files['prim'],'emitter_first_entry'),
                  (files['cat'],'computesFunInTime_pairDup_spaceUsed'),(files['cat'],'computesFunInTime_incFixed_spaceUsed'),
                  (files['cat'],'redirectTM_spaceUsedByTape')]:
 assert norm(code('head',file,name))==norm(code('previous-head',file,name))
 pending.append({'path':file,'name':name,'normalized_noncomment_code_unchanged':True})
source_hashes={r['path']:hashlib.sha256((p/'inputs/head'/(r['path']+'.txt')).read_bytes()).hexdigest() for r in json.loads((p/'capture.json').read_text())['files']}
result={'source_only_not_Lean_or_screen':True,'factoring_families':families,'unused_selector_helpers_retired':retired,
 'two_adopted_public_tagged_run_bodies':tagged,
 'private_fwdMapVirtual_run':'Unchanged small tagged induction; not claimed converted by the two-public-consumer patch.',
 'private_fwdMapVirtual_run_unchanged':private_virtual_unchanged,
 'unchanged_pending_families':pending,'source_hashes':source_hashes}
(p/'targeted-reuse.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='source_hashes'},indent=2))
