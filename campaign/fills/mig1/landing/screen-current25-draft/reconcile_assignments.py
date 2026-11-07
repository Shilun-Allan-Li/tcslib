"""Bounded mechanical checks of the named T1/T2/T3/T5/T6 families, no elaboration."""
from pathlib import Path
import ast, hashlib, json, re

p = Path(__file__).resolve().parent
tree = ast.parse((p/'copy-text-screen-v3.py.txt').read_text())
ns = {'re':re}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['strip','body']],type_ignores=[]),'<reviewed-v3-source-functions>','exec'),ns)
data = {label:json.loads((p/(label+'-declarations.json')).read_text()) for label in ['base','head']}
tm = 'TCSlib/Complexity/TuringMachine/'
prim,loop,cat,sim = [tm+x+'.lean' for x in ['Build/Primitives','Build/Loop','Build/Catalog','Simulation']]
def decl(label,path,name):
    matches=[r for r in data[label] if r['path']==path and r['name']==name]
    assert len(matches)==1,(label,path,name,len(matches))
    return matches[0]
def code(label,path,name):
    r=decl(label,path,name)
    raw=(p/'inputs'/label/(path+'.txt')).read_text()[r['raw_start']:r['raw_end']]
    return ns['strip'](raw)
norm=lambda s:re.sub(r'\s+','',s)
def body(label,path,name):return ns['body'](code(label,path,name))
def callers(path,helper):
    return [r['name'] for r in data['head'] if r['path']==path and r['name']!=helper and re.search(r'\b'+re.escape(helper)+r'\b',body('head',path,r['name']))]

result={}
names=['lenStart','splitRestore_run','splitBody_rewind','emitterP2_prepare_run']
result['T1']={'catalogRewind_removed':not any(r['path']==prim and r['name']=='catalogRewind' for r in data['head']),
 'callers':[{'name':n,'only_code_token_change_is_callee':norm(code('base',prim,n).replace('catalogRewind','timed_rewind'))==norm(code('head',prim,n))} for n in names],
 'public_timed_rewind_present':any(r['path']==sim and r['name']=='timed_rewind' for r in data['head'])}
twins=[(loop,'emCall_first_entry'),(prim,'emitter_first_entry')]
result['pending_first_entry']={
 'both_unchanged':[{'path':path,'name':n,'unchanged_normalized_code':norm(code('base',path,n))==norm(code('head',path,n)),'head_line':decl('head',path,n)['start_line']} for path,n in twins],
 'same_code_after_own_name_replacement':norm(code('head',loop,twins[0][1]).replace(twins[0][1],'first_entry'))==norm(code('head',prim,twins[1][1]).replace(twins[1][1],'first_entry')),
 'disposition':'Unchanged exact cross-file proof twin; shared API proposal pending, not discharged or acknowledged by this check.'}
families=[
 ('candidate/suffix rewind','emitterP2_prepare_rewind_bank',['emitterP2_prepare_rewind_candidate','emitterP2_prepare_rewind_suffix']),
 ('selected bank frames','emitterP2_bank_frame',['emitterP2_left_frame','emitterP2_right_frame']),
 ('administrative frames','emitterP2_admin_frame',['emitterP2_small_frame','emitterP2_pair_frame']),
 ('embedding proof fields','emitterP2_index_injective',['emitterP2SmallIndex','emitterP2PairIndex']),
 ('left/right erasure','emitterP2_body_erase',['emitterP2_body_erase_left','emitterP2_body_erase_right']),
 ('split-finder orbit','splitOrbit_find',['splitFind_eq','emitterSplit_find']),
 ('T2b buffered replay','bufferReplay_run',['extract_replay','rawStrip_replay'])]
result['T2_T2b']=[]
for family,helper,consumers in families:
    row={'family':family,'shared_private_helper':helper,'helper_private':decl('head',prim,helper)['private'],'helper_kind':decl('head',prim,helper)['declaration_kind'],'consumers':[]}
    for name in consumers:
        before=norm(body('base',prim,name));after=norm(body('head',prim,name))
        row['consumers'].append({'name':name,'base_body_chars':len(before),'head_body_chars':len(after),'helper_occurrences':len(re.findall(r'\b'+helper+r'\b',body('head',prim,name)))})
    result['T2_T2b'].append(row)
result['T3']=[]
for name in ['emCall_bank_initial','emCall_bank_final']:
    result['T3'].append({'name':name,'base_repeated_sideproof_marker':len(re.findall(r"by rintro ⟨r', hr⟩",code('base',loop,name))),
        'head_repeated_sideproof_marker':len(re.findall(r"by rintro ⟨r', hr⟩",code('head',loop,name))),
        'pair_not_mem_uses':len(re.findall(r'\bemCall_pair_not_mem\b',body('head',loop,name))),
        'triple_not_mem_uses':len(re.findall(r'\bemCall_triple_not_mem\b',body('head',loop,name)))})
result['T5']={'proof_sharing':{n:callers(cat,n) for n in ['catalog_buffer_clip','catalog_increment_framed']},'frozen_tables':[]}
for name in ['copyMapTM','transferMapTM','clearTM']:
    old,new=body('base',cat,name),body('head',cat,name)
    result['T5']['frozen_tables'].append({'name':name,'kind':decl('head',cat,name)['declaration_kind'],
        'normalized_body_unchanged':norm(old)==norm(new),'base_normalized_body_sha256':hashlib.sha256(norm(old).encode()).hexdigest(),'head_normalized_body_sha256':hashlib.sha256(norm(new).encode()).hexdigest()})
result['T5']['disposition']='Distinct frozen executable table data retained. Copy rewind preserves source; transfer rewind writes rest b to source. No table-rewrite exception or new debt approval is inferred.'
result['T6']={'shared_private_helper':'pairExtract_space_row','callers':callers(cat,'pairExtract_space_row')}
(p/'assignment-reconciliation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
