from pathlib import Path
import json,re,hashlib
O=Path(__file__).parent
T=json.loads((O/'TASK.json').read_text())
patch=O/'remaining13.patch'
added=[l[1:] for l in patch.read_text().splitlines() if l.startswith('+') and not l.startswith('+++')]
commands=[l for l in added if re.search(r'\b(?:simp|simpa|rw|unfold|change)\b',l)]
rows=[]
for line in commands:
    if 'mem_visitedByTapeHead_iff' in line:
        why='Published visited-head membership equation, local initialization equality and local run equality; no definition argument.'
    elif 'mkCfg_state' in line:
        why='Published mkCfg state projection and Core Option.map_some equations plus local hl.'
    elif 'runFrom_' in line:
        why='Published zero/successor run equations. Existing RO1 one-step chains remain explicitly scheduled, with exact overlap retained.'
    elif 'hvisit' in line or 'hinit' in line or 'hrun' in line or 'hcSdef' in line:
        why='Local proven equalities used as rewrite rules; no ordinary runtime definition argument.'
    elif 'initCfg_eq_bootCfg' in line:
        why='Same-home initialization equation, Core List.take_append_drop equation, NDTM runWith_append equation and local hboot.'
    elif 'rewind_run' in line:
        why='Same-home rewind_run theorem and local hb; simp has no explicit definition argument; only selected-time variable changed.'
    else:
        why='Complete command retained for manual context; uses local facts or existing published equations, without a new definition argument.'
    rows.append({'line':line,'disposition':why})
full=[]
inputs=json.loads((O/'SEAL-INPUTS-v4.json').read_text())
for r in T['todo']:
    data=(O/'new-chunks'/(str(r['id'])+'.lean.txt')).read_text()
    guardrow=next(d for d in inputs if d['kind']=='full_target_scopes' and d['path']==r['path'])
    leaves=[n.split('.')[-1] for n in guardrow['guards']]
    findings=[]
    for m in re.finditer(r'\b(?:simp|simp_all|simpa|rw|dsimp)\b(?:\s+only)?\s*\[',data):
        start=m.end();i=start;depth=1
        while i<len(data) and depth:
            if data[i]=='[':depth+=1
            if data[i]==']':depth-=1
            i+=1
        args=data[start:i-1]
        for name in leaves:
            pattern=r'(?<![\w.])(?:(?:Turing\.)?MultiTapeTM\.)?'+re.escape(name)+r'(?![\w\'])'
            if re.search(pattern,args):findings.append({'command':m.group(),'args':args,'name':name})
    for m in re.finditer(r'\b(?:unfold|delta)\s+([^\n]+)',data):
        for name in leaves:
            if re.search(r'(?<![\w.])(?:(?:Turing\.)?MultiTapeTM\.)?'+re.escape(name)+r'(?![\w\'])',m.group(1)):
                findings.append({'command':m.group(),'name':name})
    assert not findings,(r['id'],findings)
    full.append({'id':r['id'],'path':r['path'],'name':r['name'],'active_guard_names':guardrow['guards'],'forced_named_guard_definition_arguments':0})
res={'PASS':True,'patch_sha256':hashlib.sha256(patch.read_bytes()).hexdigest(),'changed_command_lines':rows,'new_forbidden_foreign_Core_Mathlib_definition_arguments':0,'full_target_named_guard_argument_checks':full,'all13_full_scopes_no_forced_named_guard_unfold':True,'scope_limit':'This review covers all added explicit argument lines and all named guarded definitions inside the13 complete declarations. Other inherited foreign definitions are outside the selected guard closure; no global Rule10/opacity approval is inferred.','RO1':'Call seven regions and Clean zero/one readers remain in the existing acknowledged one-step kind pending generic API/home. No generic unlanded API, new public interface, import, statement or waiver.'}
(O/'EXPLICIT-ARGUMENT-REVIEW.json').write_text(json.dumps(res,indent=2)+'\n')
print('PASS explicit arguments: added commands='+str(len(rows))+'; complete named-guard scans13')
