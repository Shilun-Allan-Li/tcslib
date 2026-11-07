"""Reconcile the refreshed gate116 receipts, without running further checks."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re
import subprocess

H=Path(__file__).resolve().parent
R=H.parents[4]

def census(label,all_constants=False):
    name=('AllConstants' if all_constants else 'Census')+'-'+label
    pattern=r'CONSTANT (\S+) module=(\S+) kind=(\S+) internal=(true|false)'
    if all_constants:pattern+=r' private=(true|false)'
    out={}
    for line in (H/(name+'.out')).read_text().splitlines():
        m=re.fullmatch(pattern,line);assert m,line
        values=m.groups();n,mod,kind,internal=values[:4]
        row={'module':mod,'kind':kind,'internal':internal=='true'}
        if all_constants:row['private']=values[4]=='true'
        assert n not in out;out[n]=row
    return out

def delta(a,b):
    return {'base_count':len(a),'head_count':len(b),
        'added':{n:b[n] for n in sorted(b.keys()-a.keys())},
        'removed':{n:a[n] for n in sorted(a.keys()-b.keys())},
        'kind_or_module_owner_changed':{n:[a[n],b[n]] for n in sorted(a.keys()&b.keys()) if a[n]!=b[n]}}

def main():
    pins=json.loads((H/'source-receipt.json').read_text())
    for key in ['base','head']:
        value=subprocess.check_output(['git','-C',str(R),'rev-parse',pins[key]],text=True).strip()
        subprocess.run(['git','-C',str(R),'cat-file','-e',value+'^{commit}'],check=True)
        assert value==pins[key]
    pub=delta(census('base'),census('head'))
    all_a,all_b=census('base',True),census('head',True)
    full=delta(all_a,all_b)
    full['base_private']=sum(x['private'] for x in all_a.values())
    full['head_private']=sum(x['private'] for x in all_b.values())
    for d in [pub,full]:
        assert list(d['added'])==['Complexity.SPACE_linear_ne_NP._proof_1_1']
        assert not d['removed'] and not d['kind_or_module_owner_changed']
    assert [pub['base_count'],pub['head_count']]==[4,5]
    assert [full['base_count'],full['head_count'],full['base_private'],full['head_private']]==[137,138,133,133]
    (H/'constant-delta.json').write_text(json.dumps(pub,indent=2)+'\n')
    (H/'all-constant-delta.json').write_text(json.dumps(full,indent=2)+'\n')
    expected=[i for i,line in enumerate((H/'Controls-sealed.lean.txt').read_text().splitlines(),1) if ':= by rfl' in line]
    actual=[int(n) for n in re.findall(r'Controls-sealed\.lean:(\d+):\d+: error(?:\(|:)',(H/'Controls-sealed.out').read_text())]
    assert len(expected)==8 and Counter(expected)==Counter(actual)
    controls={'expected_error_lines':expected,'actual_error_lines':actual,
        'multiplicities_match':True,'positive_exit':0,'negative_exit':1,
        'pointwise_controls':4,'parameter_abstracted_controls':4,'unexpected_errors':0}
    (H/'control-check.json').write_text(json.dumps(controls,indent=2)+'\n')
    P=re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%')
    pairs={}
    for label in ['base','head']:
        rows={}
        for line in (H/f'screen-{label}.txt').read_text().splitlines():
            m=P.match(line)
            if m:rows[m.group(1),m.group(2)]=list(map(int,m.groups()[2:]))
        pairs[label]=rows
        run=json.loads((H/f'screen-{label}-run.json').read_text())
        assert run['exit']==0 and run['output_sha256']==hashlib.sha256((H/f'screen-{label}.txt').read_bytes()).hexdigest()
    assert len(pairs['head'])==31 and pairs['base']==pairs['head']
    previous={}
    for line in (H.parent/'screen/screen-base.txt').read_text().splitlines():
        m=P.match(line)
        if m:previous[m.group(1),m.group(2)]=list(map(int,m.groups()[2:]))
    assert pairs['base']==previous
    inventory=(H/'Inventory.out').read_text()
    assert inventory.count('TARGET ')==2 and 'sorryAx' not in inventory
    assert 'AXIOMS [propext, Classical.choice, Quot.sound]' in inventory
    assert 'AXIOMS [propext, Quot.sound]' in inventory
    runs=['Census-base','Census-head','AllConstants-base','AllConstants-head','Inventory','SimpDefs','Hierarchy-sealed','Controls-unsealed','Controls-sealed']
    for n in runs:
        run=json.loads((H/(n+'-run.json')).read_text())
        assert run['exit']==run['expected_exit'] and run['errors']==run['expected_errors']
    result={'base':pins['base'],'head':pins['head'],'head_source_sha256':pins['head_source_sha256'],
        'same_hierarchy_source_as_initial_review':True,
        'changed_common_context_sources_since_initial_base':pins['context_source_changes_since_initial_base'],
        'source_public_before_after':[4,4],'source_private_before_after':[43,43],
        'source_headers_visibility_and_order_unchanged':True,'only_target_body_changed':True,
        'nonprivate_compiled_constants':[4,5],'all_compiled_constants':[137,138],
        'compiled_private_constants':[133,133],'sole_added_compiler_auxiliary':'Complexity.SPACE_linear_ne_NP._proof_1_1',
        'target_axioms':['propext','Classical.choice','Quot.sound'],'auxiliary_axioms':['propext','Quot.sound'],
        'foreign_definitions':['Complexity.NP','Complexity.SPACE','Complexity.padLang','Turing.pairEncode'],
        'effectively_sealed':4,'inventory_exclusions':[],'positive_controls':8,'negative_controls':8,
        'removed_default_simp_definition_unfoldings':['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg','Turing.NDTM.initCfg'],
        'screen_population_files':11,'eligible_body_counts':[247,248],'directional_pair_counts':[31,31],
        'reproduced_characters':[5917,5917],'new_pairs':0,'removed_pairs':0,
        'candidate_measurements_unchanged_from_initial_context':True,
        'parent_replay':'mlin2: 2 modules, 0 failed; checked complete before metadata/seals',
        'regressions_found':[],'git_mutations':False,'proof_source_edits':False,
        'existing_primary_pack_edited':False,'earlier_evidence_preserved':True,
        'lint_note':'Original per-file Hierarchy source lint remains valid by exact base/head text identity; no fresh lint run claimed.'}
    (H/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
