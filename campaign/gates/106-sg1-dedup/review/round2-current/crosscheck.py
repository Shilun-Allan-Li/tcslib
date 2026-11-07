"""Independent offline verification of completed current evidence and retained family accounting."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
GATE=ROOT/'campaign/gates/106-sg1-dedup'
context=json.loads((OUT/'context.json').read_text())
spec=importlib.util.spec_from_file_location('source_tools',OUT/'source_tools.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,obj):(OUT/n).write_text(json.dumps(obj,indent=2)+'\n')

def check_controls(text,code,want):
    source=(OUT/'probes'/('Controls-sealed.lean.txt' if want else 'Controls-unsealed.lean.txt')).read_text().splitlines()
    starts=[i+1 for i,l in enumerate(source) if l.startswith('example')]
    ends=starts[1:]+[len(source)+1]
    diagnostics=list(re.finditer(r'^([^ \n][^\n]*?):(\d+):(\d+): error: ([^\n]+)',text,re.M))
    counts=Counter();stray=[];other=[]
    for d in diagnostics:
        line=int(d[2]);start=next((a for a,b in zip(starts,ends) if a<=line<b),None)
        if start is None:stray.append(line)
        else:counts[start]+=1
        if d[4]!='Tactic `rfl` failed: The left-hand side':other.append(d[4])
    bad=[dict(line=a,count=counts[a]) for a in starts if counts[a]!=want]
    return dict(examples=len(starts),errors=len(diagnostics),exit=code,
        expected_per_example=want,bad_examples=bad,stray=stray,other=other,
        accepted=len(starts)==2 and not(bad or stray or other) and (code!=0 if want else code==0))

def main():
    runs={}
    for f in sorted((OUT/'runs').glob('*.json')):
        if f.name.endswith('-request.json'):continue
        r=json.loads(f.read_text());stem=f.stem
        name,which=stem.rsplit('-',1)
        assert sha(OUT/'probes'/(name+'.lean.txt'))==r['input_sha256']
        assert sha(OUT/'logs'/(stem+'.out'))==r['output_sha256']
        request=json.loads((f.parent/(stem+'-request.json')).read_text())
        assert request['command']==r['command'] and request['input_sha256']==r['input_sha256']
        assert r['local_slots']=='3' and r['one_sequential_Lean'] and r['no_outer_lock']
        if stem=='Controls-sealed-head':assert r['exit']==1 and r['errors']==2
        else:assert r['exit']==r['errors']==0
        runs[stem]=dict(exit=r['exit'],errors=r['errors'],seconds=r['seconds'])
    assert set(runs)=={'GuardActualSAT-head','GuardActualHardness-head','Controls-unsealed-head','Controls-sealed-head','ModuleCensus-base','ModuleCensus-head','Axioms-head'}
    positive=check_controls((OUT/'logs/Controls-unsealed-head.out').read_text(),runs['Controls-unsealed-head']['exit'],0)
    negative_text=(OUT/'logs/Controls-sealed-head.out').read_text()
    negative=check_controls(negative_text,runs['Controls-sealed-head']['exit'],1)
    assert positive['accepted'] and negative['accepted']
    ds=list(re.finditer(r'^[^ \n][^\n]*?:\d+:\d+: error:',negative_text,re.M))
    duplicate=negative_text+'\n'+negative_text[ds[0].start():ds[1].start()]
    missing=negative_text[:ds[0].start()]+negative_text[ds[1].start():]
    (OUT/'logs/Controls-checker-duplicate.out').write_text(duplicate)
    (OUT/'logs/Controls-checker-missing.out').write_text(missing)
    checker=dict(duplicate=check_controls(duplicate,1,1),missing=check_controls(missing,1,1),exit_zero=check_controls(negative_text,0,1))
    assert all(not x['accepted'] for x in checker.values())
    census={}
    pattern=re.compile(r'^CONSTANT (\S+) module=(\S+) kind=(\S+) private=(\w+) internal=(\w+)$',re.M)
    for label in ['base','head']:
        rows={m[1]:dict(module=m[2],kind=m[3],private=m[4]=='true',internal=m[5]=='true') for m in pattern.finditer((OUT/'logs'/('ModuleCensus-'+label+'.out')).read_text())}
        assert rows and len(rows)==len(list(pattern.finditer((OUT/'logs'/('ModuleCensus-'+label+'.out')).read_text())))
        census[label]=rows
    delta={}
    for scope in ['all','nonprivate','private']:
        a,b=[{n:r for n,r in census[label].items() if scope=='all' or r['private']==(scope=='private')} for label in ['base','head']]
        delta[scope]=dict(base_count=len(a),head_count=len(b),added={n:b[n] for n in sorted(b.keys()-a.keys())},removed={n:a[n] for n in sorted(a.keys()-b.keys())},metadata_changed=[n for n in a.keys()&b.keys() if a[n]!=b[n]])
    assert delta['nonprivate']['base_count']==delta['nonprivate']['head_count']==1349
    assert not(delta['nonprivate']['added'] or delta['nonprivate']['removed'] or delta['nonprivate']['metadata_changed'])
    assert len(delta['private']['added'])==6 and len(delta['private']['removed'])==18
    save('compiler-census-delta.json',delta)
    guards={}
    for label in ['base','head']:
        text=(OUT/'logs'/('ModuleCensus-'+label+'.out')).read_text()
        rows=re.findall(r'^GUARD_AXIOMS (\S+): \[([^\]]*)\]$',text,re.M)
        assert len(rows)==2
        guards[label]={n:a.split(', ') for n,a in rows}
        assert all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in guards[label].values())
    assert set(guards['head'])=={'_private.TCSlib.Complexity.ClassNP.SAT.0.Complexity.sat_guard_add','_private.TCSlib.Complexity.CookLevin.Hardness.0.Complexity.clA5_guard_add'}
    assert guards['base']==guards['head']
    public_axioms=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",(OUT/'logs/Axioms-head.out').read_text(),re.M)
    assert len(public_axioms)==6 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for n,a in public_axioms)
    seal_axioms={}
    for label in ['SAT','Hardness']:
        text=(OUT/'logs'/('GuardActual'+label+'-head.out')).read_text()
        rows=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
        assert len(rows)==1 and set(rows[0][1].split(', '))=={'propext','Quot.sound'}
        seal_axioms[label]=dict(rows)
    exact_targets=[]
    applied=json.loads((GATE/'evidence/round2/applied-guard-patches.json').read_text())
    for row in applied['source_files']:
        assert context['source_pins'][row['path']]['base_sha256']==row['before_sha256']
        assert context['source_pins'][row['path']]['head_sha256']==row['after_sha256']
    for target in context['new_actual_seal_targets']:
        file=target['path'];label='SAT' if file.endswith('/SAT.lean') else 'Hardness'
        a,b=[(OUT/(which+'-source')/(file+'.txt')).read_text() for which in ['base','head']]
        raw=[]
        for text in [a,b]:
            d=next(d for d in s.decls(text) if d['name']==target['qualified_name'])
            last=d['start']-1+max(i+1 for i,line in enumerate(d['code'].splitlines()) if line.strip())
            raw.append(''.join(text.splitlines(keepends=True)[d['start']-1:last]))
        assert a.count(raw[0])==1 and a.replace(raw[0],raw[1],1)==b
        archived=(OUT/'exact-declarations'/(label+'.lean.txt')).read_text()
        assert archived==raw[1] and hashlib.sha256(archived.encode()).hexdigest()==target['exact_declaration_sha256']
        probe=(OUT/'probes'/('GuardActual'+label+'.lean.txt')).read_text()
        assert probe.count(archived)==1 and s.imports(probe)==s.imports(b)
        assert probe.index('attribute [local irreducible] Turing.Segment')<probe.index(archived)
        exact_targets.append(dict(name=target['qualified_name'],original_imports_and_exact_header_body_tested=True,all_other_source_bytes_unchanged=True))
    replay_folder=GATE/'evidence/round2/current-replay'
    replay=json.loads((replay_folder/'receipt.json').read_text())
    assert replay['head']==context['supplied_frozen_head'] and replay['campaign']==context['supplied_current_base']
    assert replay['modules']==329 and replay['failed']==replay['static_mismatches']==replay['replay_exit']==0
    for f,r in replay['files'].items():
        assert (replay_folder/f).stat().st_size==r['bytes'] and sha(replay_folder/f)==r['sha256']
    order=[l.removesuffix('.lean') for l in (replay_folder/'down-msg4.txt').read_text().splitlines() if l.strip()]
    entries=re.findall(r'^(TCSlib/\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',(replay_folder/'replay-msg4.log').read_text(),re.M)
    assert [r[0] for r in entries]==order and len(entries)==329 and all(r[1:3]==('0','0') for r in entries)
    assert sum(int(r[3]) for r in entries)==replay['static_total']==66
    assert (replay_folder/'replay-msg4-static.txt').read_text().strip()=='modules 329, mismatches 0, static total 66'
    comparison=json.loads((OUT/'source-comparison.json').read_text())
    source_counts={f:dict(public=r['public_counts'][1],private=r['private_counts'][1],total=sum([r['public_counts'][1],r['private_counts'][1]])) for f,r in comparison.items()}
    assert sum(x['total'] for x in source_counts.values())==1984
    expected_calls={'dg_init':3,'dg_collect':1,'dg_turn_with_growth':2,'dg_end_with_growth':2,'dg_step':3,'dg_simulate':1}
    single=(OUT/'head-source/TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean.txt').read_text()
    members={d['name'].split('.')[-1]:d for d in s.decls(single)}
    calls={}
    call_quotes=[]
    for n in expected_calls:
        code=members[n]['code']
        matches=list(re.finditer(r'\(dgSpan_iff_segment \.\.\)\.2',code))
        assert len(matches)==1,(n,len(matches))
        tail=code[matches[0].start():]
        calls[n]=len(re.findall(r'\.trans\b',tail))
        line=members[n]['start']+code[:matches[0].start()].count('\n')
        call_quotes.append(dict(name=n,line=line,calls=calls[n],source_tail=tail.rstrip()))
    assert calls==expected_calls
    save('single-tape-call-quotes.json',call_quotes)
    family=json.loads((GATE/'review-incoming/2026-11-07-sg1-f6263c50/family-accounting.json').read_text())
    sat_text=(OUT/'head-source/TCSlib/Complexity/ClassNP/SAT.lean.txt').read_text()
    hard_text=(OUT/'head-source/TCSlib/Complexity/CookLevin/Hardness.lean.txt').read_text()
    sat={d['name'].split('.')[-1]:d for d in s.decls(sat_text)}
    hard={d['name'].split('.')[-1]:d for d in s.decls(hard_text)}
    correspondence=[]
    for r in family['exact_correspondences']:
        a,b=sat[r['sat']],hard[r['hardness']]
        mapped=a['code'].replace('Sat','CLA5').replace('sat','clA5')
        assert s.norm(mapped)==s.norm(b['code'])
        correspondence.append(dict(kind=r['kind'],sat=r['sat'],hardness=r['hardness'],sat_line=a['start'],hardness_line=b['start'],prefix_renaming_equal=True))
    assert len(correspondence)==22
    hosts=[]
    for r in family['host_kind']:
        a,b=sat[r['sat']],hard[r['hardness']]
        mapped=a['code'].replace('Sat','CLA5').replace('sat','clA5').replace('Fin 6','Fin 5')
        if r['anchor_dispatch_target_parameter_changes_2_to_3']:
            mapped=mapped.replace('clA5HostEntry M 2','clA5HostEntry M 3')
        assert s.norm(mapped)==s.norm(b['code']),(r['sat'],mapped,b['code'])
        hosts.append(dict(sat=r['sat'],hardness=r['hardness'],kind=r['kind'],sat_line=a['start'],hardness_line=b['start'],parametric_correspondence_equal=True))
    assert len(hosts)==7 and sum(r['kind']!='abbrev' for r in hosts)==6
    save('retained-family-rechecks.json',dict(five_kinds=family['five_kinds'],exact22=correspondence,dispatcher=hosts,concrete_routing_tables_excluded=family['host_client_routing_tables_excluded'],named_union=dict(SAT=dict(declarations=270,known_named_lower_bound=34),Hardness=dict(declarations=544,known_named_lower_bound=32)),statuses='Six kinds acknowledged by Seyoon in canonical ledger; source routes, old watches and wider candidates retain their separate dispositions.',all86_historical_candidate_labels_preserved_in_incoming_review=True))
    tree_hashes=json.loads((OUT/'tree-hashes.json').read_text())
    for which in ['base','head']:
        root=Path(context[which+'_source'])
        current={p.relative_to(root).as_posix():sha(p) for p in sorted((root/'TCSlib').rglob('*.lean'))}
        assert current==tree_hashes[which]
        for file,h in context['compiler_sha256'][which].items():
            assert sha(Path(context[which+'_snapshot'])/(file.removesuffix('.lean')+'.olean'))==h
    result=dict(actual_guard_seals_pass=True,actual_seal_axioms=seal_axioms,exact_actual_seal_targets=exact_targets,
        positive_controls=positive,negative_controls=negative,synthetic_checker_negative_tests=checker,
        all_request_input_output_hashes_match=True,compiled_private_guard_ids_and_axioms=guards,
        six_public_axioms=dict(public_axioms),source_counts=source_counts,source_total=1984,
        unchanged_nonprivate_constants=1349,compiler_total_before_after=[7099,7087],
        single_tape_consumer_counts=calls,single_tape_consumer_declarations=6,single_tape_total_calls=12,
        current_replay_independently_crosschecked_not_rerun=dict(modules=329,failures=0,static_mismatches=0,static_total=66,all_artifact_hashes_match=True,order_matches_raw_log=True),
        all_base_head_source_and_selected_olean_hashes_unchanged=True,
        no_gate_closure_or_merge_clearance=True)
    save('checks.json',result)
    print(json.dumps({k:v for k,v in result.items() if k not in ['source_counts','compiled_private_guard_ids_and_axioms','six_public_axioms']},indent=2))

if __name__=='__main__':main()
