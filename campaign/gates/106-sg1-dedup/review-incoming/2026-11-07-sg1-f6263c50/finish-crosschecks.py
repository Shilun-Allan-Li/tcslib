"""Additional read-only audit checks. Supplied evidence is never executed."""
from collections import Counter,deque
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('pack_reader',OUT/'crosscheck.py')
reader=importlib.util.module_from_spec(spec);spec.loader.exec_module(reader)
REPO=reader.REPO;GATE=reader.GATE
spec=importlib.util.spec_from_file_location('declarations',REPO/'campaign/fills/mig1/review/checkpoint05-2026-11-07/compare.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)


def main():
    dispatch,sec=reader.sections()
    out={}
    four=['ClassNP/Tautology','TuringMachine/Build/CounterLoop','TuringMachine/Robustness/SingleTape','SpaceComplexity/Machines/Frag']
    changes={};calls={}
    helpers={'Tautology':'tautDual_segment_add','CounterLoop':'counter_span_append','SingleTape':'dgSpan_add'}
    # Manually inspected typed Segment receivers; other .trans calls are equality/order APIs.
    call_lines={'Tautology':[1353,1396,1440,1488,1518],
                'CounterLoop':[1294,1310,1403],
                'SingleTape':[1372,1489,1626,1718,1892,2109]}
    trans_quotes=[]
    for f in four:
        path='TCSlib/Complexity/'+f+'.lean';base=sec['campaign/gates/106-sg1-dedup/evidence/current/base-source/'+path+'.txt'];head=sec[path]
        changes[path]=mod.compare(base,head)
        result=changes[path]
        for k in ['public_added','public_removed','public_header_changes','visibility_changes','public_definition_changes']:assert not result[k],(path,k)
        assert result['public_order_unchanged']
        short=Path(f).name
        if short in helpers:
            h=helpers[short];consumers={}
            for d in mod.decls(base):
                n=len(re.findall(r'\b'+h+r'\b',d['code']))
                if n and not d['name'].endswith('.'+h):consumers[d['name']]=n
            ls=head.splitlines()
            count=sum(len(re.findall(r'\.trans\b',ls[i-1])) for i in call_lines[short])
            trans_quotes.extend([f'{path}:{i}: {ls[i-1]}' for i in call_lines[short]])
            calls[short]=dict(old_consumers=consumers,consumer_declarations=len(consumers),old_calls=sum(consumers.values()),manually_verified_Segment_trans_calls=count,composition_call_lines=call_lines[short],retired_helper_absent=not re.search(r'\b'+h+r'\b',mod.clean(head)))
    assert sum(len(r['public_proof_changes']) for r in changes.values())==6
    assert calls['SingleTape']['consumer_declarations']==6 and calls['SingleTape']['old_calls']==12
    assert {h:x['manually_verified_Segment_trans_calls'] for h,x in calls.items()}=={'Tautology':10,'CounterLoop':3,'SingleTape':12}
    assert all(x['retired_helper_absent'] for x in calls.values())
    out['four_file_freeze']=changes;out['composition_calls']=calls
    (OUT/'composition-call-quotes.txt').write_text('\n'.join(trans_quotes)+'\n')
    out['sealed_copies']={}
    for short,f in zip(['Tautology','CounterLoop','SingleTape'],four[:3]):
        src=sec['TCSlib/Complexity/'+f+'.lean'];p=GATE/'evidence/current/seal'/(short+'.lean.txt');probe=p.read_text()
        edits=[dict(tag=tag,old_lines=[a+1,b],new_lines=[c+1,d],inserted='\n'.join(probe.splitlines()[c:d])) for tag,a,b,c,d in difflib.SequenceMatcher(None,src.splitlines(),probe.splitlines(),autojunk=False).get_opcodes() if tag!='equal']
        assert all(e['tag']=='insert' for e in edits),short
        output=(p.parent/(short+'.out')).read_text()
        assert not re.search(r'^.*?:\d+:\d+: error:',output,re.M)
        out['sealed_copies'][short]=dict(original_source_unchanged=True,insertions=edits,
                                       supplied_output_bytes=len(output.encode()),supplied_errors=0)
    base=(GATE/'evidence/current/screen/screen-base.txt').read_text();head=(GATE/'evidence/current/screen/screen-head.txt').read_text()
    pattern=r'^\s*(\S+\.lean::\S+)\s+reproduces\s+(\S+\.lean::\S+):\s+(\d+)/(\d+) = (\d+)%$'
    def pairs(s):return {(m[1],m[2]):dict(common=int(m[3]),source_length=int(m[4]),percent=int(m[5])) for m in re.finditer(pattern,s,re.M)}
    a,b=pairs(base),pairs(head);assert len(a)==len(b)==1583
    out['screen_data']=dict(base_header=base.splitlines()[0],head_header=head.splitlines()[0],
                            added=[list(k) for k in b.keys()-a.keys()],removed=[list(k) for k in a.keys()-b.keys()])
    assert len(out['screen_data']['added'])==len(out['screen_data']['removed'])==1
    sat_hard=[dict(target=t,source=s,**v) for (t,s),v in b.items() if (t.startswith('SAT.lean::') and s.startswith('Hardness.lean::')) or (s.startswith('SAT.lean::') and t.startswith('Hardness.lean::'))]
    assert len(sat_hard)==86
    out['sat_hardness_candidates']=dict(directed=len(sat_hard),sat_endpoints=len({x.split('::')[1] for r in sat_hard for x in [r['target'],r['source']] if x.startswith('SAT.lean::')}),hardness_endpoints=len({x.split('::')[1] for r in sat_hard for x in [r['target'],r['source']] if x.startswith('Hardness.lean::')}))
    (OUT/'sat-hardness-directed-candidates.json').write_text(json.dumps(sat_hard,indent=2)+'\n')
    for label in ['base','head']:
        raw=(GATE/'evidence/current/axioms'/('ModuleCensus-'+label+'.out')).read_text()
        rows=[l for l in raw.splitlines() if l.startswith('CONSTANT ')]
        assert len(rows)==293
        out['compiled_'+label]=rows
    assert out['compiled_base']==out['compiled_head']
    out['compiled_census']=dict(base=293,head=293,all_name_owner_kind_internal_rows_equal=True)
    del out['compiled_base'];del out['compiled_head']
    ax=(GATE/'evidence/current/axioms/Axioms.out').read_text()
    entries=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",ax,re.M)
    assert len(entries)==6 and all(set(v.split(', '))=={'propext','Classical.choice','Quot.sound'} for n,v in entries)
    assert {n for n,v in entries}=={d['name'] for r in changes.values() for d in r['public_proof_changes']}
    out['axioms']=dict(names=[n for n,v in entries],all_six_changed_public_proofs_covered=True,only_standard_axioms_in_supplied_output=True)
    # Check availability in the audited consumer tree, using pinned source overrides.
    target='TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean';paths={}
    for start in ['TCSlib/Complexity/ClassNP/SAT.lean','TCSlib/Complexity/CookLevin/Hardness.lean']:
        q=deque([[start]]);seen=set()
        while q:
            path=q.popleft();f=path[-1]
            if f==target:paths[start]=path;break
            if f in seen:continue
            seen.add(f);p=REPO/f
            s=sec[f] if f in sec else p.read_text() if p.exists() else ''
            for l in s.splitlines():
                if l.startswith('import TCSlib.'):q.append(path+[l.split()[1].replace('.','/')+'.lean'])
        assert start in paths
    out['Segment_availability_paths']=paths
    out['limitation']='Static source and supplied-log checks only. No compiler, screen, Git, or delivered tool executed. Import paths use pinned9-file overrides and unchanged local dependency import headers.'
    (OUT/'additional-crosschecks.json').write_text(json.dumps(out,indent=2)+'\n')
    print('calls',calls)
    print('public changed',[(f,[d['name'] for d in r['public_proof_changes']]) for f,r in changes.items()])
    print('sealed probes contain source unchanged; screen data agree;293 census rows equal;6 axiom names agree')
    print('SAT/Hardness candidate endpoint counts',out['sat_hardness_candidates'])


if __name__=='__main__':main()
