"""Bounded named correspondence checks, not a rerun of the copy-text screen."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reader',OUT/'crosscheck.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
_,sec=r.sections();REPO=r.REPO
spec=importlib.util.spec_from_file_location('decls',REPO/'campaign/fills/mig1/review/checkpoint05-2026-11-07/compare.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
SAT='TCSlib/Complexity/ClassNP/SAT.lean';HARD='TCSlib/Complexity/CookLevin/Hardness.lean'


def ren(t):return re.sub(r'\bSat','CLA5',re.sub(r'\bsat','clA5',t))
def arity(t):return re.sub(r'\bFin 6\b','Fin 5',ren(t))
def span(text,d):
    lines=text.splitlines();end=d['start']-1+max(i+1 for i,l in enumerate(d['code'].splitlines()) if l.strip())
    before='\n'.join(lines[:d['start']-1]).rstrip();start=d['start']
    if before.endswith('-/'):
        j=before.rfind('/--')
        if j>=0 and before.find('-/',j)==len(before)-2:start=before.count('\n',0,j)+1
    return dict(start=start,end=end,lines=end-start+1)


def main():
    sources={SAT:sec[SAT],HARD:sec[HARD]}
    a={d['name'].split('.')[-1]:d for d in m.decls(sources[SAT])};b={d['name'].split('.')[-1]:d for d in m.decls(sources[HARD])}
    groups={
        'uniform_clean_module_contract_and_bridges':['SatClean','satClean_install','satClean_emit','satClean_stop'],
        'bank_padding_action_cfg_machine_and_frame_run':['satPadAction','satPadCfg','satPadTM','satPad_apply','satPad_run','satPad_seam'],
        'positive_release_stop_adapter_and_correctness':['satStopTM','satStopCfg','satStop_step','satStop_clean'],
        'finite_word_transducer_cfg_run_poly_and_projections':['satMapTM','satMapWord','satMapCfg','satMap_run','satMap_poly','sat_pt_head','sat_pt_tail'],
        'polynomial_bridge_overhead_bound':['sat_bridge_bound']}
    rows=[];quotes=[]
    for group,names in groups.items():
        for n in names:
            other=n.replace('Sat','CLA5',1) if n.startswith('Sat') else n.replace('sat','clA5',1)
            x,y=a[n],b[other]
            assert m.norm(ren(x['header']))==m.norm(y['header'])
            assert m.norm(ren(x['code']))==m.norm(y['code'])
            rows.append(dict(kind=group,sat=n,hardness=other,header_and_code_equal_after_prefix_map=True,
                             sat_span=span(sources[SAT],x),hardness_span=span(sources[HARD],y)))
    assert len(rows)==22
    host=[]
    for n in ['SatHostState','satHostEntry','satHostRet','satHostTM','satHost_seam','satHost_call','satHost_clean']:
        other=n.replace('Sat','CLA5',1) if n.startswith('Sat') else n.replace('sat','clA5',1)
        x,y=a[n],b[other]
        code=arity(x['code'])
        target_index_change=n=='satHostTM'
        if target_index_change:code=code.replace('clA5HostEntry M 2','clA5HostEntry M 3')
        assert m.norm(code)==m.norm(y['code']),n
        host.append(dict(sat=n,hardness=other,kind=x['kind'],
                         code_equal_after_prefix_and_arity_substitution=True,
                         anchor_dispatch_target_parameter_changes_2_to_3=target_index_change,
                         sat_span=span(sources[SAT],x),hardness_span=span(sources[HARD],y)))
        for f,d in [(SAT,x),(HARD,y)]:
            sp=span(sources[f],d);ls=sources[f].splitlines()
            quotes.append(f'## {f}:{sp["start"]}–{sp["end"]}\n\n```lean\n'+'\n'.join(f'{i+1}: {ls[i]}' for i in range(sp['start']-1,sp['end']))+'\n```\n')
    # Current working-copy validation is source-only, anchored to all four msg3 scope hashes.
    wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-sg1'
    receipt=json.loads((r.GATE/'evidence/current-after-natbits/receipt.json').read_text())
    for row in receipt['audited_scope']:assert hashlib.sha256((wt/row['path']).read_bytes()).hexdigest()==row['source_sha256']
    current={f:(wt/f).read_text() for f in [SAT,HARD]}
    for row in rows+host:
        for f,key,old in [(SAT,'sat',a),(HARD,'hardness',b)]:
            ds={d['name'].split('.')[-1]:d for d in m.decls(current[f])}
            assert m.norm(ds[row[key]]['code'])==m.norm(old[row[key]]['code'])
    old_debt={SAT:['sat_first_halt','sat_call_first_halt','sat_pt_eq','satRed_one','sat_live_prefix'],
              HARD:['clA5_call_first_halt','clA5_pt_eq','clA5_live_prefix']}
    current_counts={f:len(m.decls(t)) for f,t in current.items()}
    counts={}
    for f,key in [(SAT,'sat'),(HARD,'hardness')]:
        n=[z[key] for z in rows]+[z[key] for z in host]+old_debt[f]
        assert len(set(n))==len(n)
        ds={d['name'].split('.')[-1]:d for d in m.decls(current[f])}
        assert all(n in ds for n in old_debt[f])
        counts[f]=dict(current_declarations=current_counts[f],current_source_sha256=hashlib.sha256(current[f].encode()).hexdigest(),
                       exact_five_kind_members=22,additional_host_non_abbrev_members=6,additional_host_abbrev_members=1,
                       other_named_active_members=old_debt[f],known_union_with_host_alias_excluding_F1=len(n),
                       known_union_with_host_alias_including_F1=len(n)+1,
                       note='Known named union/lower bound; wider RO1 and remaining semantic candidates are not asserted closed. Host alias shown explicitly; do not conflate rule10 abbrev transparency with a blanket census exemption.')
    # Family-only classification of every supplied directed SAT/Hardness screen candidate.
    candidates=json.loads((OUT/'sat-hardness-directed-candidates.json').read_text())
    exact_names={z['sat'] for z in rows}|{z['hardness'] for z in rows}
    host_names={z['sat'] for z in host}|{z['hardness'] for z in host}
    for row in candidates:
        ns={row['target'].split('::')[1],row['source'].split('::')[1]}
        if ns=={'sat_guard_add','clA5_guard_add'}:label='F1 cut-only composition; confirmed, outside old SG1'
        elif ns<={'sat_call_first_halt','clA5_call_first_halt'}:label='existing FH1'
        elif ns<={'sat_live_prefix','clA5_live_prefix'}:label='existing live-prefix watch/item11 T2'
        elif ns<={'sat_pt_eq','clA5_pt_eq'}:label='existing PL1/WT1'
        elif ns<=exact_names:label='F2 five exact generic kinds; repeated edges count each declaration once'
        elif ns<=host_names:label='additional finite-family shared-bank dispatcher kind; independent ruling needed'
        elif 'satRed_one' in ns:label='RO1 versus machine-step specializations; wider RO1 classification remains pending'
        elif any(n.startswith(('sat_pt_','clNative_','clLastCode_','clA5Fuel')) for n in ns):label='polynomial closure/field-reading candidates; existing PL1 and QF1 do not give blanket cross-file acceptance'
        elif any(n.startswith(('satScan','clA5Map')) for n in ns):label='generic transducer versus fixed scanner scaffold; not asserted same machine/contract'
        else:label='step/run-agreement scaffold with different statements; semantic candidate, not automatically debt or exempt'
        row['family_classification']=label
    out=dict(five_kinds=groups,exact_correspondences=rows,
             exact_correspondence_span_totals={key:sum(z[key]['lines'] for z in rows) for key in ['sat_span','hardness_span']},
             host_kind=host,host_client_routing_tables_excluded=['satHostNext','clA5HostNext'],
             prior_scopes=dict(SG1='private Segment predicates and their concatenation, explicitly excludes cut-only',
                               DR2='Primitives/Catalog/Loop family inventory, not SAT/Hardness adapters',
                               FH1='first-halting-time construction, not arbitrary stop/clean adapter proofs',
                               PL1_WT1='fixed-word test linear/poly lift and sat_pt_eq/clA5_pt_eq, not head/tail projections',
                               QF1='in-file row/field conversions, not blanket cross-file generic-machine acceptance',
                               MIG21_item13='clPlacement selector/certified-layout layer, not dispatcher/module host',
                               BL1='retired by NatBits in current tree; Hardness denominator545 to544'),
             cumulative_known_union=counts,directed_candidates_classified=candidates,
             limitation='Named static correspondence checks and supplied candidate classification only. No new copy-text screen, Lean, Git, or code change. Semantic candidate labels are not debt acknowledgment.')
    (OUT/'family-accounting.json').write_text(json.dumps(out,indent=2)+'\n')
    (OUT/'host-source-quotes.md').write_text('\n'.join(quotes))
    print('exact generic pairs22; span totals',out['exact_correspondence_span_totals'])
    print('dispatcher pairs7 =6 non-abbrevs +1 transparent type alias; all verified under explicit parameter map')
    print('known union',counts)


if __name__=='__main__':main()
