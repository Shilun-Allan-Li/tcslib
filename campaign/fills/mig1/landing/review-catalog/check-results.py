"""Offline validation of exact source restoration, diagnostics, controls and context pins."""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import re

OUT=Path(__file__).resolve().parent
CTX=json.loads((OUT/'context.json').read_text())
ERR=re.compile(r'^(.+\.lean):(\d+):(\d+): error(?:\(([^)]*)\))?: (.*)$',re.M)
STANDARD={'propext','Classical.choice','Quot.sound'}


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def diagnostics(text):
    return [dict(line=int(m[2]),column=int(m[3]),code=m[4],message=m[5]) for m in ERR.finditer(text)]


def axioms(text):
    found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
    return {n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in found}


def controls(source,ds,status,want,expected):
    lines=source.splitlines();starts=[i+1 for i,l in enumerate(lines) if l.startswith('example')]
    ends=[]
    for start in starts:
        end=next((i+1 for i in range(start-1,len(lines)) if ':= by rfl' in lines[i]),None)
        assert end is not None
        ends.append(end)
    if len(starts)!=expected or status!=(1 if want else 0):return False
    counts=[0]*len(starts)
    if len(ds)!=want*expected:return False
    for d in ds:
        owners=[i for i,(lo,hi) in enumerate(zip(starts,ends)) if lo<=d['line']<=hi]
        if len(owners)!=1 or d['code'] is not None or d['message']!='Tactic `rfl` failed: The left-hand side':return False
        counts[owners[0]]+=1
    return all(n==want for n in counts)


runs={};intervals=[]
for f in sorted(OUT.glob('*-run.json')):
    name=f.name.removesuffix('-run.json');r=json.loads(f.read_text());q=json.loads((OUT/(name+'-request.json')).read_text())
    assert all(r[k]==v for k,v in q.items()),name
    assert sha(OUT/(name+'.lean.txt'))==r['input_sha256'],name
    assert sha(OUT/(name+'.out'))==r['output_sha256'],name
    assert sha(Path(r['command'][-1]))==r['input_sha256'],name
    assert r['plain_managed'] and r['no_outer_lock'] and r['local_slots']=='3',name
    assert r['command'][0]=='bash' and r['command'][1].endswith('/devtools/seyoon/leanelab.sh'),name
    assert r['command'][2:4]==[CTX['worktree'],CTX['snapshot']],name
    text=(OUT/(name+'.out')).read_text();ds=diagnostics(text);assert len(ds)==r['errors'],name
    runs[name]=dict(exit=r['exit'],errors=r['errors'],warnings=len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M)),seconds=r['seconds'])
    start=datetime.datetime.fromisoformat(r['start_utc']).timestamp();intervals.append((start,start+r['seconds'],name))
assert all(a[1]<=b[0] for a,b in zip(sorted(intervals),sorted(intervals)[1:])), 'Own wrapper intervals overlapped'

control_results={}
for family,version,definitions,expected in [('Catalog','v3',45,90),('Code','v2',22,44)]:
    positive=family+'-controls-unsealed-'+version;negative=family+'-controls-sealed-'+version
    ps=(OUT/(positive+'.lean.txt')).read_text();ns=(OUT/(negative+'.lean.txt')).read_text()
    assert re.sub(r'^attribute \[local irreducible\] .*\n','',ns,flags=re.M)==ps
    pd=diagnostics((OUT/(positive+'.out')).read_text());nd=diagnostics((OUT/(negative+'.out')).read_text())
    assert controls(ps,pd,runs[positive]['exit'],0,expected)
    assert controls(ns,nd,runs[negative]['exit'],1,expected)
    trials=dict(missing=not controls(ns,nd[:-1],1,1,expected),
                duplicate_replacing_missing=not controls(ns,[nd[0]]+nd[:-1],1,1,expected),
                exit_zero=not controls(ns,nd,0,1,expected),
                unexpected_kind=not controls(ns,[dict(nd[0],code='lean.synthetic')]+nd[1:],1,1,expected))
    assert all(trials.values())
    mapping=json.loads((OUT/(family+'-controls-'+('v2-control-map.json' if family=='Catalog' else 'v2-control-map.json'))).read_text())
    assert len(mapping)==definitions
    starts=[i+1 for i,l in enumerate(ns.splitlines()) if l.startswith('example')]
    for i,row in enumerate(mapping):
        row.update(pointwise_line=starts[2*i],abstracted_line=starts[2*i+1],
                   pointwise_error_line=nd[2*i]['line'],abstracted_error_line=nd[2*i+1]['line'])
    (OUT/(family+'-controls-checked-map.json')).write_text(json.dumps(mapping,indent=2)+'\n')
    control_results[family]=dict(definitions=definitions,examples=expected,unsealed_exit=0,unsealed_errors=0,
                                 sealed_exit=1,sealed_errors=expected,exactly_one_expected_failure_per_example=True,
                                 isolated_one_definition_per_section=True,synthetic_rejections=trials)

eligible=json.loads((OUT/'eligible-seal-v2.json').read_text())
s=(OUT/'Catalog-eligible-strict-v2.lean.txt').read_text()
for piece in eligible['inserted_pieces']:
    assert s.count(piece)==1;s=s.replace(piece,'',1)
assert s==(OUT/'Catalog-current.lean.txt').read_text()
assert 'open private' not in s and not re.search(r'\bloopHostM\b',s)
assert runs['Catalog-eligible-strict-v2']['exit']==0 and runs['Catalog-eligible-strict-v2']['errors']==0
ca=axioms((OUT/'Catalog-eligible-strict-v2.out').read_text());assert len(ca)==24
assert all(set(a)==STANDARD for a in ca.values())
final=json.loads((OUT/'code-seal-final.json').read_text());s=(OUT/'CodeSimulator-strict-current-v3.lean.txt').read_text()
for piece in final['inserted_pieces']:
    assert s.count(piece)==1;s=s.replace(piece,'',1)
assert s==(OUT/'CodeSimulator-repaired.lean.txt').read_text()
assert runs['CodeSimulator-strict-current-v3']['exit']==0 and runs['CodeSimulator-strict-current-v3']['errors']==0
co=axioms((OUT/'CodeSimulator-strict-current-v3.out').read_text());assert len(co)==1 and all(set(a)==STANDARD for a in co.values())
compiled=axioms((OUT/'Compiled-axioms-v1.out').read_text());assert len(compiled)==28 and all(set(a)==STANDARD for a in compiled.values())
assert runs['Catalog-strict-v1']['exit']==1 and runs['Catalog-strict-v1']['errors']==2
assert runs['Catalog-pending-strict-v1']['exit']==1 and runs['Catalog-pending-strict-v1']['errors']==2
assert runs['CodeSimulator-strict-current-v2']['exit']==1 and runs['CodeSimulator-strict-current-v2']['errors']==1
assert 'sorryAx' in (OUT/'CodeSimulator-strict-current-v2.out').read_text()

assert sha(Path(CTX['worktree'])/'TCSlib/Complexity/TuringMachine/Build/Catalog.lean')==sha(OUT/'Catalog-current.lean.txt')=='eb55b3b7688f3949667df21151b8dc3036b99bd80ed467b20bf466bcedee213d'
assert sha(Path(CTX['worktree'])/'TCSlib/Complexity/TuringMachine/CodeSimulator.lean')==sha(OUT/'CodeSimulator-repaired.lean.txt')=='57e7dc52dedf3d146499ad5694270d1c6fee7255cad74338d4174c5cce3e1a73'
pins=[]
for row in CTX['modules']:
    compiled_path=Path(CTX['snapshot'])/Path(row['module']).with_suffix('.olean')
    assert sha(compiled_path)==row['compiled_sha256'],row['module']
    assert sha(Path(row['archived_source_path']))==row['archived_source_sha256'],row['module']
    pins.append(row['module'])
assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))
arguments=json.loads((OUT/'tactic-arguments.json').read_text());assert len(arguments)==81
assert all(not r['direct_foreign_definition_unfold'] for r in arguments)
freeze=json.loads((OUT/'freeze.json').read_text());codefreeze=json.loads((OUT/'code-freeze-repaired.json').read_text())
assert freeze['all_shared_headers_literal_equal'] and freeze['all_shared_definition_tables_and_types_literal_equal']
assert codefreeze['all_headers_literal_equal'] and codefreeze['all_definitions_tables_types_literal_equal']
result=dict(status='HOLD: three Catalog rule-10 leaves remain; scoped successful regions and repaired Code proof verified only',
            checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            Catalog_successful_proofs=24,Catalog_sealed_definitions=45,Catalog_axioms=ca,
            Catalog_HOLD=['computesFunInTime_pairDup_spaceUsed: pending zero-space reader',
                          'computesFunInTime_incFixed_spaceUsed: pending zero-space reader',
                          'redirectTM_spaceUsedByTape: frozen header depends on opaque redirectTM.k; home/statement ruling pending'],
            CodeSimulator_repaired_source=final['source_sha256'],CodeSimulator_guard_count=22,
            CodeSimulator_axioms=co,controls=control_results,
            imported_compiled_root_axioms=compiled,
            compiled_axiom_context='Exact preflight-current1: Catalog eb55, CodeSimulator old78837; repaired57e7 checked directly by plain full-source strict22. No new compiled module created.',
            exact_guard_removal_restores_sources=True,unchanged_compiled_context_modules=pins,
            own_managed_wrapper_intervals_nonoverlapping=True,runs=runs,
            argument_review=dict(sites=81,nested_symbolic_mentions=2,direct_foreign_unfold_found=0,
                                 limit='Bounded candidate capture plus manual inspection; not a whole-library screen.'),
            no_source_Git_snapshot_cache_or_compiled_output_mutations=True,
            no_external_gate_dispatch_closure_or_merged_tree_replay_claim=True)
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(runs=len(runs),Catalog='24/45 seals PASS;3HOLD',Code='repaired22 PASS',
                      controls=control_results,unchanged_compiled_modules=len(pins),compiled_roots=len(compiled)),indent=2))
