"""Source-only T4/T7 comparison. No Lean, Git, scripts from deliveries or screens."""
from pathlib import Path
import hashlib
import json
import re

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
SCRATCH=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch')
DELIVERY=ROOT/'campaign/fills/mig1/review/final-2026-11-07/extracted/fill-mig1-mega/source'
h=(ROOT/'campaign/fills/mig1/landing/compiled-comparison/declfreeze-helpers.py.txt').read_text()
assert hashlib.sha256(h.encode()).hexdigest()=='ef8a784f1ddbf086535d21cadb3221dc720bfe569482e0aa9afcb2503470028c'
ns={};exec(compile(h,'trusted-declfreeze-helper','exec'),ns)
queries={
 'TCSlib/Complexity/TuringMachine/Composition.lean':[
   'Turing.FinTM.computesFunInTime_comp','Turing.FinTM.exists_comp_on_image','Turing.FinTM.exists_comp_partial'],
 'TCSlib/Complexity/TuringMachine/Build/Loop.lean':[
   'Turing.loop_run','Turing.FinTM.loop_halted_run'],
 'TCSlib/Complexity/TuringMachine/Encoding.lean':[
   'Turing.FinTM.toCodeTM_computesInTime_iff','Turing.exists_codeTM_spaceUsed'],
 'TCSlib/Complexity/TuringMachine/Simulation.lean':['Turing.FinTM.bufferedSecondCfg_run'],
 'TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean':['Turing.vhostEmitTM_runFrom'],
}
rows=[];source_hashes=[];quotes=[]
for rel,names in queries.items():
    texts={}
    for stage,root in [('api1160',SCRATCH/'wt-natbits'),('producer',DELIVERY),('current',SCRATCH/'wt-epad')]:
        p=root/(rel+'.txt' if stage=='producer' else rel)
        if not p.exists():
            assert stage=='producer' and rel.endswith('VirtualInput.lean');continue
        text=p.read_text();texts[stage]=text
        source_hashes.append(dict(stage=stage,path=str(p),sha256=hashlib.sha256(text.encode()).hexdigest()))
    chunks={stage:{n:(private,t) for n,private,t in ns['chunks'](text)} for stage,text in texts.items()}
    for name in names:
        assert all(name in c for c in chunks.values()),name
        cur=chunks['current'][name][1]
        row=dict(name=name,path=rel,private=chunks['current'][name][0],
                 current_doc_line=texts['current'].count('\n',0,texts['current'].index(cur))+1,
                 current_declaration_line=texts['current'].count('\n',0,texts['current'].index(cur))+1+len(cur.splitlines())-len((cur.split('-/',1)[1] if cur.startswith('/--') else cur).lstrip().splitlines()),
                 api_chunk_literal_equal=cur==chunks['api1160'][name][1],
                 producer_chunk_literal_equal=cur==chunks['producer'][name][1] if 'producer' in chunks else None,
                 producer_absence_note='VirtualInput is not an owned/delivered module.' if 'producer' not in chunks else None,
                 sha256=hashlib.sha256(cur.encode()).hexdigest())
        rows.append(row);quotes.append('\n### '+name+' — '+rel+':'+str(row['current_doc_line'])+'\n'+cur+'\n')
        (OUT/(name.replace('.','_')+'.lean.txt')).write_text(cur+'\n')
    # Keep just the relevant full module's hash and chunks; no library source is edited.
(OUT/'source-comparison.json').write_text(json.dumps(rows,indent=2)+'\n')
(OUT/'source-hashes.json').write_text(json.dumps(source_hashes,indent=2)+'\n')
(OUT/'target-source-quotes.txt').write_text(''.join(quotes))
for row in rows:
    if row['name'] not in queries['TCSlib/Complexity/TuringMachine/Composition.lean']:
        assert row['api_chunk_literal_equal'] and row['producer_chunk_literal_equal'] is not False,row
    else:assert not row['api_chunk_literal_equal'] and row['producer_chunk_literal_equal'],row

meta=json.loads((ROOT/'campaign/fills/mig1/landing/compiled-comparison/map-final2.json').read_text())
canonical={
 'Turing.FinTM.computesFunInTime_comp':'Turing.FinTM.bufferedCompTM_computesFunInTime',
 'Turing.FinTM.exists_comp_on_image':'Turing.FinTM.bufferedCompTM_computesFunInTime_on_image',
 'Turing.FinTM.exists_comp_partial':'Turing.FinTM.bufferedCompTM_computes_iff',
}
reuse=[]
for root,lemma in canonical.items():
    cited=[c for c in meta['cited'] if c['root']==root and c['name']==lemma]
    assert len(cited)==1 and cited[0]['kind']=='theorem'
    reuse.append(dict(root=root,published_lemma=lemma,citation=cited[0],compiled_axioms=meta['root_axioms'][root]['axioms']))
(OUT/'T4-public-reuse.json').write_text(json.dumps(reuse,indent=2)+'\n')
inputs=[ROOT/'campaign/fills/mig1/briefs/megafill-mig1.md',
        ROOT/'campaign/fills/mig1/review/final-2026-11-07/extracted/fill-mig1-mega/REPORT.md',
        ROOT/'campaign/items/mig24/TRIAGE.md',ROOT/'campaign/items/mig24/README.md',
        ROOT/'campaign/items/mig24/triage-tm.tsv',ROOT/'campaign/duplication-ledger.md',ROOT/'campaign/backlog.md']
for rel in ['TCSlib/Complexity/TuringMachine/Deterministic.lean','TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean']:
    p=SCRATCH/'wt-epad'/rel;inputs.append(p)
    source_hashes.append(dict(stage='bounded public API candidate',path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(OUT/'source-hashes.json').write_text(json.dumps(source_hashes,indent=2)+'\n')
(OUT/'inputs.json').write_text(json.dumps([dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in inputs],indent=2)+'\n')
print(json.dumps(dict(T4='Three prepared source corollaries cite their exact published contracts, also present in supplied compiled direct-reference metadata.',
                      T7='All six inspected endpoints are literal-equal to API1160; five delivery-owned endpoints are also literal-equal to producer. VirtualInput is not delivery-owned.',
                      names=[dict(name=r['name'],line=r['current_declaration_line'],api_equal=r['api_chunk_literal_equal'],producer_equal=r['producer_chunk_literal_equal']) for r in rows]),indent=2))
