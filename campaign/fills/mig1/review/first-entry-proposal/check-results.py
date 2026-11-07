"""Verify actual probe receipts and exact control diagnostic multiplicity offline."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

OUT=Path(__file__).resolve().parent
context=json.loads((OUT/'context.json').read_text())

def controls(source,text,code,want):
    lines=source.read_text().splitlines()
    starts=[i+1 for i,l in enumerate(lines) if l.startswith('example')]
    ends=starts[1:]+[len(lines)+1]
    diagnostics=list(re.finditer(r'^([^ \n][^\n]*?):(\d+):(\d+): error: ([^\n]+)',text,re.M))
    counts=Counter();stray=[];other=[]
    expected='Tactic '+chr(96)+'rfl'+chr(96)+' failed: The left-hand side'
    for d in diagnostics:
        line=int(d[2])
        start=next((s for s,e in zip(starts,ends) if s<=line<e),None)
        if start is None:stray.append(line)
        else:counts[start]+=1
        if d[4]!=expected:other.append(d[4])
    bad=[dict(line=s,count=counts[s]) for s in starts if counts[s]!=want]
    accepted=len(starts)==8 and not(bad or stray or other) and (code!=0 if want else code==0)
    return dict(examples=len(starts),diagnostics=len(diagnostics),exit=code,
                expected_errors_per_example=want,bad_examples=bad,stray=stray,
                other_error_kinds=other,accepted=accepted)

def main():
    receipts={}
    for p in sorted(OUT.glob('*-run.json')):
        r=json.loads(p.read_text());stem=p.name.removesuffix('-run.json')
        source=OUT/(stem+'.lean.txt');log=OUT/(stem+'.out')
        assert hashlib.sha256(source.read_bytes()).hexdigest()==r['input_sha256']
        assert hashlib.sha256(log.read_bytes()).hexdigest()==r['output_sha256']
        receipts[stem]=r
    for n in ['Owner-home-v1','Consumers-v1','Inspect-step','Controls-unsealed-v2']:
        assert receipts[n]['exit']==receipts[n]['errors']==0,n
    assert receipts['Controls-unsealed']['exit']==1 and receipts['Controls-unsealed']['errors']==2
    assert receipts['Controls-sealed-v2']['exit']==1 and receipts['Controls-sealed-v2']['errors']==8
    s=OUT/'Controls-sealed-v2.lean.txt'
    unsealed=controls(OUT/'Controls-unsealed-v2.lean.txt',(OUT/'Controls-unsealed-v2.out').read_text(),0,0)
    text=(OUT/'Controls-sealed-v2.out').read_text()
    sealed=controls(s,text,1,1)
    assert unsealed['accepted'] and sealed['accepted']
    starts=list(re.finditer(r'^[^ \n][^\n]*?:\d+:\d+: error:',text,re.M))
    first=text[starts[0].start():starts[1].start()]
    duplicate=text+'\n'+first
    missing=text[:starts[0].start()]+text[starts[1].start():]
    negatives=dict(duplicate=controls(s,duplicate,1,1),missing=controls(s,missing,1,1),exit_zero=controls(s,text,0,1))
    assert all(not r['accepted'] for r in negatives.values())
    (OUT/'Controls-checker-duplicate.out').write_text(duplicate)
    (OUT/'Controls-checker-missing.out').write_text(missing)
    ax={}
    for stem in ['Owner-home-v1','Consumers-v1']:
        raw=(OUT/(stem+'.out')).read_text()
        rows=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",raw,re.M)
        assert len(rows)==(1 if stem=='Owner-home-v1' else 5)
        assert all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for n,a in rows)
        ax[stem]={n:a.split(', ') for n,a in rows}
    snap=Path(context['snapshot'])
    for f,sha in context['compiled_sha256'].items():
        assert hashlib.sha256((snap/(f.removesuffix('.lean')+'.olean')).read_bytes()).hexdigest()==sha
    wt=Path(context['api_worktree'])
    for f,sha in context['source_sha256'].items():
        assert hashlib.sha256((wt/f).read_bytes()).hexdigest()==sha
    result=dict(unapproved=True,implementation=False,owner_proof_passes_with_run_step_sealed=True,
                four_hypothetical_consumers_pass_with_run_step_sealed=True,
                positive_controls=unsealed,negative_controls=sealed,
                checker_negative_tests=negatives,checker_negative_tests_are_synthetic_not_Lean_runs=True,
                axioms=ax,all_receipt_hashes_match=True,source_and_snapshot_hashes_unchanged=True,
                receipts={k:dict(exit=r['exit'],errors=r['errors'],seconds=r['seconds']) for k,r in receipts.items()},
                unexecuted_archives=['Controls-sealed.lean.txt','Proposed-contract.lean.txt'],
                note='First Unit-specialized complete-step controls failed before sealing; final v2 uses abstract State. Initial sandboxed wrapper wait was interrupted, no completed Lean receipt; see execution notes.')
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['owner_proof_passes_with_run_step_sealed','four_hypothetical_consumers_pass_with_run_step_sealed','positive_controls','negative_controls','checker_negative_tests','source_and_snapshot_hashes_unchanged']},indent=2))

if __name__=='__main__':main()
