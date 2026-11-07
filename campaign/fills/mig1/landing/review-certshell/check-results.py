"""Offline exact diagnostics, hashes, source freeze and applied/sealed-body identity checks."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
OUT=Path(__file__).resolve().parent
def sha(data):return hashlib.sha256(data).hexdigest()
def controls(version,text,code,want):
    p=OUT/('Controls-'+('sealed' if want else 'unsealed')+'-'+version+'.lean.txt')
    lines=p.read_text().splitlines();starts=[i+1 for i,l in enumerate(lines) if l.startswith('example')];ends=starts[1:]+[len(lines)+1]
    ds=list(re.finditer(r'^([^ \n][^\n]*?):(\d+):(\d+): error: ([^\n]+)',text,re.M))
    counts=Counter();stray=[];other=[]
    for d in ds:
        line=int(d[2]);start=next((s for s,e in zip(starts,ends) if s<=line<e),None)
        if start is None:stray.append(line)
        else:counts[start]+=1
        if d[4]!='Tactic `rfl` failed: The left-hand side':other.append(d[4])
    bad=[dict(line=s,count=counts[s]) for s in starts if counts[s]!=want]
    return dict(examples=len(starts),diagnostics=len(ds),expected_per_example=want,exit=code,bad_examples=bad,stray=stray,other_error_kinds=other,
                accepted=len(starts)==82 and not(bad or stray or other) and (code!=0 if want else code==0))
def main():
    runs={}
    for f in OUT.glob('*-run.json'):
        name=f.name.removesuffix('-run.json');r=json.loads(f.read_text())
        if name=='Actual-source':data=Path(json.loads((OUT/'setup.json').read_text())['owned_source']).read_bytes()
        else:data=(OUT/(name+'.lean.txt')).read_bytes()
        assert sha(data)==r['input_sha256'] and sha((OUT/(name+'.out')).read_bytes())==r['output_sha256']
        q=json.loads((OUT/(name+'-request.json')).read_text());assert q['command']==r['command'] and q['input_sha256']==r['input_sha256']
        assert r['local_slots']=='3' and r['plain_managed'] and r['no_outer_lock']
        runs[name]=dict(exit=r['exit'],errors=r['errors'],seconds=r['seconds'])
    assert len(runs)==14
    failed={'CertShell-strict-v1':2,'Controls-sealed-v1':80,'Controls-sealed-v2':82,
            'Controls-unsealed-v3':1,'Controls-sealed-v3':82,'Controls-sealed-v4':82}
    for n,r in runs.items():
        assert r['exit']==(1 if n in failed else 0) and r['errors']==failed.get(n,0),(n,r)
    positive=controls('v4',(OUT/'Controls-unsealed-v4.out').read_text(),runs['Controls-unsealed-v4']['exit'],0)
    text=(OUT/'Controls-sealed-v4.out').read_text();negative=controls('v4',text,runs['Controls-sealed-v4']['exit'],1)
    assert positive['accepted'] and negative['accepted']
    ineffective=controls('v1',(OUT/'Controls-sealed-v1.out').read_text(),1,1)
    assert not ineffective['accepted'] and len(ineffective['bad_examples'])==2 and all(x['count']==0 for x in ineffective['bad_examples'])
    simplified=controls('v3',(OUT/'Controls-unsealed-v3.out').read_text(),1,0)
    assert not simplified['accepted'] and len(simplified['bad_examples'])==1
    ds=list(re.finditer(r'^[^ \n][^\n]*?:\d+:\d+: error:',text,re.M))
    duplicate=text+'\n'+text[ds[0].start():ds[1].start()]
    missing=text[:ds[0].start()]+text[ds[1].start():]
    (OUT/'Controls-checker-duplicate.out').write_text(duplicate);(OUT/'Controls-checker-missing.out').write_text(missing)
    checker=dict(duplicate=controls('v4',duplicate,1,1),missing=controls('v4',missing,1,1),exit_zero=controls('v4',text,0,1))
    assert all(not r['accepted'] for r in checker.values())
    inv=json.loads((OUT/'seal-inventory.json').read_text())
    assert len(inv['definitions'])==len(set(inv['definitions']))==41
    source=(OUT/'CertShell-final.lean.txt').read_text()
    assert source==(OUT/'CertShell-proposed-v2.lean.txt').read_text()
    guarded=(OUT/'CertShell-strict-v3.lean.txt').read_text()
    lo=guarded.index('section CertPrepareStrict\n');hi=guarded.index('/-- The loader interface,',lo)
    guard=guarded[lo:hi]
    assert guard.index('attribute [local irreducible]')<guard.index('attribute [-simp]')
    assert all(n in guard for n in inv['definitions'])
    restored=guarded[:lo]+guarded[hi:]
    restored=restored.replace('\nend CertPrepareStrict\n#print axioms cert_prepare_exists\n','',1)
    assert restored==source
    axioms=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",(OUT/'CertShell-strict-v3.out').read_text(),re.M)
    assert len(axioms)==1 and set(axioms[0][1].split(', '))=={'propext','Classical.choice','Quot.sound'}
    assert not re.search(r'\b(?:sorry|admit|unsafe)\b|allowUnsafeReducibility',source)
    app=json.loads((OUT/'application.json').read_text());context=json.loads((OUT/'setup.json').read_text())
    assert sha(source.encode())==app['new_sha256']
    assert Path(context['owned_source']).read_text()==source
    baseline=Path(context['snapshot']);overlay=Path(context['complete_private_overlay'])
    files={p.relative_to(baseline) for p in baseline.rglob('*') if p.is_file() and not p.is_symlink()}
    copied={p.relative_to(overlay) for p in overlay.rglob('*') if p.is_file() and not p.is_symlink()}
    assert files==copied
    assert all((baseline/p).stat().st_ino==(overlay/p).stat().st_ino for p in files)
    assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))
    result=dict(owned_actual_source_applied_and_elaborates=True,actual_source_sha256=app['new_sha256'],
        all_public_private_headers_imports_order_and_executable_definitions_unchanged=True,all_other_declaration_bytes_unchanged=True,
        target_only_strict_guard_before_docstring_and_header=True,sealed_ordinary_definitions=41,unchanged_legacy_helpers_outside_guard=True,
        positive_controls=positive,negative_controls=negative,ineffective_singleton_control_v1_correctly_rejected=ineffective,
        unsealed_simplified_control_v3_correctly_rejected=simplified,
        synthetic_checker_negative_tests=checker,synthetic_checker_logs_not_Lean_runs=True,
        actual_target_axioms=dict(axioms),initializer_and_whole_machine_and_transition_preservation_diagnostics_pass=True,
        all_request_and_input_output_hashes_match=True,runs=runs,complete_private_overlay_files=len(files),complete_overlay_paths_and_hardlink_identity_match_snapshot=True,
        scope='Actual source and exact sealed source elaborate against the complete mra2 import tree. No integration replay, new screen, compiled output, Git, push or other source edit performed.')
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['runs','synthetic_checker_negative_tests','ineffective_singleton_control_v1_correctly_rejected']},indent=2))
if __name__=='__main__':main()
