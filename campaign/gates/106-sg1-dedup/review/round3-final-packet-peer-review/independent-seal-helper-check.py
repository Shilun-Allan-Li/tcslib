"""Independent final seal/control and transitive-helper data review; no supplied code runs."""
from pathlib import Path
import ast
import collections
import hashlib
import json
import os
import re

R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
G=R/'campaign/gates/106-sg1-dedup/review'
OUT=Path('/private/tmp/sg1-final-packet-peer-review-output')
sha=lambda b:hashlib.sha256(b).hexdigest()
readj=lambda p:json.loads(p.read_text())
result={'seals':[],'helpers':[]}
for folder,n,stem,src in [
    ('round3-pair-bound-applied',21,'Hardness-native-v1','Hardness-after.lean.txt'),
    ('round3-image-repoint',14,'Tautology-actual-native-v1','Tautology-proposed.lean.txt')]:
    p=G/folder
    for row in readj(p/'MANIFEST.json')['files']:
        b=(p/row['path']).read_bytes()
        assert (len(b),sha(b))==(row['bytes'],row['sha256'])
    names=(p/'control-definitions.txt').read_text().splitlines()
    assert len(names)==len(set(names))==n
    expected=collections.Counter({(name,mode):1 for name in names for mode in ['point','abstract']})
    for side,want,exit_code in [('unsealed','PASS',0),('sealed','FAIL',1)]:
        text=(p/('Controls-'+side+'-v1.out')).read_text()
        rows=[x.split('|') for x in text.splitlines() if x.startswith('CONTROL|')]
        assert collections.Counter((x[1],x[2]) for x in rows)==expected
        assert all(x[3]==want for x in rows)
        receipt=readj(p/('Controls-'+side+'-v1-run.json'))
        errors=len(re.findall(r'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',text))
        assert receipt['exit']==exit_code and receipt['errors']==errors==2*n*exit_code
        assert receipt['output_sha256']==sha(text.encode())
        if side=='unsealed':assert len({x[4] for x in rows})==2*n and all(x[4].startswith('kernelChecked=') for x in rows)
        else:assert collections.Counter(re.findall(r'RFL_CONTROL\|([^|\n]+)\|(point|abstract)\|',text))==expected
    source=(p/src).read_text();append=(p/'metadata-append.lean.txt').read_text()
    native=(p/(stem+'.lean.txt')).read_text()
    assert native==source+append
    sealed_stem='Hardness-all11-sealed-v1' if n==21 else 'Tautology-actual-sealed-v1'
    sealed=(p/(sealed_stem+'.lean.txt')).read_text()
    instrumentation=readj(p/'instrumentation.json')
    if isinstance(instrumentation,list):
        assert len(instrumentation)==11
        for item in instrumentation:
            assert sealed.count(item['prefix'])==sealed.count(item['suffix'])==1
            assert all(name in item['prefix'] for name in names)
            sealed=sealed.replace(item['prefix'],'').replace(item['suffix'],'')
    else:
        assert sealed.count(instrumentation['guard'])==sealed.count(instrumentation['suffix'])==1
        assert all(name in instrumentation['guard'] for name in names)
        sealed=sealed.replace(instrumentation['guard'],'').replace(instrumentation['suffix'],'')
    assert sealed==native
    for key in [stem,sealed_stem]:
        receipt=readj(p/(key+'-run.json'));raw=(p/(key+'.out')).read_bytes()
        assert receipt['exit']==receipt['errors']==0 and receipt['output_sha256']==sha(raw)
        assert receipt['input_sha256']==sha((p/(key+'.lean.txt')).read_bytes())
    result['seals'].append(dict(folder=folder,guarded_definitions=n,paired_controls=2*n,
        exact_positive_kernel_checked_identities=2*n,exact_negative_diagnostic_identities=2*n,
        native_and_scoped_seal_receipts_zero_errors=True,guard_and_append_removal_recovers_exact_source=True,
        independently_executed_Lean=False))

names=['mkdownmulti.py','graph.py','mkreplay.py','mkbundle-mixed.py','verifybundle.py','declfreeze.py','pairdiff.py']
names+=['copy-text-screen-v3.py','style_lint.py','campaign_style_lint.py']
for name in names:
    rel=('scripts/' if name in ['copy-text-screen-v3.py','style_lint.py','campaign_style_lint.py'] else 'devtools/seyoon/')+name
    f=R/rel;tree=ast.parse(f.read_text());imports=[]
    for node in ast.walk(tree):
        if isinstance(node,ast.Import):imports.extend(x.name for x in node.names)
        elif isinstance(node,ast.ImportFrom):imports.append(node.module)
    result['helpers'].append(dict(path=rel,bytes=f.stat().st_size,sha256=sha(f.read_bytes()),imports=sorted(set(imports))))
result['transitive_local_dependency']='mkdownmulti.py→graph.py→stdlib(os,sys); graph.py is sole missing local import in frozen candidate. All screen/freeze/lint/metadata checker local file dependencies are included.'
tools=Path(os.environ['TCSLIB_SCRATCH'])/'tools';copies=[]
for name in ['graph.py','mkdownmulti.py','mkreplay.py']:
    a=(tools/name).read_bytes();b=(R/'devtools/seyoon'/name).read_bytes();assert a==b
    copies.append(dict(actual_path=str(tools/name),included_or_required_path='devtools/seyoon/'+name,bytes=len(a),sha256=sha(a),exact=True))
a=(tools/'mk-next.sh').read_bytes();bootstrap=R/'campaign/status/2026-11-06-mac-bootstrap/mk-next-codex.sh'
assert a==bootstrap.read_bytes()
copies.append(dict(actual_path=str(tools/'mk-next.sh'),included_or_required_path=str(bootstrap.relative_to(R)),bytes=len(a),sha256=sha(a),exact=True,
                   note='Actual Codex generator matches included bootstrap variant, not the generic devtools/seyoon/mk-next.sh.'))
result['actual_generation_helper_copy_checks']=copies
(OUT/'seals-and-dependencies.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
