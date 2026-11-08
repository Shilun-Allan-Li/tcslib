from collections import Counter
from copy import deepcopy
from pathlib import Path
import hashlib, json, re
out=Path(__file__).resolve().parent
names=(out/'control-definitions.txt').read_text().splitlines()
keys=[(n,m) for n in names for m in ('point','abstract')]
expected=Counter({k:1 for k in keys})
def verify(pos,neg,pr,nr):
    for raw,wanted in ((pos,'PASS'),(neg,'FAIL')):
        rows=[line.split('|') for line in raw.splitlines() if line.startswith('CONTROL|')]
        assert Counter((x[1],x[2]) for x in rows)==expected
        assert [(x[1],x[2]) for x in rows]==keys
        assert all(x[3]==wanted for x in rows)
        if wanted=='PASS':
            assert all(len(x)==5 and x[4]==f'kernelChecked=F6LandingControl_{i}_{x[2]}' for i,x in enumerate(rows,1))
            assert len({x[4] for x in rows})==len(keys)
        else: assert all(len(x)==4 for x in rows)
        assert "declaration uses 'sorry'" not in raw
    assert Counter(re.findall(r'RFL_CONTROL\|([^|\n]+)\|(point|abstract)\|',neg))==expected
    pattern=r'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:'
    assert len(re.findall(pattern,pos))==0 and len(re.findall(pattern,neg))==len(keys)
    assert (pr['exit'],pr['errors'])==(0,0)
    assert (nr['exit'],nr['errors'])==(1,len(keys))
pos=(out/'Controls-native.lean.out').read_text();neg=(out/'Controls-sealed.lean.out').read_text()
pr=json.loads((out/'Controls-native.lean-run.json').read_text());nr=json.loads((out/'Controls-sealed.lean-run.json').read_text())
verify(pos,neg,pr,nr)
ids=re.findall(r'RFL_CONTROL\|[^|\n]+\|(?:point|abstract)\|',neg)
cases={'duplicate-negative-identity':(pos,neg.replace(ids[0],ids[1],1),pr,nr),'wrong-negative-outcome':(pos,neg.replace('|point|FAIL','|point|PASS',1),pr,nr),'missing-kernel-name':(pos.replace('kernelChecked=F6LandingControl_1_point','kernelChecked=missing',1),neg,pr,nr),'wrong-negative-exit':(pos,neg,pr,{**nr,'exit':0}),'unexpected-sorry-warning':(pos+"\ndeclaration uses 'sorry'\n",neg,pr,nr)}
rejected={}
for label,args in cases.items():
    try:verify(*args)
    except AssertionError:rejected[label]='rejected'
    else:raise AssertionError('invalid evidence accepted: '+label)
result=dict(result='PASS',definitions=len(names),exact_positive_identities=len(keys),exact_expected_negative_identities=len(keys),all_kernel_checked_positive_names=True,source_sections=19,effective_TCSlib_definitions=35,extra_Mathlib='Nat.bits',all_actual_run_exits=[json.loads((out/(name+'-run.json')).read_text())['exit'] for name in ('Owner-native.lean','Owner-sealed.lean','Controls-native.lean','Controls-sealed.lean')],negative_corruption_cases=rejected,scope_limit='14abbrevprojections and2ineffective regularFintypeinstances remain separately disclosed; no blanket allforeign seal')
(out/'control-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
