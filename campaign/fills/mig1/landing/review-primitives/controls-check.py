"""Independent pair/diagnostic coverage, including fixed-total adversarial multiplicity test."""
from pathlib import Path
import re,json,hashlib
out=Path(__file__).resolve().parent
source=(out/'Controls-sealed-v1.lean.txt').read_text()
raw=(out/'Controls-sealed-v1.out').read_text()
starts=[i for i,l in enumerate(source.splitlines(),1) if l.startswith('example')]
assert len(starts)==56
ends=starts[1:]+[len(source.splitlines())+1]
diags=[{'line':int(m.group(1)),'col':int(m.group(2)),'message':m.group(3)} for m in re.finditer(r'^.*?:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$',raw,re.M)]
def check(ds):
    assert len(ds)==len(starts),'total'
    used=[]
    for start,end in zip(starts,ends):
        owned=[(i,d) for i,d in enumerate(ds) if start<=d['line']<end]
        assert len(owned)==1,('multiplicity',start,len(owned))
        i,d=owned[0];assert 'rfl' in d['message'],('kind',d)
        used.append(i)
    assert sorted(used)==list(range(len(ds))),'unmapped'
    return True
assert check(diags)
# Preserve exactly 56 diagnostic entries while duplicating one and dropping another.
adversarial=[diags[0],diags[0]]+diags[2:]
assert len(adversarial)==len(diags)
try:
    check(adversarial)
except AssertionError as e:
    negative={'rejected':True,'reason':repr(e.args),'total_preserved':True,'duplicated_example_line':starts[0],'omitted_example_line':starts[1]}
else:raise AssertionError('multiplicity checker accepted fixed-count duplicate/drop')
unsealed=json.loads((out/'Controls-unsealed-v1-run.json').read_text());sealed=json.loads((out/'Controls-sealed-v1-run.json').read_text())
assert unsealed['exit']==0 and unsealed['errors']==0
assert sealed['exit']!=0 and sealed['errors']==56
result={'expected_pairs':28,'expected_goals':56,'actual_diagnostics':len(diags),'one_rfl_failure_per_goal':True,'no_unmapped_diagnostics':True,'unsealed_pass':True,'negative_duplicate_drop_test':negative,'input_sha256':hashlib.sha256(source.encode()).hexdigest(),'log_sha256':hashlib.sha256(raw.encode()).hexdigest()}
(out/'controls-negative-test.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
