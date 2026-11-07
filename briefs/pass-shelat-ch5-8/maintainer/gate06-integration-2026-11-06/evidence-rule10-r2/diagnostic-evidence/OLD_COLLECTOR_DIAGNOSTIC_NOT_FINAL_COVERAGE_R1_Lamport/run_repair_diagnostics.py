"""Run diagnostic seals against old collected rows; never attest final coverage."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

r=Path.cwd()
g=r/'.lake/ps-maintainer/gate06'
e=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2')
helper=g/'repairs/prepare_current_diagnostic_seal.py'
assert hashlib.sha256(helper.read_bytes()).hexdigest()=='39659352a439bbb1f1511ade405704aab7aa51951f9c8c9e40d8cbcd472ec6f7'
modules=['TCSlib.Cryptography.Authentication.PRFMAC','TCSlib.Cryptography.Authentication.Lamport',
         'TCSlib.Cryptography.Authentication.HashAndSign','TCSlib.Cryptography.Composability.CCA2Scheme',
         'TCSlib.Cryptography.Composability.PRFScheme','TCSlib.Cryptography.Composability.PublicKey',
         'TCSlib.Cryptography.Composability.SequentialZK','TCSlib.Cryptography.Composability.NonMalleable',
         'TCSlib.Cryptography.Randomness.BPPBridge','TCSlib.Cryptography.Randomness.Learning']
records=[]
for module in modules:
    suffix='R1_'+module.rsplit('.',1)[1]
    prep=subprocess.run(['python3','-I',str(helper),module,suffix],check=True,capture_output=True,text=True,cwd=r)
    prepared=json.loads(prep.stdout)
    mpath=Path(prepared['metadata']);m=json.loads(mpath.read_text())
    assert m['status']=='OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE'
    assert hashlib.sha256((r/m['source']).read_bytes()).hexdigest()==m['source_sha256']
    subprocess.run(m['native_command'],cwd=r,check=False)
    out=mpath.parent/'native';label=m['label'];result=json.loads((out/(label+'.json')).read_text())
    text=(out/(label+'.log')).read_text()
    assert result['source_sha256']==m['probe_sha256'] and result['source_unchanged']
    assert hashlib.sha256((r/m['source']).read_bytes()).hexdigest()==m['source_sha256']
    n=m['requested_count'];rows=m['requested_names']
    already=sum(v['collector_reducibility']=='irreducible' for v in rows)
    expected=f'G06-SEAL label={label} requested={n} active={n-already} already_irreducible={already} verified={n}'
    assert text.splitlines().count(expected)==1
    assert text.splitlines().count(m['runtime_required']['eof_marker'])==1
    actual={}
    for line in text.splitlines():
        match=re.fullmatch(r'G06-NAME label=(\S+) spelling=(.*?) actual=(.*?) home=(\S+) before=Lean.ReducibilityStatus\.(\w+) installed=Lean.ReducibilityStatus\.(\w+)',line)
        if match:
            lab,spelling,name,home,status,installed=match.groups()
            assert lab==label and spelling==name and installed=='irreducible' and spelling not in actual
            actual[spelling]=(home,status)
    assert actual=={v['spelling']:(v['home'],v['collector_reducibility']) for v in rows}
    errors=[{'probe_line':int(a),'column':int(b),'code':c or None} for a,b,c in
            re.findall(r'\.lean:(\d+):(\d+): error(?:\(([^\n)]*)\))?:',text)]
    inverse={v['probe_line']:v['source_line'] for v in m['source_to_probe_lines']}
    for v in errors:
        assert v['probe_line'] in inverse,'Harness error is not source proof evidence'
        v['source_line']=inverse[v['probe_line']]
    assert len(errors)==result['error_diagnostics']
    assert (result['rc']!=0) if errors else (result['rc']==0 and result['fresh_nonempty_object'])
    record={'status':'OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE','module':module,
            'valid_harness':True,'old_rows_verified':n,'errors':errors,'result':result,
            'current_source_sha256':m['source_sha256'],'fresh_final_collector_required':True}
    (mpath.parent/'runtime-validation.json').write_text(json.dumps(record,indent=2)+'\n')
    (mpath.parent/'run_repair_diagnostics.py').write_bytes(Path(__file__).read_bytes())
    records.append(record)
    print('REPAIR DIAGNOSTIC',module,'source_errors',len(errors),flush=True)
dest=e/'diagnostic-evidence/repair-r1-summary.json'
assert not dest.exists()
dest.write_text(json.dumps({'status':'OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE','results':records,
                           'limit':'Initial snapshot names only; no current collector coverage or gate pass is asserted.'},indent=2)+'\n')
