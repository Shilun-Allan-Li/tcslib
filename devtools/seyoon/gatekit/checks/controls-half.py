from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

req, overlay, out = map(Path,sys.argv[1:4])
import os as _os
_GATE=Path(_os.environ['GATE']); _KIT=Path(__file__).resolve().parents[1]
r3=_GATE/'replay/runtime'
template=(_KIT/'templates/Native.lean.txt').read_text()
d=json.loads(req.read_text())
heads=sorted({n for x in d['owners'] for p in x['checks'] for n in p['heads']})
# RO1: private foreign heads cannot be named in a backtick list; left uncontrolled (disclosed, as in the seals)
heads=[h for h in heads if not h.startswith('_private')]
# gate 138: heads Lean already makes irreducible have no native rfl control; listed, not controlled
INHERENT=json.loads((_KIT/'templates/irreducible.json').read_text())['inherently_irreducible']
heads=[h for h in heads if h not in INHERENT]
# gate 122 r2: 104 sealed failures exceed Lean's default maxErrors (100); run the heads in two halves
import os
part=int(os.environ['HEADS_PART']);parts=int(os.environ.get('HEADS_PARTS','2'));heads=heads[part::parts]
simp=sorted({n for x in d['owners'] for p in x['checks'] for n in p['simp_removed']})
imports=''.join('import '+o['owner'][:-5].replace('/','.')+'\n' for o in d['owners'])
template=re.sub(r'^import TCSlib[^\n]*\n','',template,flags=re.M)
template=template.replace('import Lean\n','import Lean\n'+imports)
template=re.sub(r'^attribute \[-simp\][^\n]*\n','',template,flags=re.M)
# A typeclass instance can close by structure eta even with its head sealed.
# Keep these as raw delta controls by disabling class eta in both arms.
assert template.count('goal.mvarId!.refl')==1
template=template.replace('goal.mvarId!.refl',
    'withConfig (fun config => { config with etaStruct := .notClasses }) goal.mvarId!.refl')

nlist='['+', '.join(chr(96)+n for n in heads)+']'
template=re.sub(r'^  let targets : List Name := .*$',lambda _: '  let targets : List Name := '+nlist,template,flags=re.M)
marker='open Lean Elab Command Meta in\n'
assert template.count(marker)==1
out.mkdir()
rt=out/'runtime'
rt.mkdir()
(rt/'lean-toolchain').write_bytes((r3/'lean-toolchain').read_bytes())
(rt/'.lake').mkdir()
(rt/'.lake/packages').symlink_to((r3/'.lake/packages').resolve(),target_is_directory=True)

def run(sealed):
    name='Sealed' if sealed else 'Native'
    path=rt/(name+'.lean')
    attr='attribute [-simp] '+' '.join(simp)+'\n' if simp else ''
    if sealed:
        attr += 'attribute [local irreducible] '+' '.join(heads)+'\n'
    source=template.replace(marker,attr+marker)
    path.write_text(source)
    cmd=['bash',str(r3/'devtools/seyoon/leanelab.sh'),str(rt),str(overlay),path.name]
    p=subprocess.run(cmd,capture_output=True)
    raw=p.stdout+p.stderr
    log=raw.decode()
    (out/(name+'.log')).write_bytes(raw)
    results=re.findall(r'CONTROL\|(\d+)\|([^|\n]+)\|(point|abstract)\|(PASS|FAIL)',log)
    errs=re.findall(r'^.*?:\d+:\d+: error:.*$',log,re.M)
    expected={(n,k) for n in heads for k in ('point','abstract')}
    wanted='FAIL' if sealed else 'PASS'
    passed= (p.returncode==(1 if sealed else 0) and
        len(results)==len(expected) and {(n,k) for _,n,k,_ in results}==expected and
        all(status==wanted for _,_,_,status in results) and
        len(errs)==(len(expected) if sealed else 0) and
        all('CONTROL_RFL|' in x for x in errs) and
        log.count('kernelChecked=')==(0 if sealed else len(expected)))
    return {'name':name,'passed':passed,'argv':cmd,'exit':p.returncode,'identities':results,
        'errors':errs,'log_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(source.encode()).hexdigest()}

with ThreadPoolExecutor(max_workers=2) as pool:
    results=list(pool.map(run,(False,True)))
passed=all(r['passed'] for r in results)
(out/'RESULT.json').write_text(json.dumps({'passed':passed,'heads':heads,'simp_removed':simp,
    'paired_identities':2*len(heads),'runs':results},ensure_ascii=False,indent=2)+'\n')
print('CONTROL',len(heads),'definitions',2*len(heads),'matched identities', 'PASS' if passed else 'FAIL',flush=True)
sys.exit(0 if passed else 1)
