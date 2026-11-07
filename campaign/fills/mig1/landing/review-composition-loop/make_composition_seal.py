"""Guard every changed/new Composition proof without changing its declaration body."""
from pathlib import Path
import hashlib
import json
import os
import re
import sys
out=Path(__file__).resolve().parent
source=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad/TCSlib/Complexity/TuringMachine/Composition.lean'
s=source.read_text();label=sys.argv[1]
if not re.fullmatch(r'[A-Za-z0-9_-]+',label): raise SystemExit('bad label')
prior=(out/'Wrappers-new-seal-v1.lean.txt').read_text()
line=next(l for l in prior.splitlines() if l.startswith('attribute [local irreducible]'))
defs=line.split('] ',1)[1].split()+['Turing.FinTM.bufferedCompTM']
assert len(defs)==len(set(defs))==23
names=['idTM_computes','computesFunInTime_id','ifEqTM_computes','computesFunInTime_ifEq',
'computesFunInTime_comp','exists_comp_on_image','exists_comp_partial','condTM_branch_run',
'condTM_computes_iff','exists_cond']
regions=[]
for name in names:
    m=re.search(r'(?m)^(?:private )?(?:lemma|theorem) '+re.escape(name)+r'(?=\s|\{|\()',s)
    if not m: raise SystemExit('missing: '+name)
    a=s.rfind('/--',0,m.start())
    nextDoc=s.find('\n/--',m.end())
    b=(nextDoc+1) if nextDoc>=0 else s.rindex('end Turing.FinTM')
    if a<0: raise SystemExit('missing doc: '+name)
    regions.append(dict(name=name,start=a,end=b,first_line=s.count('\n',0,a)+1,
      last_line=s.count('\n',0,b),source_sha256=hashlib.sha256(s[a:b].encode()).hexdigest()))
regions.sort(key=lambda r:r['start'])
for r1,r2 in zip(regions,regions[1:]): assert r1['end']<=r2['start']
result=s
for i,r in reversed(list(enumerate(regions))):
    guard=f'section CompositionNewSeal{i}\nattribute [local irreducible] '+' '.join(defs)+'\n'
    guard+='attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
    close=f'end CompositionNewSeal{i}\nattribute [simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n\n'
    result=result[:r['start']]+guard+result[r['start']:r['end']]+close+result[r['end']:]
p=out/(label+'.lean.txt');manifest=out/(label+'.coverage.json')
if p.exists() or manifest.exists(): raise SystemExit('refuse overwrite')
p.write_text(result)
manifest.write_text(json.dumps(dict(source=str(source),source_sha256=hashlib.sha256(s.encode()).hexdigest(),
 sealed_definitions=defs,default_simp_removed=['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],
 regions=regions,probe_sha256=hashlib.sha256(result.encode()).hexdigest()),indent=2)+'\n')
print(json.dumps(dict(probe=str(p),definitions=len(defs),regions=[r['name'] for r in regions]),indent=2))
