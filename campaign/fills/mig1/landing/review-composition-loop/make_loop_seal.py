"""Copy the current Loop source with guards around each changed/new proof declaration."""
from pathlib import Path
import hashlib
import json
import os
import re
import sys
out=Path(__file__).resolve().parent
source=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad/TCSlib/Complexity/TuringMachine/Build/Loop.lean'
s=source.read_text()
label=sys.argv[1]
if not re.fullmatch(r'[A-Za-z0-9_-]+',label): raise SystemExit('bad label')
prior=(out/'Wrappers-new-seal-v1.lean.txt').read_text()
line=next(l for l in prior.splitlines() if l.startswith('attribute [local irreducible]'))
defs=line.split('] ',1)[1].split()+['Turing.captureCfg','Turing.captureAction','Turing.emitCfg','Turing.Cfg.ofWords',
    'Turing.Cfg.mapState','Turing.embedEmitCfg','Turing.embedEmitTM','Turing.FinTM.bufferedCompTM']
assert len(defs)==len(set(defs))==30
names=['loop_first_halt','loopHost_input_rewind','loopHost_prepare','loopCall_heads',
'loopHost_contracts','segment_heads','seamed_space','loopHostTM_contracts','exists_loopCfgTM',
'loopHostTM_decides','exists_loopTM','loopHostTM_finds','loopHostTM_spaceUsed_le_budget',
'exists_loopFindTM','emitLoopTM_computes','exists_emitLoopTM']
# Optional extra names must be reviewed before they are supplied to this script.
names+=sys.argv[2:]
regions=[]
for name in names:
    m=re.search(r'(?m)^(?:private )?(?:lemma|theorem) '+re.escape(name)+r'(?=\s|\{|\()',s)
    if not m: raise SystemExit('not found: '+name)
    a=s.rfind('/--',0,m.start())
    b=s.index('\n/--',m.end())+1
    if a<0: raise SystemExit('missing doc for '+name)
    regions.append(dict(name=name,start=a,end=b,first_line=s.count('\n',0,a)+1,
        last_line=s.count('\n',0,b),source_sha256=hashlib.sha256(s[a:b].encode()).hexdigest()))
regions.sort(key=lambda r:r['start'])
for r1,r2 in zip(regions,regions[1:]):
    assert r1['end']<=r2['start'],(r1,r2)
result=s
for index,r in reversed(list(enumerate(regions))):
    guard=f'section LoopNewSeal{index}\nattribute [local irreducible] '+ ' '.join(defs)+'\n'
    guard+='attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
    close=f'end LoopNewSeal{index}\nattribute [simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n\n'
    result=result[:r['start']]+guard+result[r['start']:r['end']]+close+result[r['end']:]
p=out/(label+'.lean.txt');manifest=out/(label+'.coverage.json')
if p.exists() or manifest.exists(): raise SystemExit('refuse overwrite')
p.write_text(result)
manifest.write_text(json.dumps(dict(source=str(source),source_sha256=hashlib.sha256(s.encode()).hexdigest(),
    sealed_definitions=defs,default_simp_removed=['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],
    regions=regions,probe_sha256=hashlib.sha256(result.encode()).hexdigest()),indent=2)+'\n')
print(json.dumps(dict(probe=str(p),definitions=len(defs),regions=[r['name'] for r in regions]),indent=2))
