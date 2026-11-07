"""Prepare bounded component probes; no library sources are changed."""
from pathlib import Path
import json
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
common=json.loads((ROOT/'campaign/fills/mig1/landing/review-certshell/seal-inventory.json').read_text())['definitions'][:19]
extra=['Turing.Cfg.mapState','Turing.seamCompTM','Turing.embedEmitTM','Turing.embedEmitRetTM','Turing.embedEmitCfg',
       'Turing.rulerHostCfg','Turing.StepBlock.forwardLoopCfg','Turing.startupLoopTM','Turing.CodeTM.toFinTM','Turing.pairEncode']
defs=common+extra
guard='attribute [local irreducible] '+' '.join(defs)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
prefix='''import TCSlib.Complexity.SpaceComplexity.Hierarchy
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
'''
(OUT/'guard.txt').write_text(guard)
(OUT/'seal-inventory.json').write_text(json.dumps(dict(definitions=defs,count=len(defs),before_headers=True,default_simp_removed=['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],scope='Only bounded component proof artifacts; no source API/Hierarchy edits.'),indent=2)+'\n')
for file in OUT.glob('*.body.txt'):
    (OUT/(file.name.removesuffix('.body.txt')+'.lean.txt')).write_text(prefix+guard+'\n'+file.read_text())
print('Prepared strict component guard for',len(defs),'ordinary definitions.')
