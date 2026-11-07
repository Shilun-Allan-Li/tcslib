"""Factor exactly one reviewed call-bank proof through existing public field equations."""
from pathlib import Path
import hashlib
import json
import os
import re
import sys
out=Path(__file__).resolve().parent
name=sys.argv[1]
if name not in ('emCall_bank_initial','emCall_bank_final'): raise SystemExit('wrong proof')
p=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad/TCSlib/Complexity/TuringMachine/Build/Loop.lean'
s=p.read_text();a=s.index('private lemma '+name+' ');b=s.index('\n/--',a);t=s[a:b]
before=t
pattern=re.compile(r'\(\(embedEmitTM_frame \(emCallTripleEmbedding M i\) emCallClearTM\.tm _ _ \[\] _ 0\)\.1 \((emCallPairIndex M [01]|emCallTripleIndex M l r)\)\s+\(by rintro ⟨r\x27, hr⟩.*?cases h\)\)\.([12])',re.S)
counts={'pair':0,'triple':0}
def replace(m):
    assert m.group(0).count('embedEmitTM_frame')==1
    index,field=m.groups()
    if index.startswith('emCallPairIndex'):
        r=index[-1]
        proof=f'emCall_pair_not_mem M i {r}'
        counts['pair']+=1
    else:
        proof='emCall_triple_not_mem M i l r he'
        counts['triple']+=1
    return f'(embedEmitCfg_unselected (emCallTripleEmbedding M i) _ _ [] _\n            ({index}) ({proof})).{field}'
t,n=pattern.subn(replace,t)
assert n==6 and counts=={'pair':4,'triple':2},counts
old='simp only [emCallEmbeddedCfg, Cfg.mapState]'
assert t.count(old)==2
t=t.replace(old,'simp only [emCallEmbeddedCfg, Cfg.mapState_workTapes]',1)
t=t.replace(old,'simp only [emCallEmbeddedCfg, Cfg.mapState_workTapePos]',1)
old='''  refine Cfg.ext rfl rfl ?_ ?_ rfl
'''
new='''  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp only [emCallEmbeddedCfg, Cfg.mapState_state, embedEmitCfg_state,
      emCallClearCfg, emCallBankFrame, emCallFrame, Option.map_some]
  · simp only [emCallEmbeddedCfg, Cfg.mapState_inputPos, embedEmitCfg_inputPos,
      emCallClearCfg, emCallBankFrame, emCallFrame]
'''
assert t.count(old)==1
t=t.replace(old,new)
t+='''  · simp only [emCallEmbeddedCfg, Cfg.mapState_output, embedEmitCfg_output,
      emCallClearCfg, emCallBankFrame, emCallFrame, List.nil_append]
'''
assert 'by rintro' not in t and 'embedEmitTM_frame' not in t
(out/(name+'-before.lean.txt')).write_text(before)
(out/(name+'-after-factor.lean.txt')).write_text(t)
(out/(name+'-factor.json')).write_text(json.dumps(dict(name=name,sites=counts,
    before_sha256=hashlib.sha256(before.encode()).hexdigest(),after_sha256=hashlib.sha256(t.encode()).hexdigest()),indent=2)+'\n')
p.write_text(s[:a]+t+s[b:])
print(json.dumps(dict(name=name,replacements=n,sites=counts),indent=2))
