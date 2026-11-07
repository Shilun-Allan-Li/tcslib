"""Make an inert prefix proof probe from maintainer-owned source, sealing one section.
The generated input is read before run_probe.py is invoked separately.
"""
from pathlib import Path
import os,re,sys,json,hashlib
out=Path(__file__).resolve().parent;source=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad/TCSlib/Complexity/TuringMachine/Build/Primitives.lean'
text=source.read_text();name=sys.argv[1];label=sys.argv[2]
m=re.search(r'^(?:private )?(?:lemma|theorem|def) '+re.escape(name)+r'\b',text,re.M)
if not m:raise SystemExit('missing declaration')
end=text.find('\n/--',m.end())
if end<0:raise SystemExit('missing next declaration doc delimiter')
start=text.rfind('\n/--',0,m.start())+1
irr='Turing.MultiTapeTM.step Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.initCfg Turing.Cfg.init Turing.Action.apply Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.moveInputPos Turing.FinTM.ComputesInTime Turing.FinTM.ComputesFunInTime Turing.FinTM.Computes Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.spaceUsedByTape Turing.MultiTapeTM.visitedByTapeHead Turing.FinTM.controlAction Turing.FinTM.leftAction Turing.FinTM.rightAction Turing.FinTM.emitAction Turing.FinTM.bufferTape Turing.FinTM.tapeBlocks Turing.FinTM.VirtualTag Turing.FinTM.virtualMove Turing.FinTM.virtualNextTag Turing.pairEncode Turing.pairDecode Turing.dbl Turing.FinTM.constTM Turing.pairDiagTM'
if len(sys.argv) > 3: irr += ' ' + sys.argv[3]
chunk=text[start:end]
sealed='section PrimitivesRepair\nattribute [local irreducible] '+irr+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'+chunk+'\nend PrimitivesRepair\n'
result=text[:start]+sealed+'\nend Turing.FinTM\n'
p=out/(label+'.lean.txt')
if p.exists():raise SystemExit('immutable attempt exists')
p.write_text(result)
print(label,'prefix source lines',text[:end].count('\n')+1,'probe bytes',len(result.encode()),'target',name)
