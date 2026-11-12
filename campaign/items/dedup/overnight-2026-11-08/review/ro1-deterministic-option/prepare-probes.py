from pathlib import Path
import json,re
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');F=Path('/private/tmp/ab34-ro1-integration');P=A/'native-project'
typebody='''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some ci := env.find? ``Turing.MultiTapeTM.runFrom_one | throwError "API absent"
  let axs ← liftCoreM <| Lean.collectAxioms ``Turing.MultiTapeTM.runFrom_one
  let home := (env.getModuleIdxFor? ``Turing.MultiTapeTM.runFrom_one).map fun i => env.header.moduleNames[i.toNat]!.toString
  logInfo m!"CONST|{(Json.mkObj [("name", toJson ci.name.toString), ("levels", toJson (ci.levelParams.map Name.toString)), ("type", toJson (reprStr ci.type)), ("owner", toJson home), ("axioms", toJson ((axs.qsort Name.lt).toList.map Name.toString))]).compress}"
example {k : ℕ} {Γ S : Type*} {x : List Γ}
    (tm : Turing.MultiTapeTM k Γ S) (c : Turing.Cfg k Γ S x) :
    tm.runFrom c 1 = tm.step c := Turing.MultiTapeTM.runFrom_one tm c
'''
for label,module in [('APITypeCfg','TCSlib.Complexity.TuringMachine.CfgFacts'),('APITypeDet','TCSlib.Complexity.TuringMachine.Deterministic')]:
 s='import '+module+'\nimport Lean\nset_option maxHeartbeats 0\n'+typebody
 (A/(label+'.lean.txt')).write_text(s);(P/(label+'.lean')).write_text(s)
inv=json.loads((F/'api-seal-inventory.json').read_text());guards=inv['guards'];simps=inv['default_simp_definitions_removed_in_both_variants'];base='section RO1AltOpacity\n'+('attribute [-simp] '+' '.join(simps)+'\n' if simps else '');guard='attribute [local irreducible] '+' '.join(guards)+'\n'
s=(P/'TCSlib/Complexity/TuringMachine/Deterministic.lean').read_text();s=s.replace('import TCSlib.Complexity.TuringMachine.Configuration\n','import TCSlib.Complexity.TuringMachine.Configuration\nimport Lean\n')
assert 'import Lean' in s
a=s.index('/-- A one-step run from any configuration');api=(A/'API-Deterministic.lean.txt').read_text();assert s[a:a+len(api)]==api;b=a+len(api)
variants={}
for label in ['Native','Sealed']:
 text=s[:a]+base+(guard if label=='Sealed' else '')+s[a:b]+'end RO1AltOpacity\n'+s[b:];variants[label]=text;(A/('APIScope'+label+'.lean.txt')).write_text(text);(P/('APIScope'+label+'.lean')).write_text(text)
assert variants['Sealed'].replace(guard,'')==variants['Native']
for label in ['Native','Sealed']:
 text=(F/('APIControls'+label+'.lean.txt')).read_text().replace('import TCSlib.Complexity.TuringMachine.StateRenaming','import TCSlib.Complexity.TuringMachine.Deterministic').replace('RO1APIRfl','RO1AltAPIRfl').replace('RO1Opacity','RO1AltOpacity')
 (A/('APIControls'+label+'.lean.txt')).write_text(text);(P/('APIControls'+label+'.lean')).write_text(text)
owners=['TCSlib/Complexity/TuringMachine/Simulation.lean','TCSlib/Complexity/TuringMachine/Encoding.lean','TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean','TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean','TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean','TCSlib/Complexity/TimeHierarchy/ClockMachine.lean']
freeze=json.loads((F/'declaration-freeze.json').read_text());roots=[{'path':'TCSlib/Complexity/TuringMachine/Deterministic.lean','name':'Turing.MultiTapeTM.runFrom_one'},{'path':owners[0],'name':'Turing.bufferedScanCfg_run'}]
for p in owners[1:]:
 r=next(r for r in freeze['changed_proof_roots'] if r['path']==p);roots.append({'path':p,'name':r['name']})
tmpl=(F/'AXCurrent.lean.txt').read_text();tail=tmpl[tmpl.index('open Lean Elab Command'):];begin=tail.index('  let roots : List (String × String) := ');end=tail.index('\n  for (owner, sourceName)',begin)
imports=''.join('import '+p[:-5].replace('/','.')+'\n' for p in [r['path'] for r in roots])+'import Lean\nset_option maxHeartbeats 0\n'
for label,rs in [('AXSmallAlt',roots),('AXSmallBaseline',roots[1:])]:
 payload='['+', '.join('('+json.dumps(r['path'][:-5].replace('/','.'))+', '+json.dumps(r['name'])+')' for r in rs)+']'
 text=imports+tail[:begin]+'  let roots : List (String × String) := '+payload+tail[end:]
 (A/(label+'.lean.txt')).write_text(text);(P/(label+'.lean')).write_text(text)
(A/'planned-small-AX-roots.json').write_text(json.dumps(roots,indent=2)+'\n');(A/'planned-native-owners.json').write_text(json.dumps(['TCSlib/Complexity/TuringMachine/Deterministic.lean']+owners,indent=2)+'\n')
print('Prepared exact type/native contract pair, complete API scopes, fresh controls, and bounded7-root AX probes.')
