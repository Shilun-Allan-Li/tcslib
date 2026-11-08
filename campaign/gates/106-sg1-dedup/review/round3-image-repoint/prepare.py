from pathlib import Path
import json,hashlib,re,subprocess,datetime,difflib
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
O=R/'campaign/gates/106-sg1-dedup/review/round3-image-repoint'
S=Path('/private/tmp/tcslib-g106-image-ff7rmon8')
assert not O.exists(), 'new folder required'
O.mkdir(parents=True)
source=W/'TCSlib/Complexity/ClassNP/Tautology.lean'
b=source.read_bytes();text=b.decode();head=subprocess.check_output(['git','-C',str(W),'rev-parse','HEAD']).decode().strip()
assert head=='63a3ce018e96c8c114b9c82f8d5fce6021c7d03c'
assert subprocess.check_output(['git','-C',str(W),'status','--porcelain'])==b''
decl=text.index('private lemma taut_comp_on_image ')
start=text.rfind('/--',0,decl);end=text.index('/-- The verifier is polynomial-time:',decl)
old=text[start:end]
header=text[decl:text.index(':= by',decl)+5]
doc='''/-- Quantitative buffered composition with a second-stage contract only on
the actual first-stage image.

**Proof sketch.** Apply the public image-composition theorem with the two
given machine contracts and their original-input time budgets. -/
'''
chunk=doc+header+'\n  exact FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU\n\n'
after=text[:start]+chunk+text[end:]
assert after.count(header)==1
assert after[:start]==text[:start] and after[start+len(chunk):]==text[end:]
imports='\n'.join(re.findall(r'^import .*$',text,re.M))+'\n'
names=(R/'campaign/gates/106-sg1-dedup/review/round3-pair-bound-applied/guard-definitions.txt').read_text().splitlines()[:14]
assert len(names)==14 and names[-1]=='Turing.MultiTapeTM.visitedByTapeHead'
guard='section G106ImageSeal\nattribute [local irreducible] '+' '.join(names)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n\n'
tail='end G106ImageSeal\n\n'
meta='''

open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let kenv := env.toKernelEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    match n with
    | .str _ "taut_comp_on_image" =>
      if (env.getModuleIdxFor? n).isNone then roots := roots.push n
    | _ => pure ()
  unless roots.size == 1 do throwError "root count mismatch {roots.size}"
  let kind := fun (ci : ConstantInfo) => match ci with
    | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"
  for n in roots do
    unless isPrivateName n do throwError "root unexpectedly public {n}"
    logInfo m!"ROOT|{n}|private={isPrivateName n}"
  for (n, _) in env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    unless roots.any (fun root => root.isPrefixOf n) do continue
    let some ci := kenv.find? n | throwError "missing actual constant {n}"
    let ax ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"PROOFAX|{n}|kind={kind ci}|{(ax.qsort Name.lt).toList}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut seen : Array Name := #[]
    for usedName in used do
      if seen.contains usedName then continue
      seen := seen.push usedName
      match env.getModuleIdxFor? usedName, kenv.find? usedName with
      | some idx, some usedInfo =>
        let owner := env.header.moduleNames[idx.toNat]!
        if (`TCSlib).isPrefixOf owner then
          logInfo m!"CITED|{n}|{usedName}|{owner}|kind={kind usedInfo}|private={isPrivateName usedName}"
          if let .defnInfo d := usedInfo then
            let hint := match d.hints with
              | .regular _ => "regular" | .abbrev => "abbrev" | .opaque => "opaque"
            logInfo m!"FOREIGNDEF|{n}|{usedName}|{owner}|hints={hint}"
      | none, some (.defnInfo _) => logInfo m!"HOMEDEF|{n}|{usedName}"
      | _, _ => pure ()
'''
hyp=imports+'set_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\nnamespace Complexity\nopen Turing\n\n'+chunk+'end Complexity\n'
hypSeal=imports+'set_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\nnamespace Complexity\nopen Turing\n\n'+guard+chunk+tail+'end Complexity\n'
files={'Tautology-before.lean.txt':b,'Tautology-proposed.lean.txt':after.encode(),'target-before.lean.txt':old.encode(),'target-after.lean.txt':chunk.encode(),'full-header.lean.txt':header.encode(),'Hypothetical-native-v1.lean.txt':(hyp+meta).encode(),'Hypothetical-sealed-v1.lean.txt':(hypSeal+meta).encode(),'metadata-append.lean.txt':meta.encode(),'imports.lean.txt':imports.encode(),'guard-definitions.txt':('\n'.join(names)+'\n').encode(),'source.patch':''.join(difflib.unified_diff(text.splitlines(True),after.splitlines(True),fromfile='a/TCSlib/Complexity/ClassNP/Tautology.lean',tofile='b/TCSlib/Complexity/ClassNP/Tautology.lean')).encode()}
for name,data in files.items(): (O/name).write_bytes(data)
pins={}
for rel in ['TCSlib/Complexity/ClassNP/Tautology.lean','TCSlib/Complexity/ClassNP/SAT.lean','TCSlib/Complexity/CookLevin/Hardness.lean','TCSlib/Complexity/TuringMachine/Composition.lean','lean-toolchain']:
 d=(W/rel).read_bytes();pins[rel]={'bytes':len(d),'sha256':hashlib.sha256(d).hexdigest()}
assert pins['TCSlib/Complexity/CookLevin/Hardness.lean']['sha256']=='3c41a6aca1ed4e24b08330b7819a4d36ce0e695be4a71b11382c346e39499952'
assert pins['TCSlib/Complexity/ClassNP/SAT.lean']['sha256']=='682df0cd83abed16dac1e44768bee40a1691030eaeab1cf56373fa0677dbc6ba'
context={'source_head_at_preparation':head,'worktree':str(W),'snapshot':'/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-msg6','records':str(R),'scratch':str(S),'source_pins':pins,'proposed_sha256':hashlib.sha256(after.encode()).hexdigest(),'source_unmodified_at_preparation':True,'dependency_correction':'Tautology explicitly imports CookLevin.Hardness at line10. MSG5 was previously suggested as identical dependencies; MSG6 is used now, after root confirmed its complete26-module chain PASS, for exact current context.','scope':'One private proof body and adjacent accurate sketch only; no imports, headers, executable definitions, attributes, order or other-source changes.'}
(O/'context.json').write_text(json.dumps(context,indent=2)+'\n')
(O/'preparation-attempts.json').write_text(json.dumps({'read_only_failed_path_guesses':['TCSlib/Complexity/Tautology.lean','TCSlib/Complexity/TuringMachine/Build/Composition.lean'],'correct_homes':['TCSlib/Complexity/ClassNP/Tautology.lean','TCSlib/Complexity/TuringMachine/Composition.lean'],'no_Lean_or_source_mutation_in_failed_reads':True},indent=2)+'\n')
oldControl=(R/'campaign/gates/106-sg1-dedup/review/round3-pair-bound-applied/Controls-unsealed-v1.lean.txt').read_text()
body=oldControl[oldControl.index('/-! Kernel-checked'):]
a=body.index('  let names : List Name := [');z=body.index('  let mut index :=',a)
body=body[:a]+'  let names : List Name := ['+',\n    '.join('`'+n for n in names)+']\n'+body[z:]
body=body.replace('#g106_prefix_controls','#g106_image_controls').replace('G106PrefixRflControl_','G106ImageRflControl_')
assert body.count('#g106_image_controls')==2
controls=imports+'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'+body
(O/'Controls-unsealed-v1.lean.txt').write_text(controls)
(O/'Controls-sealed-v1.lean.txt').write_text(imports+'attribute [local irreducible] '+' '.join(names)+'\n'+controls[len(imports):])
(O/'control-definitions.txt').write_text('\n'.join(names)+'\n')
(O/'check-controls.py').write_bytes((R/'campaign/gates/106-sg1-dedup/review/round3-pair-bound-applied/check-controls.py').read_bytes())
(O/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(context,indent=2))
