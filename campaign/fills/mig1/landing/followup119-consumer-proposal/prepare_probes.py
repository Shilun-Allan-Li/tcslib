from pathlib import Path
import json
out=Path(__file__).resolve().parent;root=out.parents[4]
pre='''import TCSlib.Complexity.TuringMachine.Build.Primitives
set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace MIGFollowup119ConsumerCheck
open Turing Turing.FinTM
'''
names=['Turing.MultiTapeTM.step','Turing.MultiTapeTM.runFrom','Turing.MultiTapeTM.initCfg','Turing.MultiTapeTM.spaceUsed','Turing.Cfg.init','Turing.pairDiagTM','Turing.FinTM.incFixedTM']
guard='attribute [local irreducible] '+' '.join(names)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
body=''
for owner,name in [('Loop','emCall_first_entry'),('Primitives','catalogFirstEntry'),('Primitives','emitter_first_entry')]:body+=(out/'inputs'/(owner+'-'+name+'-after.lean.txt')).read_text()
body+='''private lemma pairDup_zero_space_leaf (x : List Bool) (t : ℕ) :
    pairDiagTM.tm.spaceUsed (pairDiagTM.tm.initCfg x) t ≤ 6 := by
  rw [Turing.pairDiagTM_spaceUsed]
  omega

private lemma incFixed_zero_space_leaf (x : List Bool) (t : ℕ) :
    incFixedTM.tm.spaceUsed (incFixedTM.tm.initCfg x) t ≤ 3 := by
  rw [Turing.FinTM.incFixedTM_spaceUsed]
  omega

#print axioms emCall_first_entry
#print axioms catalogFirstEntry
#print axioms emitter_first_entry
#print axioms pairDup_zero_space_leaf
#print axioms incFixed_zero_space_leaf
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [``emCall_first_entry, ``catalogFirstEntry, ``emitter_first_entry,
    ``pairDup_zero_space_leaf, ``incFixed_zero_space_leaf]
  for (n, ci) in env.constants.toList do
    if !(roots.any (fun r => r.isPrefixOf n)) then continue
    let ax ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"AX|{n}|{(ax.qsort Name.lt).toList}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut seen : Array Name := #[]
    for d in used do
      if seen.contains d then continue
      seen := seen.push d
      match env.getModuleIdxFor? d, env.find? d with
      | some i, some (.defnInfo di) =>
        let home := env.header.moduleNames[i.toNat]!
        if (`TCSlib).isPrefixOf home then
          let hint := match di.hints with
            | .abbrev => "abbrev" | .opaque => "opaque" | .regular _ => "regular"
          logInfo m!"DEF|{n}|{d}|{home}|{hint}"
      | _, _ => pure ()

end MIGFollowup119ConsumerCheck
'''
(out/'Consumers-native.lean.txt').write_text(pre+body);(out/'Consumers-sealed.lean.txt').write_text(pre+guard+'\n'+body);(out/'guard.txt').write_text(guard)
# Reuse the reviewed maintainer-owned native control generator as source text only;
# no generator file is executed. Limit its explicit list to the seven proposed guards.
s=(root/'campaign/gates/119-mig1-followup-api/review/pair-diag/Controls-unsealed-v1.lean.txt').read_text();s=s[s.index('open Lean Elab Command Meta in\nelab "#g119_pair_diag_controls"'):]
a=s.index('  let names : List Name :=');b=s.index('  let mut index :=',a);s=s[:a]+'  let names : List Name := ['+',\n    '.join('`'+n for n in names)+']\n'+s[b:];s=s.replace('#g119_pair_diag_controls','#mig119_consumer_controls').replace('G119PairDiagRflControl_','MIG119ConsumerRflControl_')
cp='import TCSlib.Complexity.TuringMachine.Build.Primitives\nset_option maxHeartbeats 0\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n'
common='attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
(out/'Controls-native.lean.txt').write_text(cp+common+s);(out/'Controls-sealed.lean.txt').write_text(cp+guard+s)
(out/'probe-scope.json').write_text(json.dumps({'three_forwarded_private_headers_exact_from_MIG':True,'catalog_tests':'Only two new zero-space leaves, not full computation/existential rows','actual_API_consumption':'Imports stable whole preflight Primitives including119Finite/Encoding/Wrappers; no hypothetical API premise','guard_definitions':names,'native_vs_sealed':'Same complete five proof blocks; guard before all headers; default3 removals explicit in sealed version','control_modes':['pointwise data projection/delta','abstracted complete defining-function equation'],'controls_expected':14,'no_new_production_declaration_or_source_compilation':True,'no_full_proposed_MIG_module_or12module_replay':True},indent=2)+'\n')
print((pre+guard+'\n'+body)[:4300]);print('CONTROLS_GENERATOR\n'+(cp+guard+s))
