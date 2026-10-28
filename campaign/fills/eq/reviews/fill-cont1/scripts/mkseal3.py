"""Build the review's maximal seal of the head module, with non-erroring controls (python3 -I).
As mkseal2.py, but each control catches its own failure and logs one info line
(`CONTROL_PASS <kind> <name>` or `CONTROL_FAIL <kind> <name>`), so that the CLI's cap of 100
errors cannot hide a result.  Kinds: `rfl` (the goal `c = <its value>` by `rfl` at default
transparency), `eqn` (the first equation lemma's statement of `c`, by `intros; rfl`: for the
recursive definitions, whose generic delta goal does not close even unsealed) and `simp` (the
pointwise unfolding goal of a `@[simp]` definition, by `intros; simp`).
usage: python3 -I mkseal3.py <head.lean> <alldefs.txt> <outdir>"""
import os, sys
src, alld, outd = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
assert L[374] == '' and L[375].startswith('/-- The next rung'), (L[374], L[375][:30])
assert L[-2] == 'end Turing.NTimeDiag' and L[-1] == ''
seal = [l.strip() for l in open(alld, encoding='utf-8') if l.strip()]
assert len(seal) == 275 and len(set(seal)) == 275
simpdefs = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
rec = ['Turing.FinTM.sweepFold', 'Turing.NDTM.runWith', 'Turing.codeReadUnary', 'Turing.codeReadVec',
       'Turing.codeSkipRepeat', 'Turing.decFixed', 'Turing.incFixed', 'Turing.mealyRun',
       'Turing.pairDecode', 'Turing.unaryTokenSplit']
assert all(d in seal for d in simpdefs + rec)
block = ['-- review seal (maximal): every semireducible, non-instance, non-projection TCSlib',
         '-- definition outside this module (275), and the four @[simp] TCSlib definitions erased',
         'attribute [-simp] ' + ' '.join(simpdefs),
         'attribute [local irreducible]'] + ['  ' + d for d in seal] + ['']
ctl = ['', '-- controls (inside the namespace, so that the local seal applies); each logs one info line',
       'open Lean Elab Command Meta in',
       'elab "#ctl_rfl " id:ident : command => do',
       '  let n ← liftCoreM (realizeGlobalConstNoOverload id)',
       '  let ci ← getConstInfo n',
       '  let some value := ci.value? | throwError "not a definition: {n}"',
       '  let ok ← liftTermElabM do',
       '    try',
       '      Term.withoutErrToSorry do',
       '        let goal ← mkEq (mkConst n (ci.levelParams.map Level.param)) value',
       '        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal',
       '        Term.synthesizeSyntheticMVarsNoPostponing',
       '        return !(← instantiateMVars proof).hasSorry',
       '    catch _ => return false',
       '  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} rfl {n}"', '',
       'open Lean Elab Command Meta in',
       'elab "#ctl_eqn " id:ident : command => do',
       '  let n ← liftCoreM (realizeGlobalConstNoOverload id)',
       '  let ok ← liftTermElabM do',
       '    try',
       '      let some eqs ← getEqnsFor? n | return false',
       '      let ty := (← getConstInfo eqs[0]!).type',
       '      let ty ← instantiateForall ty #[] ',
       '      Term.withoutErrToSorry do',
       '        let proof ← Term.elabTermEnsuringType (← `(by intros; rfl)) ty',
       '        Term.synthesizeSyntheticMVarsNoPostponing',
       '        return !(← instantiateMVars proof).hasSorry',
       '    catch _ => return false',
       '  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} eqn {n}"', '',
       'open Lean Elab Command Meta in',
       'elab "#ctl_simp " id:ident : command => do',
       '  let n ← liftCoreM (realizeGlobalConstNoOverload id)',
       '  let ci ← getConstInfo n',
       '  let some value := ci.value? | throwError "not a definition: {n}"',
       '  let ok ← liftTermElabM do',
       '    try',
       '      Term.withoutErrToSorry do',
       '        let c := mkConst n (ci.levelParams.map Level.param)',
       '        let goal ← forallTelescopeReducing ci.type fun xs _ => do',
       '          mkForallFVars xs (← mkEq (mkAppN c xs) (mkAppN value xs).headBeta)',
       '        let proof ← Term.elabTermEnsuringType (← `(by intros; simp)) goal',
       '        Term.synthesizeSyntheticMVarsNoPostponing',
       '        return !(← instantiateMVars proof).hasSorry',
       '    catch _ => return false',
       '  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} simp {n}"', '']
ctl += [f'#ctl_rfl {d}' for d in seal] + ['']
ctl += [f'#ctl_eqn {d}' for d in rec] + ['']
ctl += [f'#ctl_simp {d}' for d in simpdefs] + ['']
nb = len(block)
body_sealed = L[:375] + block + L[375:-2] + ctl + L[-2:]
body_unsealed = L[:375] + [''] * nb + L[375:-2] + ctl + L[-2:]
os.makedirs(outd, exist_ok=True)
for name, b in [('Seal3_sealed.lean', body_sealed), ('Seal3_unsealed.lean', body_unsealed)]:
    open(os.path.join(outd, name), 'w', encoding='utf-8').write('\n'.join(b))
print('sealed', len(seal), 'definitions; erased', len(simpdefs), '; controls', len(seal), 'rfl +', len(rec),
      'eqn +', len(simpdefs), 'simp; module body (new code onward) at sealed lines', 376 + nb, '-', len(L) - 3 + nb)
