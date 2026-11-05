"""Build the E-D seal test (python3 -I mkseal_dz.py <owned.lean> <seal-list.txt> <outdir>).
The sealed variant places, right before the first new declaration (the section header
"/-! ### The diagonalizer's leaf: the one-cell take -/"), `attribute [-simp]` on the four
@[simp] TCSlib definitions and `attribute [local irreducible]` on every listed definition; the
unsealed variant has blank lines there instead (same line numbers). Both end with controls that
log one info line each (CONTROL_PASS / CONTROL_FAIL): an `rfl` delta goal and the first
equation lemma's goal for every sealed definition, and the pointwise `simp` unfolding goal for
the four erased ones (the cont1 review's mkseal3 controls)."""
import os, sys
src, alld, outd = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
marker = "/-! ### The diagonalizer's leaf: the one-cell take -/"
k = L.index(marker)
assert L[-2] == 'end Turing.NTimeDiag' and L[-1] == ''
seal = [l.split()[-1] for l in open(alld, encoding='utf-8') if l.startswith('SEAL ')]
assert len(seal) == len(set(seal))
simpdefs = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg',
            'Turing.NDTM.initCfg']
block = ['-- seal (maximal): every semireducible, non-instance, non-projection, non-matcher TCSlib',
         f'-- definition outside this module ({len(seal)}), and the four @[simp] TCSlib definitions erased',
         'attribute [-simp] ' + ' '.join(simpdefs),
         'attribute [local irreducible]'] + ['  ' + d for d in seal] + ['']
ctl = ['', '-- controls (inside the namespace, so that the local seal applies); each logs one line',
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
 '      let ty ← instantiateForall ty #[]',
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
ctl += [f'#ctl_eqn {d}' for d in seal] + ['']
ctl += [f'#ctl_simp {d}' for d in simpdefs] + ['']
nb = len(block)
sealed = L[:k] + block + L[k:-2] + ctl + L[-2:]
unsealed = L[:k] + [''] * nb + L[k:-2] + ctl + L[-2:]
os.makedirs(outd, exist_ok=True)
for name, b in [('DzSeal_sealed.lean', sealed), ('DzSeal_unsealed.lean', unsealed)]:
    open(os.path.join(outd, name), 'w', encoding='utf-8').write('\n'.join(b))
print('sealed', len(seal), 'definitions; erased', len(simpdefs), '; controls', len(seal), 'rfl +',
      len(seal), 'eqn +', len(simpdefs), 'simp; new code at sealed lines', k + 1 + nb, '-',
      len(L) - 2 + nb)
