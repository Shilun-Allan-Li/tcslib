"""Build the review's maximal seal of the head module, with non-erroring controls (python3 -I).
Adapted from the E-Q cont1 review's mkseal3.py.  The seal block sits at the top of region (b)
(before `nf_pack`'s docstring, head line 45): `attribute [-simp]` on the four `@[simp]` TCSlib
definitions and `attribute [local irreducible]` on every semireducible, non-instance,
non-projection, non-matcher, non-private TCSlib definition of the environment outside this module
(the audit's ALLDEFS).  The controls sit before `end FinNDTM`, so that the local seal applies;
each logs one info line (`CONTROL_PASS <kind> <name>` or `CONTROL_FAIL <kind> <name>`).  Kinds:
`rfl` (the goal `c = <its value>` by `rfl`), `eqn` (the first equation lemma of `c`, by
`intros; rfl`; only recursive definitions have one) and `simp` (the pointwise unfolding goal of
a `@[simp]` definition, by `intros; simp`).  The unsealed copy replaces the block by blank lines.
usage: python3 -I mkseal.py <head.lean> <alldefs.txt> <outdir>"""
import os, sys
src, alld, outd = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
assert L[42] == 'namespace FinNDTM' and L[43] == '' and L[44].startswith('/-- A finite-state machine'), L[42:45]
assert L[-4] == 'end FinNDTM' and L[-3] == '' and L[-2] == 'end Turing' and L[-1] == '', L[-4:]
seal = [l.strip() for l in open(alld, encoding='utf-8') if l.strip()]
assert len(seal) == len(set(seal)), 'duplicates'
simpdefs = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
assert all(d in seal for d in simpdefs)
block = ['-- review seal (maximal): every semireducible, non-instance, non-projection TCSlib',
         f'-- definition outside this module ({len(seal)}), and the four @[simp] TCSlib definitions erased',
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
body_sealed = L[:44] + block + L[44:-4] + ctl + L[-4:]
body_unsealed = L[:44] + [''] * nb + L[44:-4] + ctl + L[-4:]
os.makedirs(outd, exist_ok=True)
for name, b in [('NFSeal_sealed.lean', body_sealed), ('NFSeal_unsealed.lean', body_unsealed)]:
    open(os.path.join(outd, name), 'w', encoding='utf-8').write('\n'.join(b))
print('sealed', len(seal), 'definitions; erased', len(simpdefs), '; controls', len(seal), 'rfl +', len(seal),
      'eqn +', len(simpdefs), 'simp; module body (new code onward) at sealed lines', 45 + nb, '-', len(L) - 4 + nb)
