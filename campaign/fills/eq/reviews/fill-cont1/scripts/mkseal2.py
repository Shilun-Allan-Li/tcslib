"""Build the review's maximal seal of the head module (python3 -I).
Writes <outdir>/Seal_sealed.lean (attribute block before the first new private, controls at the
end of the namespace) and Seal_unsealed.lean (the same with the attribute block blanked, so line
numbers agree).  The seal: `attribute [local irreducible]` on every TCSlib definition of the
environment outside this module that is semireducible, not an instance, not a projection and not
a matcher (the audit's ALLDEFS list), and `attribute [-simp]` on the environment's four `@[simp]`
TCSlib definitions.
usage: python3 -I mkseal2.py <head.lean> <alldefs.txt> <outdir>"""
import os, sys
src, alld, outd = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
assert L[374] == '' and L[375].startswith('/-- The next rung'), (L[374], L[375][:30])
assert L[-2] == 'end Turing.NTimeDiag' and L[-1] == ''
seal = [l.strip() for l in open(alld, encoding='utf-8') if l.strip()]
assert len(seal) == 275 and len(set(seal)) == 275
simpdefs = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
assert all(d in seal for d in simpdefs)
block = ['-- review seal (maximal): every semireducible, non-instance, non-projection TCSlib',
         '-- definition outside this module (275), and the four @[simp] TCSlib definitions erased',
         'attribute [-simp] ' + ' '.join(simpdefs),
         'attribute [local irreducible]'] + ['  ' + d for d in seal] + ['']
ctl = ['', '-- controls (inside the namespace, so that the local seal applies): each must fail sealed and',
       '-- close unsealed', 'open Lean Elab Command Meta in',
       'elab "#rfl_control " id:ident : command => do',
       '  let n ← liftCoreM (realizeGlobalConstNoOverload id)',
       '  let ci ← getConstInfo n',
       '  let some value := ci.value? | throwError "not a definition: {n}"',
       '  liftTermElabM do',
       '    let goal ← mkEq (mkConst n (ci.levelParams.map Level.param)) value',
       '    let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal',
       '    Term.synthesizeSyntheticMVarsNoPostponing',
       '    if (← instantiateMVars proof).hasSorry then throwError "control admits: {n}"',
       '    logInfo m!"RFL_CONTROL_PASS {n}"', '',
       'open Lean Elab Command Meta in',
       'elab "#simp_control " id:ident : command => do',
       '  let n ← liftCoreM (realizeGlobalConstNoOverload id)',
       '  let ci ← getConstInfo n',
       '  let some value := ci.value? | throwError "not a definition: {n}"',
       '  liftTermElabM do',
       '    let c := mkConst n (ci.levelParams.map Level.param)',
       '    let goal ← forallTelescopeReducing ci.type fun xs _ => do',
       '      mkForallFVars xs (← mkEq (mkAppN c xs) (mkAppN value xs).headBeta)',
       '    let proof ← Term.elabTermEnsuringType (← `(by intros; simp)) goal',
       '    Term.synthesizeSyntheticMVarsNoPostponing',
       '    if (← instantiateMVars proof).hasSorry then throwError "control admits: {n}"',
       '    logInfo m!"SIMP_CONTROL_PASS {n}"', '']
ctl += [f'#rfl_control {d}' for d in seal] + ['']
ctl += [f'#simp_control {d}' for d in simpdefs] + ['']
nb = len(block)
body_sealed = L[:375] + block + L[375:-2] + ctl + L[-2:]
body_unsealed = L[:375] + [''] * nb + L[375:-2] + ctl + L[-2:]
os.makedirs(outd, exist_ok=True)
for name, b in [('Seal_sealed.lean', body_sealed), ('Seal_unsealed.lean', body_unsealed)]:
    open(os.path.join(outd, name), 'w', encoding='utf-8').write('\n'.join(b))
first = 376 + nb
last = len(L) - 2 + nb  # the head's 'end' line, shifted
print('sealed', len(seal), 'definitions; erased', len(simpdefs), '; controls', len(seal) + len(simpdefs),
      '; module body (new code onward) at sealed lines', first, '-', last - 1)
