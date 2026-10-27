"""Build the review's seal of the head module (python3 -I).
Writes <outdir>/EQSeal_sealed.lean (attribute block at the top of region (b), controls at the end of
the namespace), EQSeal_unsealed.lean (the same without the attribute block), and
EQSeal_singleton.lean (sealed, plus the core `List.singleton` made irreducible, an experiment).
usage: python3 -I mkseal.py <NTimeDiagonalizer.lean> <worker seal-definitions.txt> <outdir>"""
import os, sys
src, wlist, outd = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
assert L[254] == '' and L[255].startswith('/-- The query '), (L[254], L[255][:30])
assert L[-2] == 'end Turing.NTimeDiag' and L[-1] == ''
worker = [l.strip() for l in open(wlist, encoding='utf-8') if l.strip()]
assert len(worker) == 29
simpdefs = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
seal = worker + [d for d in simpdefs if d not in worker]
assert len(seal) == 32
reached = ['Complexity.TimeConstructible', 'Turing.FinTM.ComputesFunInTime', 'Turing.FinTM.ComputesInTime', 'Turing.incFixed']
assert all(r in seal for r in reached)
block = ['', '-- review seal: every other-file TCSlib definition the new code reaches (4), the worker\'s 29,',
         '-- and the four @[simp] TCSlib definitions of the environment, erased from simp', '',
         'attribute [-simp] ' + ' '.join(simpdefs), '', 'attribute [local irreducible]'] + ['  ' + d for d in seal] + ['']
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
ctl += ['-- usage-shaped controls for the four reached definitions',
        'example (M : Turing.FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)',
        '    (h : M.ComputesFunInTime f T) (x : List Bool) : M.ComputesInTime x (f x) (T x.length) :=',
        '  h x',
        'example (M : Turing.FinTM Bool) (x w : List Bool) (t : ℕ) (h : M.ComputesInTime x w t) :',
        '    ∃ s, M.tm.ComputesInTimeAndSpace x w t s := h',
        'example (T : ℕ → ℕ) (h : Complexity.TimeConstructible T) : ∀ n, n ≤ T n := h.1',
        'example : Turing.incFixed [false, true] = some [true, true] := rfl', '']
body_sealed = L[:255] + block + L[255:-2] + ctl + L[-2:]
body_unsealed = L[:255] + [''] * len(block) + L[255:-2] + ctl + L[-2:]
blk2 = block[:-1] + ['  List.singleton', '']
body_single = L[:255] + blk2 + L[255:-2] + L[-2:]
os.makedirs(outd, exist_ok=True)
for name, b in [('EQSeal_sealed.lean', body_sealed), ('EQSeal_unsealed.lean', body_unsealed), ('EQSeal_singleton.lean', body_single)]:
    open(os.path.join(outd, name), 'w', encoding='utf-8').write('\n'.join(b))
print('sealed', len(seal), 'definitions; erased', len(simpdefs), '; controls', len(seal) + len(simpdefs) + 4,
      '; region (b) starts at sealed line', 256 + len(block), '; new code ends at line', 453 + len(block))
