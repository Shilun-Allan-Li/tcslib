import sys, json
# usage: mkseal2.py <module> <out> <seal list file> <erase names comma ('' for none)> <mode>
#   mode 'seal'    : after each `namespace Turing`, `attribute [local irreducible] <seal list>`; after the
#                    first one also `attribute [-simp] <erase>` (if any) and the TOP controls; before the
#                    last `end Turing` the END controls. A JSON map of inserted lines goes to <out>.map.json.
#   mode 'control' : the module's imports, the control command, and the controls alone, unsealed.
#   mode 'sealedcontrol' : imports, control command, the seal and erasure, the controls alone.
src, out, sealf, erase, mode = sys.argv[1:6]
names = [l.strip() for l in open(sealf, encoding='utf-8') if l.strip()]
erase = [e for e in erase.split(',') if e]
L = open(src, encoding='utf-8').read().split('\n')
last_import = max(i for i, l in enumerate(L) if l.startswith('import '))
ctl_def = r'''
open Lean Meta Elab Command in
/-- Review control: does `rfl` close `c = <c's own definition body>` at default transparency? -/
elab "#rfl_control " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverload id
  let ci ← getConstInfo n
  let some v := ci.value? | throwError "{n}: no value"
  let us := ci.levelParams.map mkLevelParam
  let goal ← mkEq (mkConst n us) (v.instantiateLevelParams ci.levelParams us)
  let mv ← mkFreshExprMVar goal
  try
    mv.mvarId!.refl
    logInfo m!"CONTROL {n}: rfl closes"
  catch _ =>
    logError m!"CONTROL {n}: rfl fails"
'''.split('\n')
simp_ctl = []
if 'Turing.Action.apply' in erase:
    simp_ctl.append('example {k : ℕ} {Γ S : Type} {x : List Γ} (a : Turing.Action k Γ S) (c : Turing.Cfg k Γ S x) : (a.apply c).state = a.state := by simp -- SIMPCONTROL Action.apply')
if 'Turing.Cfg.init' in erase:
    simp_ctl.append('example {k : ℕ} {Γ S : Type} (x : List Γ) (q : S) : (Turing.Cfg.init q x : Turing.Cfg k Γ S x).state = some q := by simp -- SIMPCONTROL Cfg.init')
# structurally recursive definitions do not unfold on a variable (smart unfolding), so their
# meta control never closes; a closed instance that evaluates only by unfolding replaces it
conc = {'Turing.decFixed': 'example : Turing.decFixed [true] = some [false] := rfl -- RFLCONTROL decFixed',
        'Turing.incFixed': 'example : Turing.incFixed [false] = some [true] := rfl -- RFLCONTROL incFixed'}
# the END block repeats only the ledger's 20 sealable definitions (lean caps a run at 100 errors)
LEDGER = {'Turing.' + d for d in ('Cfg.mapState Cfg.liftSymbols MultiTapeTM.runFrom fieldOffset fieldsTape '
    'embedEmitCfg FinTM.bufferTape Action.apply MultiTapeTM.step MultiTapeTM.outputSymbol decFixed incFixed '
    'roundOrbit counterWord scanFold scanKeep Cfg.inputSymbol Cfg.workTapeSymbols moveInputPos Cfg.init').split()}
assert len(LEDGER) == 20
def controls(tag):
    sel = [n for n in names if tag != 'END' or n in LEDGER]
    if tag == 'END': assert len(sel) == 20, sel
    return [f'-- {tag} controls'] + [f'#rfl_control {n}' for n in sel if n not in conc] + [conc[n] for n in sel if n in conc] + simp_ctl
seal = 'attribute [local irreducible] ' + ' '.join(names)
ers = ('attribute [-simp] ' + ' '.join(erase)) if erase else None
if mode == 'seal':
    res, ins = [], []   # ins: (output line number 1-based, original line or None)
    def emit(l, orig): res.append(l); ins.append(orig)
    ns = [i for i, l in enumerate(L) if l == 'namespace Turing']
    ends = [i for i, l in enumerate(L) if l == 'end Turing']
    assert len(ns) == 2 and len(ends) == 2, (ns, ends)
    for i, l in enumerate(L):
        if i == ends[-1]:
            for c in controls('END'): emit(c, None)
        emit(l, i + 1)
        if i == last_import:
            for c in ctl_def: emit(c, None)
        if l == 'namespace Turing':
            emit(seal, None)
            if ers: emit(ers, None)   # simp erasure is scoped too: repeat it in every namespace block
            if i == ns[0]:
                for c in controls('TOP'): emit(c, None)
    open(out, 'w', encoding='utf-8').write('\n'.join(res))
    json.dump(ins, open(out + '.map.json', 'w'))
    print('lines', len(res), 'inserted', sum(1 for x in ins if x is None))
else:
    hdr = L[:last_import + 1] + ctl_def + ['', 'namespace Turing']
    body = []
    if mode == 'sealedcontrol':
        body.append(seal)
        if ers: body.append(ers)
    body += controls('ONLY')
    open(out, 'w', encoding='utf-8').write('\n'.join(hdr + body + ['end Turing', '']))
    print('control lines', len(body))
