# The review's mkseal.py with its anchor found rather than fixed (gate 95).
# mkseal.py <head module> <seal candidates (audit output)> <brief NFSealDefs.txt> <outdir>
# My maximal seal: every semireducible TCSlib definition imported at the module that is not a
# projection, matcher, auxiliary recursor, other file's private, or compiler auxiliary
# (_sizeOf_*, *._flat_ctor, *._sunfold, *._unsafe_rec); instances included.
import sys, re
mod, candf, brieff, outd = sys.argv[1:5]
L = open(mod, encoding='utf-8').read().split('\n')
K = next(i for i in range(690, 720) if L[i] == 'section' and L[i - 1] == '')  # the continuation's section
# (one line lower than the review's land file: the landing adds the CfgFacts import)
cand = []
for l in open(candf, encoding='utf-8'):
    l = l.strip()
    if not l: continue
    n, inst = l.split()
    if re.search(r'(_sizeOf_\d+|_sizeOf_inst|\._flat_ctor|\._sunfold|\._unsafe_rec)$', n): continue
    cand.append((n, inst == 'inst=true'))
brief = [l.strip() for l in open(brieff) if l.strip() and not l.startswith('#')]
names = [n for n, _ in cand]
assert set(brief) <= set(names), set(brief) - set(names)
insts = [n for n, i in cand if i]
print('seal size', len(names), '| of which instances', len(insts), '| brief 223 included:', len(brief))
open(outd + '/seal-set.txt', 'w').write('\n'.join(names) + '\n')
block = ['-- ===== review seal (reviewer-written): every other-file TCSlib definition in scope =====']
for i in range(0, len(names), 4):
    block.append('attribute [local irreducible] ' + ' '.join(names[i:i + 4]))
block.append('')
sealed = L[:K] + block + L[K:]
open(outd + '/NFSeal.lean', 'w', encoding='utf-8').write('\n'.join(sealed))
ctl = r'''
-- ===== review controls (reviewer-written) =====
open Lean Elab Command Meta in
elab "#rv_ctl " ids:ident* : command => do
  let mut nR := 0
  let mut nE := 0
  let mut lines : Array String := #[]
  for id in ids do
    let n ← liftCoreM (realizeGlobalConstNoOverload id)
    let ci ← getConstInfo n
    let lvls := ci.levelParams.map mkLevelParam
    let r ← liftTermElabM <| (do
      try isDefEq (mkConst n lvls) ci.value! catch _ => pure false)
    let e ← liftTermElabM <| (do
      try
        match ← getEqnsFor? n with
        | some eqs =>
          if h : 0 < eqs.size then
            let ty := (← getConstInfo eqs[0]).type
            forallTelescope ty fun _ body => do
              match body.eq? with
              | some (_, l, r) => isDefEq l r
              | none => pure false
          else pure false
        | none => pure false
      catch _ => pure false)
    if r then nR := nR + 1
    if e then nE := nE + 1
    lines := lines.push s!"CTL {n} rfl={r} eqn={e}"
  logInfo m!"CONTROLS {ids.size}: rfl closes {nR}, eqn closes {nE}\n{String.intercalate "\n" lines.toList}"
'''
ctl_call = '#rv_ctl ' + ' '.join(names)
uns = L + [ctl, ctl_call, '']
open(outd + '/NFSealCtl_unsealed.lean', 'w', encoding='utf-8').write('\n'.join(uns))
reapply = ['', '-- the seal again, at top level, for the controls']
for i in range(0, len(names), 4):
    reapply.append('attribute [local irreducible] ' + ' '.join(names[i:i + 4]))
sea = sealed + reapply + [ctl, ctl_call, '']
open(outd + '/NFSealCtl_sealed.lean', 'w', encoding='utf-8').write('\n'.join(sea))
print('wrote', outd)
