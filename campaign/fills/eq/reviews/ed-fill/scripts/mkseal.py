"""Build the reviewer's sealed and unsealed copies of the head file.
usage: python3 -I mkseal.py <head.lean> <sealgen.out> <outdir>
The seal (attribute [local irreducible] on every name of the generator's SEAL list, attribute [-simp]
on its SIMPU list) goes right before the first new declaration's section heading; the control block
(one logged line per control, so no error cap) goes right before `end Turing.NTimeDiag`. The
unsealed copy has the same pre-realization and control blocks and no seal."""
import sys, os
head, gen, outdir = sys.argv[1:4]
src = open(head, encoding='utf-8').read()
lines = open(gen, encoding='utf-8').read().split('\n')
def block(tag):
    out = []; on = False
    for l in lines:
        if l in ('SEAL', 'SIMPU', 'SKIP'):
            on = (l == tag); continue
        if on and '\t' in l: out.append(l.split('\t')[0])
    return out
seal = block('SEAL'); simpu = block('SIMPU')
assert len(seal) == 350 and len(simpu) == 4, (len(seal), len(simpu))
anchor = "/-! ### The diagonalizer's leaf: the one-cell take -/"
assert src.count(anchor) == 1
endl = "\nend Turing.NTimeDiag\n"
assert src.count(endl) == 1 and src.endswith(endl)
def ids(ns): return ' '.join('_root_.' + n for n in ns)
meta = r'''
open Lean Meta Elab Term Command in
/-- reviewer: realize the equation lemmas of the controlled definitions (before any seal). -/
elab "#rv_realize " xs:ident* : command => do
  for x in xs do
    let n := x.getId.replacePrefix `_root_ .anonymous
    let _ ← liftTermElabM (getEqnsFor? n)
    pure ()

open Lean Meta Elab Term Command in
/-- reviewer: try `intros; exact rfl` on a goal. -/
def rvTryRfl (ty : Expr) : TermElabM Bool := do
  let mv ← mkFreshExprMVar ty
  try
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| (intros; exact rfl))))
    pure gs.isEmpty
  catch _ => pure false

open Lean Meta Elab Term Command in
/-- reviewer: the delta control `∀ xs, c xs = value xs` of a definition. -/
def rvDelta (n : Name) : TermElabM String := do
  let ci ← getConstInfo n
  let us := ci.levelParams.map mkLevelParam
  match ci.value? with
  | none => pure "noval"
  | some v =>
    let ty ← forallTelescope ci.type fun as _ => do
      let lhs := mkAppN (mkConst n us) as
      let rhs := (v.instantiateLevelParams ci.levelParams us).beta as
      mkForallFVars as (← mkEq lhs rhs)
    let ok ← rvTryRfl ty
    pure (if ok then "pass" else "fail")

open Lean Meta Elab Term Command in
/-- reviewer: the first-equation control of a definition (its equation realized before the seal). -/
def rvEqn (n : Name) : TermElabM String := do
  let es? ← getEqnsFor? n
  match es? with
  | none => pure "none"
  | some es =>
    match es[0]? with
    | none => pure "none"
    | some e0 =>
      let e ← getConstInfo e0
      let ok ← rvTryRfl (e.type.instantiateLevelParams e.levelParams
        (e.levelParams.map mkLevelParam))
      pure (if ok then "pass" else "fail")

open Lean Meta Elab Term Command in
/-- reviewer: one logged line per controlled definition. -/
elab "#rv_ctl " xs:ident* : command => do
  for x in xs do
    let n := x.getId.replacePrefix `_root_ .anonymous
    let d ← liftTermElabM (rvDelta n)
    let q ← liftTermElabM (rvEqn n)
    logInfo m!"CTL {n} delta={d} eqn={q}"

open Lean Meta Elab Term Command in
/-- reviewer: the simp control for a `@[simp]` definition: its delta goal tried by `intros; simp`. -/
elab "#rv_simpctl " xs:ident* : command => do
  for x in xs do
    let n := x.getId.replacePrefix `_root_ .anonymous
    let r ← liftTermElabM do
      let ci ← getConstInfo n
      let us := ci.levelParams.map mkLevelParam
      let some v := ci.value? | pure "noval"
      let ty ← forallTelescope ci.type fun as _ => do
        mkForallFVars as (← mkEq (mkAppN (mkConst n us) as)
          ((v.instantiateLevelParams ci.levelParams us).beta as))
      let mv ← mkFreshExprMVar ty
      let ok ← try
          let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| (intros; simp))))
          pure gs.isEmpty
        catch _ => pure false
      pure (if ok then "pass" else "fail")
    logInfo m!"SIMPCTL {n} {r}"
'''
def chunks(ns, k=20):
    for i in range(0, len(ns), k): yield ns[i:i+k]
realize = '\n'.join('#rv_realize ' + ids(c) for c in chunks(seal)) + '\n'
sealblk = ('-- reviewer seal: ' + str(len(seal)) + ' definitions, ' + str(len(simpu)) + ' simp erasures\n' +
           '\n'.join('attribute [local irreducible] ' + ids(c) for c in chunks(seal)) + '\n' +
           'attribute [-simp] ' + ids(simpu) + '\n\n')
ctl = ('\n-- reviewer controls\n' + '\n'.join('#rv_ctl ' + ids(c) for c in chunks(seal)) + '\n' +
       '#rv_simpctl ' + ids(simpu) + '\n')
pre, post = src.split(anchor)
body, _ = post.rsplit(endl, 1)
for name, s in (('sealed', sealblk), ('unsealed', '')):
    out = pre + meta + '\n' + realize + '\n' + s + anchor + body + '\n' + ctl + endl
    os.makedirs(outdir, exist_ok=True)
    open(os.path.join(outdir, f'NTimeDiagonalizer_{name}.lean'), 'w', encoding='utf-8').write(out)
    print(name, 'lines', out.count('\n'))
# record where the seal sits
print('seal before head line', src[:src.index(anchor)].count('\n') + 1)
