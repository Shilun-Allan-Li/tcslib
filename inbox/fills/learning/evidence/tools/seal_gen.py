#!/usr/bin/env python3
"""Whole-file closure seal of one source file.

Usage: seal_gen.py <worktree> <src.lean (relative)> <out module (relative, no .lean)>
                   [--eval-open] [--coe-open]

Writes <worktree>/<out>.lean: a verbatim copy of the source file whose imports are kept, with
`import Lean` added and, right after the imports, a `run_cmd` that makes every TCSlib definition
of the import closure irreducible (`attribute [local irreducible]`) and removes it from the
instance-unfolding set. Always excluded (notation, never sealed): reducible abbreviations
(`abbrev` hints: structure projections, `casesOn`, `noConfusion`, `bitSpec`-style notation).
--eval-open also excludes `Complexity.PolyExpr.eval` (variant A; without it, variant B).
--coe-open (the canonical "coe" variant) also excludes the projection coercions: TCSlib instances
of a coercion class (`CoeFun`, `Coe`, `CoeSort`, `CoeOut`, `CoeTail`, `CoeHead`, `CoeTC`,
`CoeHTCT`, `CoeDep`) whose value is the class constructor applied to a structure projection
(such as `FinDist`'s `⟨FinDist.prob⟩`). Without it ("strict"), they are sealed like every other
definition. The run reports the counts (sealed, already irreducible, abbreviation-excluded,
eval-excluded, coercion-excluded with their names).
The copy is a new module, so the file's own definitions stay transparent: the whole file must
elaborate while reading every other TCSlib definition only through published lemmas.
"""
import re, sys, os

wt, src, out = sys.argv[1], sys.argv[2], sys.argv[3]
eval_open = '--eval-open' in sys.argv[4:]
coe_open = '--coe-open' in sys.argv[4:]
text = open(os.path.join(wt, src)).read()
ms = list(re.finditer(r'^import .*\n', text, re.M))
assert ms, 'no imports'
e = ms[-1].end()
head, imports, rest = text[:ms[0].start()], text[ms[0].start():e], text[e:]
excl = '[`Complexity.PolyExpr.eval]' if eval_open else '[]'
coe = 'true' if coe_open else 'false'
label = os.path.basename(out)
variant = ('A (PolyExpr.eval open)' if eval_open else 'B (PolyExpr.eval sealed)') + \
    (', coe (projection coercions open)' if coe_open else ', strict')
harness = f'''/- DLC-SEAL {label}: whole-file closure seal of `{src}`, variant {variant}. -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := {excl}
  let coeOpen : Bool := {coe}
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
          continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {{n}}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {{n}}"
  Lean.logInfo m!"DLC-SEAL {label}: sealed={{sealed.size}} (already irreducible {{already}}) abbrev-excluded={{abbrevs}} excluded={{excluded}} coe-excluded={{coeExcl.size}} {{coeExcl.toList}}"

'''
os.makedirs(os.path.dirname(os.path.join(wt, out)), exist_ok=True)
open(os.path.join(wt, out + '.lean'), 'w').write(head + 'import Lean\n' + imports + harness + rest)
print(out)
