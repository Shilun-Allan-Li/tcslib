#!/usr/bin/env python3
"""Whole-file closure seal of one source file.

Usage: seal_gen.py <worktree> <src.lean (relative)> <out module (relative, no .lean)> [--eval-open]

Writes <worktree>/<out>.lean: a verbatim copy of the source file whose imports are kept, with
`import Lean` added and, right after the imports, a `run_cmd` that makes every TCSlib definition
of the import closure irreducible (`attribute [local irreducible]`) and removes it from the
instance-unfolding set. Excluded: abbreviations (`abbrev` hints: structure projections,
`casesOn`, `noConfusion`, `bitSpec`-style notation) and, with --eval-open, `Complexity.PolyExpr.eval`.
The copy is a new module, so the file's own definitions stay transparent: the whole file must
elaborate while reading every other TCSlib definition only through published lemmas.
"""
import re, sys, os

wt, src, out = sys.argv[1], sys.argv[2], sys.argv[3]
eval_open = '--eval-open' in sys.argv[4:]
text = open(os.path.join(wt, src)).read()
ms = list(re.finditer(r'^import .*\n', text, re.M))
assert ms, 'no imports'
e = ms[-1].end()
head, imports, rest = text[:ms[0].start()], text[ms[0].start():e], text[e:]
excl = '[`Complexity.PolyExpr.eval]' if eval_open else '[]'
label = os.path.basename(out)
harness = f'''/- DLC-SEAL {label}: whole-file closure seal of `{src}`{' (PolyExpr.eval open)' if eval_open else ''}. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := {excl}
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
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
  Lean.logInfo m!"DLC-SEAL {label}: sealed={{sealed.size}} (already irreducible {{already}}) abbrev-excluded={{abbrevs}} excluded={{excluded}}"

'''
os.makedirs(os.path.dirname(os.path.join(wt, out)), exist_ok=True)
open(os.path.join(wt, out + '.lean'), 'w').write(head + 'import Lean\n' + imports + harness + rest)
print(out)
