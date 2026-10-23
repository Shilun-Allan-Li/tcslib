import sys, re
# usage: mkax.py <module file> <out file> <names comma-separated> <targets comma-separated>
src, out, names, targets = sys.argv[1], sys.argv[2], sys.argv[3].split(','), sys.argv[4].split(',')
text = open(src, encoding='utf-8').read()
lines = text.split('\n')
last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
lines.insert(last_import + 1, 'import Lean.Util.FoldConsts')
tail = r'''
open Lean Elab Command in
/-- Every constant in the dependency closure of `root` whose own type or value mentions
`sorryAx` (maintainer's read-only admission walk). -/
def rvc2SorrySourcesOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut srcs : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      let used := ci.getUsedConstantsAsSet
      if used.contains ``sorryAx then srcs := srcs.push c
      for d in used.toList do
        unless visited.contains d do stack := stack.push d
  return srcs

open Lean Elab Command in
elab "#sorry_sources " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  logInfo m!"{n}: direct sorryAx users in closure: {rvc2SorrySourcesOf (← getEnv) n}"

open Lean in
/-- Is `c` an equation/unfolding lemma (`X.eq_N`, `X.eq_def`, `X.eq_unfold`, `X._unfold`,
`X.match_N`) of a constant `X` defined in another module? -/
def rvc2ExtEqn? (env : Environment) (c : Name) : Option Name :=
  match c with
  | .str p s =>
    if (s.startsWith "eq_" || s == "_unfold" || s.startsWith "match_" || s.startsWith "proof_")
        && (env.getModuleIdxFor? p).isSome then some p else none
  | _ => none

open Lean in
/-- External constants reached from `root` through this module's own constants, the external
private names among them, and equation/unfolding lemmas of other modules' constants. -/
def rvc2ExtDeps (env : Environment) (root : Name) : NameSet × Array Name × Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut ext : NameSet := {}
  let mut privs : Array Name := #[]
  let mut eqns : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some _ := rvc2ExtEqn? env c then eqns := eqns.push c
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet.toList do
        if (env.getModuleIdxFor? d).isSome then
          unless ext.contains d do
            ext := ext.insert d
            if isPrivateName d then privs := privs.push d
            if let some _ := rvc2ExtEqn? env d then eqns := eqns.push d
        else unless visited.contains d do stack := stack.push d
  return (ext, privs, eqns)

open Lean Elab Command in
elab "#ext_check " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let (ext, privs, eqns) := rvc2ExtDeps env n
  let tcs := ext.toList.filter fun d =>
    match env.getModuleIdxFor? d with
    | some i => (env.header.moduleNames[i]?.map (·.getRoot == `TCSlib)).getD false
    | none => false
  logInfo m!"EXT {n}: external {ext.size} (TCSlib {tcs.length}); external privates {privs}; external eqn/unfold lemmas {eqns}"

open Lean Elab Command in
elab "#ext_list " ids:ident* : command => do
  let env ← getEnv
  let mut all : NameSet := {}
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let (ext, _, _) := rvc2ExtDeps env n
    for d in ext.toList do all := all.insert d
  let tcs := all.toList.filter fun d =>
    match env.getModuleIdxFor? d with
    | some i => (env.header.moduleNames[i]?.map (·.getRoot == `TCSlib)).getD false
    | none => false
  let s := (tcs.map toString).toArray.qsort (· < ·)
  logInfo m!"EXTLIST total {all.size}; TCSlib {s.size}: {s}"
'''
cmds = []
for t in targets: cmds.append(f'#print axioms {t}')
for t in targets: cmds.append(f'#sorry_sources {t}')
for n in names: cmds.append(f'#print axioms {n}')
for n in names: cmds.append(f'#ext_check {n}')
cmds.append('#ext_list ' + ' '.join(names))
open(out, 'w', encoding='utf-8').write('\n'.join(lines).rstrip('\n') + '\n' + tail + '\n' + '\n'.join(cmds) + '\n')
print('commands', len(cmds))
