#!/usr/bin/env python3
"""In-module axiom / admission / dependency / public-constant probe.

usage: mkax.py <module file> <out file> <names,comma-separated or -> <targets,comma-separated or ->
Names and targets are fully qualified Lean names. Appends, after the module's last line:
  - a sorry-source walk (`#sorry_sources`), an external-dependency walk (`#ext_check`,
    `#ext_list`), a definition-kind census of the external TCSlib constants reached (`#ext_defs`),
  - a census of the module's own public constants (`#pub_census`, the names added by this module
    that are not private, excluding the probe's own `cont7Probe*` helpers),
  - `#print axioms` for every target and name.
Inserts one line `import Lean.Util.FoldConsts` after the last import (line numbers shift by 1).
"""
import sys

src, out = sys.argv[1], sys.argv[2]
names = [] if sys.argv[3] == '-' else sys.argv[3].split(',')
targets = [] if sys.argv[4] == '-' else sys.argv[4].split(',')
lines = open(src, encoding='utf-8').read().rstrip('\n').split('\n')
last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
lines.insert(last_import + 1, 'import Lean.Util.FoldConsts')
assert lines[last_import + 1] == 'import Lean.Util.FoldConsts'
tail = r'''

open Lean in
/-- Every constant in the dependency closure of `root` whose own type or value mentions
`sorryAx` (the reviewer's read-only admission walk). -/
def cont7ProbeSorrySources (env : Environment) (root : Name) : Array Name := Id.run do
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
  logInfo m!"SORRYSRC {n}: direct sorryAx users in closure: {cont7ProbeSorrySources (← getEnv) n}"

open Lean in
/-- Is `c` an equation/unfolding lemma or matcher of a constant defined in another module? -/
def cont7ProbeExtEqn? (env : Environment) (c : Name) : Option Name :=
  match c with
  | .str p s =>
    if (s.startsWith "eq_" || s == "_unfold" || s.startsWith "match_" || s == "eq_def")
        && (env.getModuleIdxFor? p).isSome then some p else none
  | _ => none

open Lean in
/-- External constants reached from `root` through this module's own constants, the external
private names among them, and equation/unfolding lemmas of other modules' constants. -/
def cont7ProbeExtDeps (env : Environment) (root : Name) :
    NameSet × Array Name × Array Name := Id.run do
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
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet.toList do
        if (env.getModuleIdxFor? d).isSome then
          unless ext.contains d do
            ext := ext.insert d
            if isPrivateName d then privs := privs.push d
            if let some _ := cont7ProbeExtEqn? env d then eqns := eqns.push d
        else unless visited.contains d do stack := stack.push d
  return (ext, privs, eqns)

open Lean in
def cont7ProbeIsTCS (env : Environment) (d : Name) : Bool :=
  match env.getModuleIdxFor? d with
  | some i => (env.header.moduleNames[i]?.map (·.getRoot == `TCSlib)).getD false
  | none => false

open Lean in
def cont7ProbeModOf (env : Environment) (d : Name) : String :=
  match env.getModuleIdxFor? d with
  | some i => (env.header.moduleNames[i]?.map toString).getD "?"
  | none => "this"

open Lean Elab Command in
elab "#ext_check " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let (ext, privs, eqns) := cont7ProbeExtDeps env n
  let tcs := ext.toList.filter (cont7ProbeIsTCS env)
  logInfo m!"EXT {n}: external {ext.size} (TCSlib {tcs.length}); external privates {privs}; external eqn/unfold/matcher {eqns}"

open Lean Elab Command in
elab "#ext_defs " ids:ident* : command => do
  let env ← getEnv
  let mut all : NameSet := {}
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let (ext, _, _) := cont7ProbeExtDeps env n
    for d in ext.toList do all := all.insert d
  let tcs := (all.toList.filter (cont7ProbeIsTCS env)).toArray.qsort (fun a b => a.toString < b.toString)
  logInfo m!"EXTLIST total {all.size}; TCSlib {tcs.size}"
  for d in tcs do
    let kind := match env.find? d with
      | some (.defnInfo v) =>
        match v.hints with
        | .abbrev => "def(abbrev)"
        | .opaque => "def(opaque-hint)"
        | .regular _ =>
          match getReducibilityStatusCore env d with
          | .reducible => "def(reducible)"
          | .irreducible => "def(irreducible)"
          | _ => "def"
      | some (.thmInfo _) => "theorem"
      | some (.ctorInfo _) => "ctor"
      | some (.inductInfo _) => "inductive"
      | some (.recInfo _) => "recursor"
      | some (.opaqueInfo _) => "opaque"
      | some (.axiomInfo _) => "axiom"
      | some (.quotInfo _) => "quot"
      | none => "?"
    let proj := if (env.getProjectionFnInfo? d).isSome then " projection" else ""
    let inst := if Lean.Meta.isInstanceCore env d then " instance" else ""
    let simp := ""
    logInfo m!"EXTDEF {kind}{proj}{inst} {d} [{cont7ProbeModOf env d}]{simp}"

open Lean Elab Command in
elab "#pub_census" : command => do
  let env ← getEnv
  let mut pub : Array Name := #[]
  let mut priv := 0
  for (n, _) in env.constants.map₂.toList do
    if isPrivateName n then priv := priv + 1
    else if (n.toString.splitOn "cont7Probe").length > 1 then pure ()
    else pub := pub.push n
  let sorted := pub.qsort (fun a b => a.toString < b.toString)
  logInfo m!"PUBCENSUS public {sorted.size}, private {priv}"
  for n in sorted do logInfo m!"PUB {n}"

open Lean in
/-- The seal walk. From the new declarations `roots` (user names), collect the other-module
constants that occur in: the type and value of every constant of this module whose user name
extends a root (the new declarations and their auxiliaries); the value of every other definition
of this module reached (own definitions may be unfolded, exposing what they mention); the type
only of every other theorem of this module reached (cited old lemmas: statements, not proofs). -/
def cont7ProbeSealWalk (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let isNew (c : Name) : Bool :=
    let u := (privateToUserName? c).getD c
    roots.any fun r => r.isPrefixOf u
  let mut visited : NameSet := {}
  let mut stack : Array Name := roots.filterMap fun r =>
    (env.constants.map₂.toList.find? fun (n, _) => ((privateToUserName? n).getD n) == r).map (·.1)
  let mut ext : NameSet := {}
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if (env.getModuleIdxFor? c).isSome then
      ext := ext.insert c
      continue
    if let some ci := env.find? c then
      let tyUsed := ci.type.getUsedConstants
      let valUsed := match ci with
        | .thmInfo v => if isNew c then v.value.getUsedConstants else #[]
        | .defnInfo v => v.value.getUsedConstants
        | _ => #[]
      for d in tyUsed ++ valUsed do
        unless visited.contains d do stack := stack.push d
  return ext

open Lean Elab Command Meta in
elab "#seal_walk " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.map (·.getId)
  let ext := cont7ProbeSealWalk env roots
  let tcs := (ext.toList.filter (cont7ProbeIsTCS env)).toArray.qsort
    (fun a b => a.toString < b.toString)
  let simpThms ← liftTermElabM getSimpTheorems
  logInfo m!"SEALWALK roots {roots.size}; external {ext.size}; TCSlib {tcs.size}"
  for d in tcs do
    match env.find? d with
    | some (.defnInfo v) =>
      let red := match v.hints, getReducibilityStatusCore env d with
        | .abbrev, _ => "abbrev"
        | _, .reducible => "reducible"
        | _, .irreducible => "irreducible"
        | _, _ => "semireducible"
      let proj := if (env.getProjectionFnInfo? d).isSome then " projection" else ""
      let inst := if Lean.Meta.isInstanceCore env d then " instance" else ""
      let simp := if simpThms.isDeclToUnfold d ||
          simpThms.isLemma (.decl (d ++ `eq_1)) then " simp" else ""
      logInfo m!"SEALDEF {red}{proj}{inst}{simp} {d} [{cont7ProbeModOf env d}]"
    | _ => pure ()

open Lean Elab Command Meta in
/-- A `rfl` control for one definition: is `@f` definitionally equal, at default transparency
(the check `rfl` makes), to its own delta-unfolded value? Unsealed this closes; with `f` locally
irreducible it fails, and the failure is logged as an error. -/
elab "#seal_control " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM do
    let ci ← getConstInfo n
    let some v := ci.value? | throwError "CONTROL {n}: no value"
    let us := ci.levelParams.map mkLevelParam
    let ok ← withTransparency .default <| isDefEq (mkConst n us) v
    if ok then logInfo m!"CONTROL {n}: rfl closes"
    else logError m!"CONTROL {n}: rfl fails"
'''
cmds = []
for t in targets:
    cmds.append(f'#print axioms {t}')
for t in targets:
    cmds.append(f'#sorry_sources {t}')
for n in names:
    cmds.append(f'#print axioms {n}')
for n in names:
    cmds.append(f'#sorry_sources {n}')
for n in names:
    cmds.append(f'#ext_check {n}')
if names:
    cmds.append('#ext_defs ' + ' '.join(names))
    cmds.append('#seal_walk ' + ' '.join(n for n in names if not n.endswith('.exists_canonDecider')))
cmds.append('#pub_census')
open(out, 'w', encoding='utf-8').write('\n'.join(lines) + tail + '\n' + '\n'.join(cmds) + '\n')
print('commands', len(cmds))
