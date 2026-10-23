#!/usr/bin/env python3
"""usage: mkdirect.py <module file> <names file (comma-separated, fully qualified)> <out file>
Appends `#direct_cites`: the constants occurring in the types and values of the new
declarations and their auxiliaries (this module's constants whose user name extends a root),
without descending into any other constant. Prints every external TCSlib constant (kind, module)
and every other constant of this module that the new code cites."""
import sys
src, namesf, out = sys.argv[1:4]
names = open(namesf).read().strip().split(',')
t = open(src, encoding='utf-8').read().rstrip('\n')
tail = r'''

open Lean in
def c7DirectWalk (env : Environment) (roots : Array Name) : NameSet × NameSet := Id.run do
  let isNew (c : Name) : Bool :=
    let u := (privateToUserName? c).getD c
    roots.any fun r => r.isPrefixOf u
  let mut visited : NameSet := {}
  let mut stack : Array Name := (env.constants.map₂.toList.filter fun (n, _) =>
    isNew n).toArray.map (·.1)
  let mut ext : NameSet := {}
  let mut own : NameSet := {}
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      for d in used do
        if (env.getModuleIdxFor? d).isSome then ext := ext.insert d
        else if isNew d then
          unless visited.contains d do stack := stack.push d
        else own := own.insert d
  return (ext, own)

open Lean Elab Command in
elab "#direct_cites " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.map (·.getId)
  let (ext, own) := c7DirectWalk env roots
  let tcs := (ext.toList.filter fun d => match env.getModuleIdxFor? d with
    | some i => (env.header.moduleNames[i]?.map (·.getRoot == `TCSlib)).getD false
    | none => false).toArray.qsort (fun a b => a.toString < b.toString)
  logInfo m!"DIRECT external {ext.size}; TCSlib {tcs.size}; own old {own.size}"
  for d in tcs do
    let kind := match env.find? d with
      | some (.thmInfo _) => "theorem"
      | some (.defnInfo _) => "def"
      | some (.ctorInfo _) => "ctor"
      | some (.inductInfo _) => "inductive"
      | some (.recInfo _) => "recursor"
      | some _ => "other"
      | none => "?"
    let m := match env.getModuleIdxFor? d with
      | some i => (env.header.moduleNames[i]?.map toString).getD "?"
      | none => "?"
    logInfo m!"DEXT {kind} {d} [{m}]"
  for d in own.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"DOWN {(privateToUserName? d).getD d}"
'''
cmd = '#direct_cites ' + ' '.join(n for n in names if not n.endswith('.exists_canonDecider'))
open(out, 'w', encoding='utf-8').write(t + tail + cmd + '\n')
print('ok')
