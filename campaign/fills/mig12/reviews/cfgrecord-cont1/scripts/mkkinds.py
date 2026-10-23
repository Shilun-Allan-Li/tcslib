import sys
# usage: mkkinds.py <out .lean> <names file>...: a probe importing the module's own imports that prints,
# for each constant, its kind, reducibility, projection/instance/matcher flags, the default simp set's
# view of it, and its module.
out, files = sys.argv[1], sys.argv[2:]
names = []
for f in files:
    for l in open(f, encoding='utf-8'):
        l = l.strip()
        if l and l not in names: names.append(l)
hdr = '''import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.Contract

open Lean Meta Elab Command in
elab "#kinds " ids:ident* : command => liftTermElabM do
  let env ← getEnv
  let s ← getSimpTheorems
  for id in ids do
    let n := id.getId
    let some ci := env.find? n | logInfo m!"KIND {n} MISSING"; continue
    let k := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let r ← getReducibilityStatus n
    let rs := match r with | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
    let proj := (env.getProjectionFnInfo? n).isSome
    let inst ← isInstance n
    let mat := (Meta.Match.Extension.getMatcherInfo? env n).isSome
    let unf := s.isDeclToUnfold n
    let lem := s.lemmaNames.contains (.decl n)
    let eq1 := s.lemmaNames.contains (.decl (n ++ `eq_1))
    let mod := match env.getModuleIdxFor? n with
      | some i => toString (env.header.moduleNames[i]!)
      | none => "this"
    logInfo m!"KIND {n} {k} {rs} proj={proj} inst={inst} matcher={mat} simpUnfold={unf} simpLemma={lem} simpEq1={eq1} {mod}"
'''
body = ''.join(f'#kinds {n}\n' for n in names if not n.startswith('_private'))
open(out, 'w', encoding='utf-8').write(hdr + '\n' + body)
print('names', len(names))
