import Lean
open Lean Elab Command

/-- `#kinds a b c`: for each identifier resolvable in the current scope, report its kind and the
module that defines it (one line each); unresolvable names (locals) are reported as such. -/
elab "#kinds " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    try
      let n ← liftCoreM <| realizeGlobalConstNoOverload id
      let some ci := env.find? n | logInfo m!"KIND|{n}|missing|"
      let k := match ci with
        | .defnInfo _ => "def" | .thmInfo _ => "thm" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
        | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct"
        | .quotInfo _ => "quot"
      let modName := match env.getModuleIdxFor? n with
        | some i => env.header.moduleNames[i.toNat]!
        | none => `current
      logInfo m!"KIND|{n}|{k}|{modName}"
    catch _ => logInfo m!"KIND|{id.getId}|unresolved|"
