import TCSlib.Cryptography.Candidates.Rabin

/-! The foreign TCSlib definitions read by the declarations of `Rabin.lean`: for each
declaration of the module (private ones included), the constants of its type and value that
are definitions (not theorems) of another TCSlib module. Printed per declaration and as a
union over the given declarations. -/
open Lean Elab Command in
elab "#rabin_foreign" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `TCSlib.Cryptography.Candidates.Rabin | logInfo "no module"
  let isTCSOther : Name → Bool := fun c =>
    match env.getModuleIdxFor? c with
    | some i => (`TCSlib).isPrefixOf (env.header.moduleNames[i.toNat]!) && i != modIdx
    | none => false
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n != some modIdx then continue
    let cs := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut fs : Array Name := #[]
    for c in cs do
      if isTCSOther c then
        match env.find? c with
        | some (.defnInfo _) => if !fs.contains c then fs := fs.push c
        | _ => pure ()
    if !fs.isEmpty then
      lines := lines.push s!"{n}\t{fs.toList}"
  logInfo (String.intercalate "\n" lines.toList)

#rabin_foreign
