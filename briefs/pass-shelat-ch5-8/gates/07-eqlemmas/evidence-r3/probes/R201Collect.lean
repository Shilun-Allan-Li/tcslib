import TCSlib.Cryptography.Asymptotic.HardCoreCollection

/-! R2-01 seal collector: every TCSlib definition reached (transitively, through types and values,
matchers included) from `PermCollection.glPad` and `Collection.glPad`. Kinds: `def` (plain),
`aux` (matcher / auxiliary), `reducible`, `instance`, `proj`, `irreducible`. Printed one per line as
`SEAL <kind> <name>`; theorems, structures, constructors are walked through their types only. -/

open Lean Meta in
run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let isTCS (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some j => (modNames[j.toNat]!).getRoot == `TCSlib
    | none => false
  let roots : Array Name := #[`TCSlib.Cryptography.PermCollection.glPad,
    `TCSlib.Cryptography.Collection.glPad]
  let mut work := roots
  let mut seen : NameSet := {}
  let mut out : Array String := #[]
  while !work.isEmpty do
    let u := work.back!
    work := work.pop
    if seen.contains u then continue
    seen := seen.insert u
    unless isTCS u do continue
    let some ci := env.find? u | continue
    let kind : String := match ci with
      | .defnInfo _ =>
        if isMatcherCore env u then "aux"
        else if env.isProjectionFn u then "proj"
        else if isInstanceCore env u then "instance"
        else if getReducibilityStatusCore env u == .reducible then "reducible"
        else if getReducibilityStatusCore env u == .irreducible then "irreducible"
        else if (u.components.any fun c => c.toString.startsWith "_" ||
            c.toString.startsWith "match_" || c.toString.startsWith "proof_") then "aux"
        else "def"
      | .thmInfo _ => "thm" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | _ => "other"
    if kind != "thm" && kind != "inductive" && kind != "ctor" && kind != "rec" && kind != "other" then
      out := out.push s!"SEAL {kind} {u}"
    for c in ci.type.getUsedConstants do work := work.push c
    if kind != "thm" then
      match ci with
      | .defnInfo dv => for c in dv.value.getUsedConstants do work := work.push c
      | _ => pure ()
  for l in out.qsort (· < ·) do IO.println l
