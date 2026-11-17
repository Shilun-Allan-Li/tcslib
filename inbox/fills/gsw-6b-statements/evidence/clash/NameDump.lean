import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
import TCSlib.Cryptography.LWE

/-! Name dump (gsw-6b statements, sub-agent probe; check 11): every non-internal constant declared
by the 9 new modules, the two facades and `LWE/BitEncoding` (all of it; O2's five are marked by
the comparison), private names demangled (`Name.isPrivateName`, `privateToUserName`). Output
TSV on stdout: full name, kind (private flagged), module. -/

open Lean Elab Command

def dumpMods : List Name :=
  [`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic,
   `TCSlib.Cryptography.LWE.Ratio,
   `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW,
   `TCSlib.Cryptography.LWE,
   `TCSlib.Cryptography.LWE.BitEncoding]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[i.toNat]!
    if !dumpMods.contains m then continue
    let priv := isPrivateName n
    let u := if priv then (privateToUserName? n).getD n else n
    if u.isInternalDetail then continue
    let k := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
    rows := rows.push s!"{u}\t{if priv then "private " else ""}{k}\t{m}"
  for r in rows.qsort (· < ·) do IO.println r
