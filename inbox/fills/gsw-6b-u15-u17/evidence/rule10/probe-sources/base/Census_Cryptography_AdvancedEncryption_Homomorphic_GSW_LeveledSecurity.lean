import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity

open Lean Elab Command Meta

/-! Seal census (sc-compose, base) for `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean`: the file's own imports; one `CAT` line per constant of a
TCSlib module of the import closure (all foreign to the file). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`TCSlib).isPrefixOf mod do continue
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let st := match getReducibilityStatusCore env c with
      | .reducible => "reducible" | .semireducible => "semireducible"
      | .irreducible => "irreducible"
    let inst := isInstanceCore env c
    let matcher := (Match.Extension.getMatcherInfo? env c).isSome
    out := out.push s!"CAT\t{c}\t{mod}\t{kind}\t{st}\t{inst}\t{matcher}\t{isPrivateName c}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size}"
