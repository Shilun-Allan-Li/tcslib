import TCSlib.Cryptography.SecretSharing.Efficient
import TCSlib.Cryptography.SecretSharing.ShamirEfficient
import TCSlib.Cryptography.MPC.BGW.Efficient
open Lean Meta Elab Command

def targetMods : Array Name := #[`TCSlib.Cryptography.SecretSharing.Efficient,
  `TCSlib.Cryptography.SecretSharing.ShamirEfficient, `TCSlib.Cryptography.MPC.BGW.Efficient]

elab "#stmtax" : command => do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless targetMods.contains mod do continue
    if n.isInternalDetail || isPrivateName n then continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let ty ← liftTermElabM <| do
      let f ← ppExpr ci.type
      pure (toString f)
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | _ => "other"
    rows := rows.push s!"{mod}\t{n}\t{kind}\t{axs.toList}\t{ty.replace "\n" " "}"
  let sorted := rows.qsort (· < ·)
  for r in sorted do logInfo r
  logInfo s!"TOTAL {sorted.size}"

#stmtax
