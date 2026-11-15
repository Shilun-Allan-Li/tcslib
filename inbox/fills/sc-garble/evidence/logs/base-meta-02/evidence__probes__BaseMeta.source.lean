import TCSlib.Cryptography.SecureComputation
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned := #[
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity,
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti,
    `TCSlib.Cryptography.SecureComputation.Garbling,
    `TCSlib.Cryptography.SecureComputation.GarblingSecurity,
    `TCSlib.Cryptography.SecureComputation.Yao]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if modName.toString.startsWith "TCSlib." then
        match ci with
        | .defnInfo d =>
          let abbrev := match d.hints with
            | .abbrev => true
            | _ => false
          logInfo m!"DEF\t{modName}\t{name}\t{abbrev}"
        | _ => pure ()
      if owned.contains modName then
        let axioms ← collectAxioms name
        logInfo m!"AXIOMS\t{modName}\t{name}\t{axioms}"
#print axioms TCSlib.Cryptography.SecureComputation.garbling_good_whp
#print axioms TCSlib.Cryptography.SecureComputation.specialScheme_multiMessageSecure_of_joint
#print axioms TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure
#print axioms TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure
