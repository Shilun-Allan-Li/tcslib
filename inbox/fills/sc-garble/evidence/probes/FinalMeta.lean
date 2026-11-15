import TCSlib.Cryptography.SecureComputation
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned := #[
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity,
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti,
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser,
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceReduction,
    `TCSlib.Complexity.CircuitComplexity.DAGCircuit,
    `TCSlib.Cryptography.SecureComputation.Garbling,
    `TCSlib.Cryptography.SecureComputation.Garbling.Probability,
    `TCSlib.Cryptography.SecureComputation.Garbling.CoinBlocks,
    `TCSlib.Cryptography.SecureComputation.GarblingSecurity,
    `TCSlib.Cryptography.SecureComputation.Yao,
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad,
    `TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.WrongKey,
    `TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals,
    `TCSlib.Cryptography.SecureComputation.GarblingSecurity.NestedBounds]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if owned.contains modName then
        let axioms ← collectAxioms name
        logInfo m!"AXIOMS\t{modName}\t{name}\t{axioms}"
#print axioms TCSlib.Cryptography.SecureComputation.garbling_good_whp
#print axioms TCSlib.Cryptography.SecureComputation.specialScheme_multiMessageSecure_of_joint
#print axioms TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure
#print axioms TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure

#print axioms TCSlib.Cryptography.SecureComputation.spDecStr_wrongKey
#print axioms TCSlib.Cryptography.SecureComputation.specialScheme_wrongKey
#print axioms TCSlib.Cryptography.SecureComputation.specialScheme_multiMessageSecure
#print axioms TCSlib.Cryptography.SecureComputation.nestedSpecial_wrongKeyBot

#print axioms TCSlib.Cryptography.SecureComputation.uprob_not_good_le
#print axioms TCSlib.Cryptography.SecureComputation.uprob_not_good_le_of_perm
#print axioms TCSlib.Cryptography.SecureComputation.yaoSeed_good_whp

#print axioms TCSlib.Cryptography.SecureComputation.sliceMultiMessageSecure_of_prfOut
