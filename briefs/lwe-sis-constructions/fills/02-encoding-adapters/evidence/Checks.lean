import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
import TCSlib.Cryptography.Encryption
import TCSlib.Cryptography.Hashing
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.toLE
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.toLE_eq
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.toLE_eq_natBits
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.bitsVal_toLE
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.length_toLE_le
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.polyTimeComputable_toLE
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly_eq
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly_pairEncode
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly_length
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly_of_length_eq
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.polyTimeComputable_normalizeWidthPoly
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly_eq
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly_pairEncode
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly_length
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly_toLE
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly_toLE_of_length_eq
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.toLE_fromLEPoly
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.polyTimeComputable_fromLEPoly
#print axioms Complexity.BinArith.polyTimeComputable_reverse
#print axioms Complexity.BinArith.polyTimeComputable_normBits
#print axioms TCSlib.Cryptography.EnsembleLemmas.polyTimeComputable_zeros
#print axioms Complexity.polyTimeComputable_pairDropPoly
#print axioms Complexity.polyTimeComputable_pairFstD
#print axioms Complexity.polyTimeComputable_pairSndD
#print axioms Complexity.PolyTimeComputable.comp
#print axioms Complexity.PolyTimeComputable.pairEncode
#print axioms Complexity.PolyTimeComputable.append
open Lean in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.toString.startsWith "TCSlib.Cryptography.Encoding." ||
          mod.toString.startsWith "TCSlib.Cryptography.LWE." ||
          mod.toString.startsWith "TCSlib.Cryptography.SIS." ||
          mod.toString.startsWith "TCSlib.Cryptography.Encryption.Symmetric.Regev." ||
          mod.toString.startsWith "TCSlib.Cryptography.Hashing.SIS." then
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        logInfo m!"ADAPTER_CONSTANT|{mod}|{n}|{kind}|{isPrivateName n}"
        let axs ← Lean.collectAxioms n
        let labels := String.intercalate "," (axs.toList.map fun a => a.toString)
        logInfo m!"ADAPTER_AXIOMS|{n}|{labels}"
