import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
import TCSlib.Cryptography.Encryption
import TCSlib.Cryptography.Hashing
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.addPoly
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.addPoly_eq
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.addPoly_pairEncode
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.addPoly_length
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.addPoly_natCast_pairEncode
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.polyTimeComputable_addPoly
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.mulPoly
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.mulPoly_eq
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.mulPoly_pairEncode
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.mulPoly_length
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.mulPoly_natCast_pairEncode
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.polyTimeComputable_mulPoly
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.subPoly
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.subPoly_eq
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.subPoly_pairEncode
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.subPoly_length
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.subPoly_natCast_pairEncode
#print axioms TCSlib.Cryptography.Encoding.DyadicArithmetic.polyTimeComputable_subPoly
#print axioms Complexity.BinArith.polyTimeComputable_reverse
#print axioms Complexity.BinArith.polyTimeComputable_normBits
#print axioms TCSlib.Cryptography.EnsembleLemmas.polyTimeComputable_zeros
#print axioms Complexity.polyTimeComputable_pairDropPoly
#print axioms Complexity.polyTimeComputable_pairFstD
#print axioms Complexity.polyTimeComputable_pairSndD
#print axioms Complexity.PolyTimeComputable.comp
#print axioms Complexity.PolyTimeComputable.pairEncode
#print axioms Complexity.PolyTimeComputable.append
#print axioms Complexity.BinArith.polyTimeComputable_add
#print axioms Complexity.BinArith.polyTimeComputable_mul
#print axioms Complexity.BinArith.polyTimeComputable_sub
#print axioms Complexity.polyTimeComputable_const
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.polyTimeComputable_toLE
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.polyTimeComputable_normalizeWidthPoly
#print axioms TCSlib.Cryptography.Encoding.BinaryArith.polyTimeComputable_fromLEPoly
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
        logInfo m!"DYADIC_CONSTANT|{mod}|{n}|{kind}|{isPrivateName n}"
        let axs ← Lean.collectAxioms n
        let labels := String.intercalate "," (axs.toList.map fun a => a.toString)
        logInfo m!"DYADIC_AXIOMS|{n}|{labels}"
