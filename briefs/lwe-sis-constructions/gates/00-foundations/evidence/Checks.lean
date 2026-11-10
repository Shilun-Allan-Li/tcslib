import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeVector
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeVector_eq
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeMatrix
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeMatrix_eq
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeVector_length
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeMatrix_length
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeVector_injective
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeMatrix_injective
#print axioms TCSlib.Cryptography.LWE.Family
#print axioms TCSlib.Cryptography.LWE.Family.inputBitsBound
#print axioms TCSlib.Cryptography.LWE.Family.inputBitsBound_eq
#print axioms TCSlib.Cryptography.LWE.Family.encodeChallenge_length_le
#print axioms TCSlib.Cryptography.LWE.Family.advantageAt
#print axioms TCSlib.Cryptography.LWE.Family.advantageAt_eq
#print axioms TCSlib.Cryptography.LWE.DLWEAssumption
#print axioms TCSlib.Cryptography.LWE.dlweAssumption_iff
#print axioms TCSlib.Cryptography.LWE.Parameters
#print axioms TCSlib.Cryptography.LWE.instNeZeroNatModulus
#print axioms TCSlib.Cryptography.LWE.noisyValues
#print axioms TCSlib.Cryptography.LWE.noisyValues_apply
#print axioms TCSlib.Cryptography.LWE.sample
#print axioms TCSlib.Cryptography.LWE.sample_fst
#print axioms TCSlib.Cryptography.LWE.sample_snd
#print axioms TCSlib.Cryptography.LWE.encodeChallenge
#print axioms TCSlib.Cryptography.LWE.encodeChallenge_eq
#print axioms TCSlib.Cryptography.LWE.encodeChallenge_length
#print axioms TCSlib.Cryptography.LWE.encodeChallenge_injective
#print axioms TCSlib.Cryptography.LWE.decisionAdvantage
#print axioms TCSlib.Cryptography.LWE.decisionAdvantage_eq
#print axioms TCSlib.Cryptography.LWE.Noise
#print axioms TCSlib.Cryptography.LWE.Noise.Bounded
#print axioms TCSlib.Cryptography.LWE.Noise.bounded_iff
#print axioms TCSlib.Cryptography.SIS.Family
#print axioms TCSlib.Cryptography.SIS.Family.inputBitsBound
#print axioms TCSlib.Cryptography.SIS.Family.inputBitsBound_eq
#print axioms TCSlib.Cryptography.SIS.Family.outputBitsBound
#print axioms TCSlib.Cryptography.SIS.Family.outputBitsBound_eq
#print axioms TCSlib.Cryptography.SIS.Family.encodeChallenge_length_le
#print axioms TCSlib.Cryptography.SIS.Family.encodeSolution_length_le
#print axioms TCSlib.Cryptography.SIS.Family.successAt
#print axioms TCSlib.Cryptography.SIS.Family.successAt_eq
#print axioms TCSlib.Cryptography.SIS.SISAssumption
#print axioms TCSlib.Cryptography.SIS.sisAssumption_iff
#print axioms TCSlib.Cryptography.SIS.Parameters
#print axioms TCSlib.Cryptography.SIS.instNeZeroNatModulus
#print axioms TCSlib.Cryptography.SIS.IsSolution
#print axioms TCSlib.Cryptography.SIS.isSolution_iff
#print axioms TCSlib.Cryptography.SIS.encodeChallenge
#print axioms TCSlib.Cryptography.SIS.encodeChallenge_eq
#print axioms TCSlib.Cryptography.SIS.decodeSolution
#print axioms TCSlib.Cryptography.SIS.decodeSolution_eq
#print axioms TCSlib.Cryptography.SIS.decodeSolution_of_length_ne
#print axioms TCSlib.Cryptography.SIS.encodeSolution
#print axioms TCSlib.Cryptography.SIS.encodeSolution_eq
#print axioms TCSlib.Cryptography.SIS.encodeChallenge_length
#print axioms TCSlib.Cryptography.SIS.encodeChallenge_injective
#print axioms TCSlib.Cryptography.SIS.encodeSolution_length
#print axioms TCSlib.Cryptography.SIS.decodeSolution_encodeSolution
#print axioms TCSlib.Cryptography.SIS.decodeSolution_encodeSolution_of_isSolution
#print axioms TCSlib.Cryptography.SIS.successProbability
#print axioms TCSlib.Cryptography.SIS.successProbability_eq
open Lean in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.toString.startsWith "TCSlib.Cryptography.LWE." ||
          mod.toString.startsWith "TCSlib.Cryptography.SIS." ||
          mod.toString.startsWith "TCSlib.Cryptography.Encoding." then
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        logInfo m!"PHASE0_CONSTANT|{mod}|{n}|{kind}|{isPrivateName n}"
