import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
import TCSlib.Cryptography.Encryption
import TCSlib.Cryptography.Hashing
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeVector
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeVector_eq
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeVector_of_length_ne
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeVector_of_outOfRange
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeVector_encodeVector
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeVector_decodeVector
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeMatrix
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeMatrix_eq
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeMatrix_of_length_ne
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeMatrix_of_outOfRange
#print axioms TCSlib.Cryptography.Encoding.Modular.decodeMatrix_encodeMatrix
#print axioms TCSlib.Cryptography.Encoding.Modular.encodeMatrix_decodeMatrix
#print axioms TCSlib.Cryptography.LWE.Parameters.withSamples
#print axioms TCSlib.Cryptography.LWE.Family.withSamples
#print axioms TCSlib.Cryptography.LWE.multiMessageSamples
#print axioms TCSlib.Cryptography.LWE.multiMessageSamples_eq
#print axioms TCSlib.Cryptography.LWE.multiMessageSamples_eval
#print axioms TCSlib.Cryptography.LWE.BitEncoding.codepoint
#print axioms TCSlib.Cryptography.LWE.BitEncoding.codepoint_eq
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance_eq
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance_symm
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance_triangle
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance_add_right
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance_codepoints
#print axioms TCSlib.Cryptography.LWE.BitEncoding.distance_intCast_zero_le
#print axioms TCSlib.Cryptography.LWE.BitEncoding.decode
#print axioms TCSlib.Cryptography.LWE.BitEncoding.decode_eq
#print axioms TCSlib.Cryptography.LWE.BitEncoding.decode_codepoint_add
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.shift
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.encrypt
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.decrypt
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.decrypt_apply
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.decrypt_encrypt
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.decrypt_encrypt_noise
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.encryptDist
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.encryptDist_eq_shift_sample
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.acceptProb_uniform_shift
#print axioms TCSlib.Cryptography.Encryption.Symmetric.Regev.distAdv_encrypt_le
#print axioms TCSlib.Cryptography.Hashing.SIS.hash
#print axioms TCSlib.Cryptography.Hashing.SIS.hash_eq
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionDifference
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionDifference_apply
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionDifference_ne_zero
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionDifference_sqNorm_le
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionDifference_isSolution
#print axioms TCSlib.Cryptography.Hashing.SIS.cardinal_compression
#print axioms TCSlib.Cryptography.Hashing.SIS.exists_collision
#print axioms TCSlib.Cryptography.Hashing.SIS.exists_solution
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionProbability
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionProbability_eq
#print axioms TCSlib.Cryptography.Hashing.SIS.collisionProbability_le_successProbability
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_modulus_ge_two
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_magnitude_fits
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadicParameters
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadicFamily
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_sqNormBound_lt_modulus_sq
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_cardinal_compression
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_exists_solution
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_not_isSolution_of_modulus_dvd
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_inputBitsBound_eval
#print axioms TCSlib.Cryptography.Hashing.SIS.dyadic_outputBitsBound_eval
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
        logInfo m!"CONSTRUCTION_CONSTANT|{mod}|{n}|{kind}|{isPrivateName n}"
        let axs ← Lean.collectAxioms n
        let labels := String.intercalate "," (axs.toList.map fun a => a.toString)
        logInfo m!"CONSTRUCTION_AXIOMS|{n}|{labels}"
