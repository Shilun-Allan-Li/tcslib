import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula from another file through its body
example (P : Parameters) : decDepth P = FormulaArith.modSumDepth P.columns P.lwe.modulus :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
