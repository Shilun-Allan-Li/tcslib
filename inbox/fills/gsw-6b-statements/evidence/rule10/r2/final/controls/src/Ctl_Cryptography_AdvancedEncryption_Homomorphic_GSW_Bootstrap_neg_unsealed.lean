import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap from another file through its body
example (P : Parameters) (β : ℕ) : bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β)) :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
