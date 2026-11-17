import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Complexity
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encodeCiphertext` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic from another file through its body
example (P : Parameters) (C : Ciphertext P) : encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
