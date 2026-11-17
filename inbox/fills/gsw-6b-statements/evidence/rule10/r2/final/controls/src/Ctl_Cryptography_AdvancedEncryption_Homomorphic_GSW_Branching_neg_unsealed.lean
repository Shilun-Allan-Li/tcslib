import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.select` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching from another file through its body
example (P : Parameters) (C U V : Ciphertext P) : select P C U V = mul P (gadget P - C) U + mul P C V :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
