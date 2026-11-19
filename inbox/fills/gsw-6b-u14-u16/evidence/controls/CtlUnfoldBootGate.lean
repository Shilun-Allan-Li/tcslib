import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): the new public helper `encrypts_bootGate`, negative: its case split read off `bootGate` by `rfl` (fan-in 0) instead of the case reader. Passes unsealed; must fail exactly once sealed. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example (P : Parameters) (evk : Fin P.columns → Ciphertext P) (cts : List (Ciphertext P)) :
    bootGate P evk ⟨.not, []⟩ cts = bootNAND P evk (gadget P) (gadget P) := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
