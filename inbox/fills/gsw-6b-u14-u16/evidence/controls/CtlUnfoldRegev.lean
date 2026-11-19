import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): foreign owner `Encryption/PublicKey/Regev/Basic.lean`, negative: `Regev.keygen` read by `rfl`. Passes unsealed; must fail exactly once sealed. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example (P : Parameters) (χ : LWE.Noise) (rg : KeySeed P χ) :
    (Regev.keygen P.lwe χ rg).2 = rg.2.1 := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
