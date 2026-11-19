import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): owner `GSW/Bootstrap.lean`, negative: `bootNoise` read by `rfl`. Passes unsealed; must fail exactly once sealed. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example (P : Parameters) (β : ℕ) :
    bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β)) := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
