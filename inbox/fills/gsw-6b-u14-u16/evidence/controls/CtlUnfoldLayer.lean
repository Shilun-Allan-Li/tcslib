import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): foreign owner `CircuitComplexity/NANDLayering.lean` (6a), negative: `litInput` read by `rfl`. Passes unsealed; must fail exactly once sealed. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example {n : ℕ} (x : Fin n → Bool) : litInput x = Fin.append x fun i => !x i := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
