import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): foreign owner `CircuitComplexity/DAGCircuit.lean` (host H19), negative: `DAGCircuit.depth` read by `rfl`. Passes unsealed; must fail exactly once sealed. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example {n : ℕ} (C : DAGCircuit n) : C.depth = C.depthAt C.output := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
