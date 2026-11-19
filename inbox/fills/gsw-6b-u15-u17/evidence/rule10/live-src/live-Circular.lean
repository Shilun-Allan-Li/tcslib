
/-! Liveness pair (gsw-6b-u15-u17, C6, owner Circular.lean), appended to the owner's own probe: a
foreign definition read by `rfl` (negative: closes unsealed, fails exactly once sealed) and the same
fact through its published reader (positive: closes sealed). -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

-- NEG realView by rfl
example (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : KeySeed P χ × Coins P) :
    realView P χ μ r = view P μ (LWE.sample P.lwe χ r.1) r.2 :=
  rfl
-- POS realView through realView_eq
example (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : KeySeed P χ × Coins P) :
    realView P χ μ r = view P μ (LWE.sample P.lwe χ r.1) r.2 :=
  realView_eq P χ μ r

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
