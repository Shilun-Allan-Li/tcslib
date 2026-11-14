import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl

theorem positive (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := Complexity.PolyExpr.eval_const 2 n

end HashSignSensitivity

