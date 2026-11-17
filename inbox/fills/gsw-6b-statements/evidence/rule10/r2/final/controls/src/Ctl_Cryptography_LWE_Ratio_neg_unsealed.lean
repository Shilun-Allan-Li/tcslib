import TCSlib.Cryptography.LWE.Ratio
set_option autoImplicit false
namespace TCSlib.Cryptography.LWE
open Complexity
-- Rule 10 control (neg): reads `TCSlib.Cryptography.LWE.Family.RatioBounded` of TCSlib.Cryptography.LWE.Ratio from another file through its body
example (F : Family) (B : ℕ → ℕ) (p : PolyExpr) :
    F.RatioBounded B p ↔ ∀ κ, (F.noise κ).Bounded (B κ) ∧ (F.parameters κ).modulus ≤ p.eval κ * B κ :=
  Iff.rfl
end TCSlib.Cryptography.LWE
