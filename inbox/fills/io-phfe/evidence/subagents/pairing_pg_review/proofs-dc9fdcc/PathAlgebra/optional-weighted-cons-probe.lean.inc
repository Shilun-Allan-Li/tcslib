-- Optional later probe only; no header is proposed for immediate integration.
-- This weighted suffix decomposition could move more algebra out of Layered.
-- Requires its own exact?/apply? searches before a new helper proof.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
namespace PartialGarbling.PathAlgebra

example {I R : Type*} [Fintype I] [CommSemiring R] (k : ℕ)
    (c : (Fin (k + 1) → I) → R) (w : I → R) :
    (∑ tau : Fin (k + 1) → I, c tau * ∏ i, w (tau i)) =
      ∑ a : I, w a * ∑ tau : Fin k → I,
        c (Fin.cons a tau) * ∏ i, w (tau i) := sorry

end PartialGarbling.PathAlgebra
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
