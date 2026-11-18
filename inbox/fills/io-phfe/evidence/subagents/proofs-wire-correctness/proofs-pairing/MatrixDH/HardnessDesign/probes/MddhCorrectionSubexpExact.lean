import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Foundations.Subexponential
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.Pairing.BilinearGen

open Complexity TCSlib.Cryptography.Games

example (p : ℕ → ℕ) (d : PolyExpr) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    SubexpSmall c (fun κ => (d.eval κ : ℝ) * (4 / (p κ : ℝ))) := exact?%

end TCSlib.Cryptography.Pairing.BilinearGen
