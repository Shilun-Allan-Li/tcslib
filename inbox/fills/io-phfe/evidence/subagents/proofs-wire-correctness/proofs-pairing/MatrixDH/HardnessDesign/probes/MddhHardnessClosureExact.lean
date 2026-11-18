import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Foundations.Subexponential
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.Pairing.BilinearGen

open Complexity TCSlib.Cryptography.Games

example (G : BilinearGen) (d ℓ : PolyExpr) (β : ℕ → ℝ)
    (hβ : ∀ c : ℝ, 0 < c → c < 1 → SubexpSmall c β)
    (hBound : ∀ D : NUPPT, ∃ B : NUPPT, ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * G.dlinAdv B κ + β κ)
    (h : G.SubexpDLIN) : SubexpHard (G.mddhAdv d ℓ) := exact?%

end TCSlib.Cryptography.Pairing.BilinearGen
