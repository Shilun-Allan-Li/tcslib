-- New helper target only. Do not import the proposed named declaration.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
namespace PartialGarbling.PrefixAlgebra

open scoped BigOperators

example {I R : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid R] (d : ℕ)
    (flow : (Σ k : Fin d, Fin (k.val + 1) → I) → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) = u then flow e else 0) =
      if h : u.1.val < d then
        ∑ a : I, flow ⟨⟨u.1.val, h⟩, Fin.snoc (α := fun _ => I) u.2 a⟩
      else 0 := sorry

end PartialGarbling.PrefixAlgebra
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
