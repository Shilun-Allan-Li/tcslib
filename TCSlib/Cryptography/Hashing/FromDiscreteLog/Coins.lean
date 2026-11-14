/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Splitting a machine's coin polynomial

A machine whose coin polynomial is a sum can read its coins as two consecutive bit vectors.
The equivalence below combines the published machine-coin identification, an equality of
evaluated polynomial lengths, and the shared coin-splitting equivalence.

## Main definitions

* `sumCoinsEquiv` splits the coins of a machine with coin polynomial `c + d`.

## Main results

* `sumCoinsEquiv_symm_ofFn` reads the reassembled coin string as a concatenation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, Protocol 142.2 and the proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open Complexity TCSlib.Cryptography

/-- A machine with coin polynomial `c + d` has coins equivalent to a `c(n)`-bit vector and
a `d(n)`-bit vector. -/
def sumCoinsEquiv (A : NUPPT) {c d : PolyExpr} (h : A.coins = .add c d) (n : ℕ) :
    A.Coins n ≃ (Fin (c.eval n) → Bool) × (Fin (d.eval n) → Bool) :=
  (NUPPT.coinsEquivPoly h n).trans
    ((Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)).trans
      (splitCoins (c.eval n) (d.eval n)))

/-- The sum-coin equivalence first identifies the machine's polynomial-length coin vector,
then transports its length through evaluation of addition and applies `splitCoins`. -/
theorem sumCoinsEquiv_eq (A : NUPPT) {c d : PolyExpr} (h : A.coins = .add c d) (n : ℕ) :
    sumCoinsEquiv A h n =
      (NUPPT.coinsEquivPoly h n).trans
        ((Equiv.arrowCongr (finCongr (PolyExpr.eval_add c d n)) (Equiv.refl Bool)).trans
          (splitCoins (c.eval n) (d.eval n))) := rfl

/-- Reassembling the two components of a machine's sum-length coins concatenates their
words: `ofFn (sumCoinsEquiv.symm (r, s)) = ofFn r ++ ofFn s`. -/
theorem sumCoinsEquiv_symm_ofFn (A : NUPPT) {c d : PolyExpr}
    (h : A.coins = .add c d) (n : ℕ)
    (r : Fin (c.eval n) → Bool) (s : Fin (d.eval n) → Bool) :
    List.ofFn ((sumCoinsEquiv A h n).symm (r, s)) = List.ofFn r ++ List.ofFn s := by
  rw [sumCoinsEquiv_eq, Equiv.symm_trans_apply, NUPPT.coinsEquivPoly_symm_ofFn,
    Equiv.symm_trans_apply, Equiv.arrowCongr_symm]
  rw [finCongr_symm, Equiv.refl_symm, ofFn_arrowCongr_finCongr, ofFn_splitCoins_symm]

end TCSlib.Cryptography.Authentication.FromDiscreteLog
