/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete wrong-key bounds for nested special encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingCoins.length_nestedInner`: the inner ciphertext has `4n+2` bits.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingCoins

open Complexity Turing TCSlib.Cryptography

/-- A special ciphertext with an `n`-bit nonce, an `n`-bit message, and a `2n`-bit pad has
`innerLen(n) = 4n+2` bits:
`|spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧| = innerLen.eval n`. -/
theorem length_nestedInner
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E : List Bool → List Bool}
    (hGE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G n k r)) (n : ℕ) (k m r : Fin n → Bool) :
    (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length = innerLen.eval n := by
  rw [length_spEncStr E (by rw [hGE]; simp), List.length_ofFn, List.length_ofFn,
    innerLen_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var, PolyExpr.eval_const]
  omega

end TCSlib.Cryptography.SecureComputation.GarblingCoins
