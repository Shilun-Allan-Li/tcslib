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

/-- Inner and outer string success bounds `ε₁, ε₂` give
`(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁+ε₂)`, provided both errors are nonnegative and
the evaluators have the specified `2n` and `n+innerLen(n)` output lengths.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** There are at most two key positions. With one position use the inner
string bound and its uniform key/nonce marginal. With two positions, if the first key
differs, condition on the second position's keys and inner nonce, and apply the outer
bound to the resulting fixed inner ciphertext. If the first key agrees, correctness
opens the outer layer and the inner key/nonce marginal gives the inner bound. Add the
nonnegative unused error in each case. The zero-position case has no distinct choices. -/
theorem nestedSpecial_wrongKeyBot_of_string_bounds
    (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
    (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
    (E₁ E₂ : List Bool → List Bool)
    (hGE₁ : ∀ n (k r : Fin n → Bool), E₁ (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G₁ n k r))
    (hGE₂ : ∀ n (k r : Fin n → Bool), E₂ (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G₂ n k r)) (n : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h₁ : ∀ m : Fin n → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁)
    (h₂ : ∀ m : Fin (innerLen.eval n) → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂) :
    (nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂) := by
  rw [MultiEnc.wrongKeyBot_iff]
  intro len hlen a a' hne o
  have hcases : len = 0 ∨ len = 1 ∨ len = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (hne (Subsingleton.elim a a')).elim
  · have hab : a 0 ≠ a' 0 := fun h => hne (funext (Fin.forall_fin_one.mpr h))
    have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (0 : Fin 1)
      hab false).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
    refine (uprob_mono (fun t ht => ?_)).trans
      ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
    simp only [List.ofFn_succ, List.ofFn_zero, nestedSpecial_enc, nestedSpecial_dec] at ht
    exact Option.isSome_of_isSome_bind ht
  · by_cases hfirst : a 0 = a' 0
    · have hsecond : a 1 ≠ a' 1 := fun h =>
        hne (funext (Fin.forall_fin_two.mpr ⟨hfirst, h⟩))
      have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (1 : Fin 2)
        hsecond true).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (spDecStr E₁ n n (List.ofFn t.2.1)
            (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
      refine (uprob_mono (fun t ht => ?_)).trans
        ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
      simp only [List.ofFn_succ, List.ofFn_zero, nestedSpecial_enc, nestedSpecial_dec] at ht
      have hc := length_nestedInner hGE₁ n (t.1 1 (a 1)) o t.2.2
      have hp : (E₂ (pairEncode (List.ofFn (t.1 0 (a 0))) (List.ofFn t.2.1))).length =
          n + innerLen.eval n := by
        rw [hGE₂, List.length_ofFn]
        rfl
      rw [← hfirst, spDecStr_spEncStr E₂ List.length_ofFn hc List.length_ofFn hp,
        Option.bind_some] at ht
      exact Option.isSome_of_isSome_bind ht
    · sorry

end TCSlib.Cryptography.SecureComputation.GarblingCoins
