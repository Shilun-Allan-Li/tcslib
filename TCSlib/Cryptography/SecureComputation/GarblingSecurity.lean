/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.NestedBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits from PRFs: Claim 159.a

[PS10, §6.2.2–6.2.3]: with the nested special encryption of `GarblingSpecial.lean`, built from two
pseudorandom function families (`PRFOut`), a random garbling is good with high probability. This
combines Claim 157.a's wrong-key property (here for the nesting) with the union bound of
`Garbling.lean`.

## Main definitions

The imported `SecureComputation.nestedSpecial` construction uses the correctness and
wrong-key contracts `MultiEnc.DecCorrect` and `MultiEnc.WrongKeyBot` from `Garbling.lean`.

## Main results

* `SecureComputation.nestedSpecial_wrongKeyBot` (Claim 157.a (ii) for the nesting): the
  wrong-key error is negligible.
* `SecureComputation.garbling_good_whp` (Claim 159.a, proved from the previous results): a random
  garbling of a fan-in-two circuit is good except with probability `12 · |gates| · δ(n)`, `δ`
  negligible.

## Contents

* `GarblingSecurity.CoinMarginals`: independent key/nonce marginals and option probabilities.
* `GarblingSecurity.NestedBounds`: the three concrete nesting cases.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Claim 157.a (ii) for the nesting: the wrong-key property with negligible error**
[PS10, §6.2.2]: for length-doubling `G₁` and `G₂` with `n + (4n + 2)`-bit outputs, both PRFs,
nested special encryption has `WrongKeyBot` with a negligible error `δ(n)`.

**Proof sketch.** Let `a ≠ a'` be the key choices on at most two positions.
- **One position:** the ciphertext under `k_a` is decrypted under the independent `k_{a'}`, which
  is `spDecStr_wrongKey` at `ℓ = n`: error `ε₁(n)`.
- **Two positions, first differs:** the outer layer is decrypted under an independent key, which
  is `spDecStr_wrongKey` at `ℓ = 4n + 2`: error `ε₂(n)`.
- **Two positions, first agrees, second differs:** the outer layer opens to the inner ciphertext,
  which is decrypted under an independent key: error `ε₁(n)`.

So `δ = ε₁ + ε₂`, negligible (`Negligible.add`); `ε₁` and `ε₂` are averaged over the plaintext
and the other layer's key and coins. In the proof, `spDecStr_wrongKey` at `ℓ = n` (with `G₁`)
and at `ℓ = innerLen` (with `G₂`) gives the two string success bounds
(`GarblingCoins.uprob_isSome_lt_of_none`), and
`GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds` carries out the case analysis,
including the zero-position case, which has no distinct choices. -/
theorem nestedSpecial_wrongKeyBot (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n) := by
  obtain ⟨ε₁, hε₁, hb₁⟩ := spDecStr_wrongKey .var G₁ E₁ hGE₁ hG₁
  simp only [PolyExpr.eval_var] at hb₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := spDecStr_wrongKey innerLen G₂ E₂ hGE₂ hG₂
  refine ⟨fun n => ε₁ n + ε₂ n, hε₁.add hε₂, fun n => ?_⟩
  have hs₁ : ∀ m : Fin n → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁ n :=
    fun m => (GarblingCoins.uprob_isSome_lt_of_none _ (hb₁ n m)).le
  have hs₂ : ∀ m : Fin (innerLen.eval n) → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂ n :=
    fun m => (GarblingCoins.uprob_isSome_lt_of_none _ (hb₂ n m)).le
  have hε₁n : 0 ≤ ε₁ n := (uprob_nonneg _).trans (hs₁ (fun _ => false))
  have hε₂n : 0 ≤ ε₂ n := (uprob_nonneg _).trans (hs₂ (fun _ => false))
  exact GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds G₁ G₂ E₁ E₂
    hGE₁ hGE₂ n hε₁n hε₂n hs₁ hs₂

include hGE₁ hGE₂ in
/-- **Claim 159.a: a random garbling is good with high probability** [PS10, §6.2.3, "all but one
row will evaluate to `⊥`"]: with the nested special encryption from two PRFs, there is a
negligible `δ` such that, for every parameter `n` and every fan-in-two circuit, a uniformly
random garbling is good, and so evaluates correctly (`garbledOutput_eq`), except with
probability at most `12 · |gates| · δ(n)`. Goodness here concerns the first successful opening
for every assignment; the stronger source assertion of unique opening is not this conclusion. -/
theorem garbling_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ (n m : ℕ) (Cc : DAGCircuit m), Cc.IsFaninTwo →
      uprob (fun s : GarbleSeed Cc (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) =>
        ¬ Good (nestedSpecial E₁ E₂ n) Cc s) ≤ 12 * Cc.gates.length * δ n := by
  obtain ⟨δ, hδ, hbot⟩ := nestedSpecial_wrongKeyBot G₁ G₂ E₁ E₂ hGE₁ hGE₂ hG₁ hG₂
  exact ⟨δ, hδ, fun n m Cc hC => uprob_not_good_le (nestedSpecial E₁ E₂ n) Cc
    (nestedSpecial_decCorrect G₁ G₂ E₁ E₂ hGE₁ hGE₂ n) (hbot n) hC⟩

end TCSlib.Cryptography.SecureComputation
