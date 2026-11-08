/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Signed Inner Product of Bit Strings

Bit strings of length `n` and their signed inner product: the unnormalised inner product
`⟨x, y⟩ = ∑ᵢ x'ᵢ y'ᵢ` of the `{±1}`-encodings `x'`, `y'` of `x`, `y` [OD14, §1.3 eq. (1.8)],
which counts agreeing coordinates as `+1` and disagreeing ones as `−1`. Its basic
identities relate it to the Hamming distance [GRS25, Def 1.3.3]: `⟨x, y⟩ = n − 2 d_H(x, y)`
(the unnormalised form of `⟨f, g⟩ = 1 − 2 dist(f, g)` in [OD14, §1.4]), and it is
additive under concatenation and scales linearly under repetition.

## Main definitions

- `CommunicationComplexity.BitString`: `n`-bit strings, as Boolean-valued functions on
  `Fin n`.
- `CommunicationComplexity.BitString.signedInner`: the signed inner product of two Boolean
  strings under the `{0,1}` to `{±1}` correspondence.
- `CommunicationComplexity.BitString.agreementCount`: the number of coordinates on which two
  bit strings agree.

## Main results

- `CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist`: the
  signed inner product equals the string length minus twice the Hamming distance.
- `CommunicationComplexity.BitString.signedInner_append`: the signed inner product is
  additive under concatenation.
- `CommunicationComplexity.BitString.signedInner_amplify`: repeating both inputs `a` times
  multiplies the signed inner product by `a`.

## References

* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
* [GRS25] V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft textbook,
  2025/26.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

/-- `n`-bit strings, represented as Boolean-valued functions on `Fin n`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

namespace BitString

open scoped BigOperators

/-- The signed inner product of two Boolean strings, viewed through the
usual `{0,1}` to `{±1}` correspondence. Each agreeing coordinate
contributes `1`, and each disagreeing coordinate contributes `-1`. This is the
unnormalised inner product `∑ᵢ x'ᵢ y'ᵢ` on the Hamming cube [OD14, §1.3 eq. (1.8)], i.e.
`n` times the expectation `⟨f, g⟩ = E[f(x) g(x)]` used there. -/
def signedInner {n : ℕ} (x y : CommunicationComplexity.BitString n) : ℤ :=
  ∑ i, if x i = y i then 1 else -1

/-- The number of coordinates on which two bit strings agree. -/
def agreementCount {n : ℕ} (x y : CommunicationComplexity.BitString n) : ℕ :=
  (Finset.univ.filter (fun i => x i = y i)).card

/-- The number of agreeing coordinates plus the number of disagreeing
coordinates is the total length of the strings. -/
theorem agreementCount_add_hammingDist_eq_length
    {n : ℕ} (x y : CommunicationComplexity.BitString n) :
    agreementCount x y + hammingDist x y = n := by
  classical
  simpa [agreementCount, hammingDist] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
      (p := fun i : Fin n => x i = y i))

/-- The number of agreeing coordinates is the total length minus the
Hamming distance. -/
theorem agreementCount_eq_length_sub_hammingDist
    {n : ℕ} (x y : CommunicationComplexity.BitString n) :
    (agreementCount x y : ℤ) = n - hammingDist x y := by
  have h :
      (agreementCount x y : ℤ) +
        (hammingDist x y : ℤ) = n := by
    exact_mod_cast agreementCount_add_hammingDist_eq_length x y
  linarith

/-- The signed inner product is the length minus twice the Hamming distance:
`⟨x, y⟩ = n − 2 d_H(x, y)`. This is the unnormalised form of `⟨f, g⟩ = 1 − 2 dist(f, g)`
[OD14, §1.4], with the Hamming distance in place of the relative distance. -/
theorem signedInner_eq_length_sub_twice_hammingDist
    {n : ℕ} (x y : CommunicationComplexity.BitString n) :
    signedInner x y = n - 2 * hammingDist x y := by
  classical
  unfold signedInner
  have hsplit :
      (∑ i : Fin n, if x i = y i then (1 : ℤ) else -1) =
        ∑ i : Fin n, ((1 : ℤ) - 2 * (if x i ≠ y i then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : x i = y i <;> simp [h]
  have hcount :
      (∑ i : Fin n, if x i ≠ y i then (1 : ℤ) else 0) = hammingDist x y := by
    have hcount_nat :
        (∑ i : Fin n, if x i ≠ y i then (1 : ℕ) else 0) = hammingDist x y := by
      simpa [hammingDist] using
        (Finset.card_filter (p := fun i : Fin n => x i ≠ y i) Finset.univ).symm
    exact_mod_cast hcount_nat
  rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
  simp [Finset.sum_const, Fintype.card_fin]

/-- The signed inner product is the number of agreeing coordinates minus the number of
disagreeing coordinates, i.e. `agreementCount x y − d_H(x, y)`; equivalently the
unnormalised form of `⟨f, g⟩ = Pr[f = g] − Pr[f ≠ g]` [OD14, §1.4]. -/
theorem signedInner_eq_agreementCount_sub_hammingDist
    {n : ℕ} (x y : CommunicationComplexity.BitString n) :
    signedInner x y = agreementCount x y - hammingDist x y := by
  rw [signedInner_eq_length_sub_twice_hammingDist,
    agreementCount_eq_length_sub_hammingDist]
  ring

/-- Concatenating two pairs of strings adds their signed inner products. -/
theorem signedInner_append {m n : ℕ}
    (x₁ : Fin m → Bool) (x₂ : Fin n → Bool)
    (y₁ : Fin m → Bool) (y₂ : Fin n → Bool) :
    signedInner (Fin.append x₁ x₂) (Fin.append y₁ y₂) =
      signedInner x₁ y₁ + signedInner x₂ y₂ := by
  unfold signedInner
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp
  · apply Finset.sum_congr rfl
    intro i hi
    simp

/-- Reindexing both inputs along a `Fin.cast` does not change the signed
inner product. -/
theorem signedInner_comp_cast {m n : ℕ} (h : m = n)
    (x y : Fin n → Bool) :
    signedInner (x ∘ Fin.cast h) (y ∘ Fin.cast h) = signedInner x y := by
  subst h
  simp [signedInner]

/-- Repeating both inputs `a` times multiplies the signed inner product
by `a`. -/
theorem signedInner_amplify {a n : ℕ} (x y : CommunicationComplexity.BitString n) :
    signedInner (Fin.repeat a x) (Fin.repeat a y) = a * signedInner x y := by
  induction a with
  | zero =>
      rw [Fin.repeat_zero, Fin.repeat_zero]
      rw [signedInner_comp_cast (Nat.zero_mul n), signedInner]
      simp
  | succ a ih =>
      rw [Fin.repeat_succ x a, Fin.repeat_succ y a]
      rw [signedInner_comp_cast, signedInner_append, ih]
      simp [add_mul, add_comm]

end BitString

end CommunicationComplexity
