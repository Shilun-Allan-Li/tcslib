/-
Copyright (c) 2026 Prastik Mohanraj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prastik Mohanraj
-/

import TCSlib.BooleanAnalysis.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset BooleanAnalysis

namespace BoolFourier

/-!
# BoolFourier

Fourier analysis on the Boolean hypercube, built on top of `TCSlib.BooleanAnalysis.Basic`.

Type aliases and analysis operators follow `BooleanAnalysis` naming. BLR-specific objects
(`xor_vec`, `zero_vec`, `convolution`) are defined here.

## Main results

- `card_hypercube`: The Boolean hypercube `Fin n → Bool` has cardinality `2 ^ n`.
- `BoolToPM1_xor`: XOR in `Bool` corresponds to multiplication in `{±1} ⊂ ℝ`.
- `char_S_times_char_T`: Product of two Fourier characters equals the character at the symmetric difference.
- `inner_product_char_self` / `inner_product_char_nonself`: Orthonormality of characters.
- `fourier_expansion`: Every Boolean function expands in the Fourier–Walsh basis.
- `parseval_identity`: Sum of squared Fourier coefficients equals the squared L² norm.
- `fourier_coeff_convolution`: Fourier coefficient of a convolution is the product of coefficients.
-/

-- ============================================================================
-- SECTION 1: HYPERCUBE
-- ----------------------------------------------------------------------------
-- Type aliases pointing to BooleanAnalysis, plus BLR-specific group structure.
-- ============================================================================
section HYPERCUBE

-- Thin aliases over TCSlib BooleanAnalysis types
abbrev hypercube (n : ℕ) := BoolCube n
abbrev BoolFun (n : ℕ)   := BooleanFunc n

-- Bool → {±1} embedding (alias for BooleanAnalysis.boolToSign)
abbrev BoolToPM1 : Bool → ℝ := boolToSign

-- Partial inverse of BoolToPM1
noncomputable def PM1ToBool? : ℝ → Option Bool
  | x => if x = -1 then some true else if x = 1 then some false else none

-- All-zeros vector (additive identity of F₂ⁿ)
def zero_vec (n : ℕ) : hypercube n := fun _ => false

-- Pointwise XOR (group operation on F₂ⁿ)
def xor_vec {n : ℕ} (x y : hypercube n) : hypercube n :=
  fun i => Bool.xor (x i) (y i)

lemma card_hypercube (n : ℕ) : Fintype.card (hypercube n) = 2 ^ n := by
  simp [hypercube, BoolCube, Fintype.card_pi]

-- BoolToPM1 properties (delegated to BooleanAnalysis)
lemma avg_BoolToPM1 : (BoolToPM1 false + BoolToPM1 true) / 2 = 0 := by
  simp [BoolToPM1, boolToSign]

lemma BoolToPM1_sq (b : Bool) : BoolToPM1 b * BoolToPM1 b = 1 :=
  boolToSign_mul_self b

lemma BoolToPM1_not (b : Bool) : BoolToPM1 (!b) = -BoolToPM1 b :=
  boolToSign_not b

lemma BoolToPM1_xor (a b : Bool) :
    BoolToPM1 (Bool.xor a b) = BoolToPM1 a * BoolToPM1 b := by
  cases a <;> cases b <;> simp [BoolToPM1, boolToSign, Bool.xor]

end HYPERCUBE

-- ============================================================================
-- SECTION 2: BOOLEAN_FUNCTION
-- ----------------------------------------------------------------------------
-- Analysis operators. `expectation` keeps the `(∑ f) / 2^n` form so that
-- downstream proofs in BoolBLR / LowDegree continue to work unchanged.
-- ============================================================================
section BOOLEAN_FUNCTION

-- E[f] = (∑_x f(x)) / 2^n
noncomputable def expectation {n : ℕ} (f : BoolFun n) : ℝ :=
  (Finset.sum Finset.univ fun x => f x) / (2 : ℝ) ^ n

-- E[∏_i g_i(x_i)] = ∏_i (g_i(false) + g_i(true)) / 2
lemma expectation_factorizes {n : ℕ} (g : Fin n → Bool → ℝ) :
    expectation (fun x : hypercube n => ∏ i, g i (x i))
    = ∏ i, ((g i false + g i true) / 2) := by
  unfold expectation
  simp +decide [Finset.prod_add, Finset.prod_div_distrib]
  refine' Finset.sum_bij (fun x _ => Finset.univ.filter fun i => x i = false) _ _ _ _ <;>
      simp +decide [Finset.ext_iff]
  · exact fun a₁ a₂ h => funext h
  · exact fun b => ⟨fun i => if i ∈ b then false else true, fun i => by aesop⟩
  · intro a
    rw [← Finset.prod_sdiff (Finset.filter_subset (fun i => a i = false) Finset.univ)]
    simp +decide [Finset.prod_filter]
    rw [mul_comm]
    exact congrArg₂ _ (Finset.prod_congr rfl fun i hi => by aesop)
                      (Finset.prod_congr rfl fun i hi => by aesop)

-- ⟨f, g⟩ = E[f · g]
noncomputable def inner_product {n : ℕ} (f g : BoolFun n) : ℝ :=
  expectation (fun x => f x * g x)

-- ‖f‖₂² = E[f²]
noncomputable def L2_norm_sq {n : ℕ} (f : BoolFun n) : ℝ :=
  expectation (fun x => f x ^ 2)

-- (f * g)(x) = E_y[f(y) g(x ⊕ y)]
noncomputable def convolution {n : ℕ} (f g : BoolFun n) : BoolFun n :=
  fun x => expectation (fun y => f y * g (xor_vec x y))

end BOOLEAN_FUNCTION

-- ============================================================================
-- SECTION 3: CHARACTERS
-- ----------------------------------------------------------------------------
-- Walsh characters alias BooleanAnalysis.chiS; proofs delegate to Basic.
-- ============================================================================
section CHARACTERS

-- χ_S(x) = ∏_{i∈S} (-1)^{x_i}  — alias for BooleanAnalysis.chiS
noncomputable abbrev char_S {n : ℕ} (S : Finset (Fin n)) : BoolFun n := chiS S

lemma char_S_of_zero (n : ℕ) (S : Finset (Fin n)) : char_S S (zero_vec n) = 1 := by
  simp [chiS, zero_vec, boolToSign]

private lemma char_S_sq_aux_h (n : Nat) (S : Finset (Fin n)) (x : hypercube n) : χ_[S] x ^ 2 = 1 :=
  chiS_sq_eq_one S x

lemma char_S_sq (n : ℕ) (S : Finset (Fin n)) (x : hypercube n) :
    char_S S x * char_S S x = 1 := by
  let h : χ_[S] x ^ 2 = 1 := (char_S_sq_aux_h n S x)
  rw [sq] at h; exact h
lemma char_S_empty (n : ℕ) : char_S (∅ : Finset (Fin n)) = fun _ => 1 :=
  chiS_empty

-- χ_S · χ_T = χ_{S △ T}  (uses Mathlib's symmDiff via BooleanAnalysis.chiS_mul_chiS)
lemma char_S_times_char_T {n : ℕ} (S T : Finset (Fin n)) (x : hypercube n) :
    char_S S x * char_S T x = char_S (symmDiff S T) x :=
  chiS_mul_chiS S T x

-- ∑_S χ_S(0,...,0) = 2^n
private lemma sum_char_S_at_zero_aux_h {n : Nat} : (fun S => char_S S (zero_vec n)) = fun _ => 1 :=
  funext fun S => char_S_of_zero n S

lemma sum_char_S_at_zero {n : ℕ} :
    ∑ S : Finset (Fin n), char_S S (zero_vec n) = (Fintype.card (hypercube n) : ℝ) := by
  simp [(sum_char_S_at_zero_aux_h)]

-- ∑_S χ_S(x) = 0 for x ≠ 0
private lemma sum_char_S_ne_zero_aux_h_pair {n : Nat} {x : hypercube n} (hx : x ≠ zero_vec n) (i : Fin n) (hi : x i = true) :
  ∑ S, char_S S x = ∑ S, -char_S S x := by
  apply Finset.sum_bij (fun S _ => if i ∈ S then S \ {i} else S ∪ {i})
  · grind
  · intro a₁ _ a₂ _ h
    split_ifs at h <;> simp_all +decide [Finset.ext_iff] <;> grind
  · grind
  · intro S _
    split_ifs <;> simp_all +decide [chiS]
    · rw [Finset.prod_eq_prod_diff_singleton_mul ‹i ∈ S›]
      simp +decide [hi, boolToSign]

lemma sum_char_S_ne_zero {n : ℕ} {x : hypercube n} (hx : x ≠ zero_vec n) :
    ∑ S : Finset (Fin n), char_S S x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i = true :=
    not_forall_not.mp fun h => hx (funext fun i => by simpa using h i)
  let h_pair : ∑ S : Finset (Fin n), char_S S x = ∑ S : Finset (Fin n), -char_S S x := (sum_char_S_ne_zero_aux_h_pair hx i hi)
  rw [Finset.sum_neg_distrib] at h_pair; linarith

-- E[χ_∅] = 1
lemma expectation_char_empty (n : ℕ) :
    expectation (char_S (∅ : Finset (Fin n))) = 1 := by
  simp [expectation]

-- E[χ_S] = 0 for S ≠ ∅
private lemma expectation_char_nonempty_aux_h_exp {n : Nat} {S : Finset (Fin n)} (_hS : S.Nonempty) :
  expectation (char_S S) = ∏ _j ∈ S, (BoolToPM1 false + BoolToPM1 true) / 2 := by
  convert expectation_factorizes _ using 1
  any_goals exact fun i b => if i ∈ S then BoolToPM1 b else 1
  · exact congr_arg _ (funext fun x => by rw [← Finset.prod_filter]; congr; ext; aesop)
  · rw [← Finset.prod_subset (Finset.subset_univ S)] <;> aesop

lemma expectation_char_nonempty {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    expectation (char_S S) = 0 := by
  simp [(expectation_char_nonempty_aux_h_exp hS), Finset.Nonempty.ne_empty hS]

-- ⟨χ_S, χ_S⟩ = 1
lemma inner_product_char_self {n : ℕ} (S : Finset (Fin n)) :
    inner_product (char_S S) (char_S S) = 1 := by
  simp [inner_product,
        show (fun x => char_S S x * char_S S x) = fun _ => (1 : ℝ) from
          funext fun x => char_S_sq n S x,
        expectation]

-- ⟨χ_S, χ_T⟩ = 0 for S ≠ T
lemma inner_product_char_nonself {n : ℕ} {S T : Finset (Fin n)} (hST : S ≠ T) :
    inner_product (char_S S) (char_S T) = 0 := by
  unfold inner_product
  simp only [show (fun x => char_S S x * char_S T x) = fun x => char_S (symmDiff S T) x from
    funext fun x => char_S_times_char_T S T x]
  exact expectation_char_nonempty (Finset.symmDiff_nonempty.mpr hST)

end CHARACTERS

-- ============================================================================
-- SECTION 4: FOURIER_COEFFICIENTS
-- ============================================================================
section FOURIER_COEFFICIENTS

-- f̂(S) = ⟨f, χ_S⟩
noncomputable def fourier_coeff {n : ℕ} (f : BoolFun n) (S : Finset (Fin n)) : ℝ :=
  inner_product f (char_S S)

lemma fourier_coeff_char_self {n : ℕ} (S : Finset (Fin n)) :
    fourier_coeff (char_S S) S = 1 := inner_product_char_self S

lemma fourier_coeff_char_of_ne {n : ℕ} {S T : Finset (Fin n)} (hST : S ≠ T) :
    fourier_coeff (char_S S) T = 0 := inner_product_char_nonself hST

-- Bridge: BoolFourier.expectation ↔ BooleanAnalysis.expect
private lemma expectation_eq_expect {n : ℕ} (f : BoolFun n) :
    expectation f = expect f := by
  unfold expectation BooleanAnalysis.expect BooleanAnalysis.uniformWeight
  rw [div_eq_mul_inv, ← inv_pow, mul_comm]

-- Bridge: BoolFourier.fourier_coeff ↔ BooleanAnalysis.fourierCoeff
private lemma fourier_coeff_eq {n : ℕ} (f : BoolFun n) (S : Finset (Fin n)) :
    fourier_coeff f S = fourierCoeff f S := by
  unfold fourier_coeff inner_product BooleanAnalysis.fourierCoeff BooleanAnalysis.innerProduct
  exact expectation_eq_expect _

-- f(x) = ∑_S f̂(S) χ_S(x)
lemma fourier_expansion {n : ℕ} (f : BoolFun n) (x : hypercube n) :
    f x = ∑ S : Finset (Fin n), fourier_coeff f S * char_S S x := by
  simp_rw [fourier_coeff_eq]
  exact walsh_expansion f x

-- ∑_S f̂(S)² = ‖f‖₂²
private lemma parseval_identity_aux_hL2 {n : Nat} (f : BoolFun n) : L2_norm_sq f = ⟪f, f⟫_𝔹 := by
  unfold L2_norm_sq BooleanAnalysis.innerProduct
  rw [expectation_eq_expect]
  congr 1; funext x; ring

lemma parseval_identity {n : ℕ} (f : BoolFun n) :
    ∑ S : Finset (Fin n), (fourier_coeff f S) ^ 2 = L2_norm_sq f := by
  simp_rw [fourier_coeff_eq]
  rw [(parseval_identity_aux_hL2 f), ← parseval]

-- (f * g)̂(S) = f̂(S) · ĝ(S)
private lemma fourier_coeff_convolution_aux_h_fubini {n : Nat} (f g : BoolFun n) (S : Finset (Fin n)) :
  ∑ x, (∑ y, f y * g (xor_vec x y)) * char_S S x = ∑ y, f y * ∑ x, g (xor_vec x y) * char_S S x := by
  simpa only [Finset.mul_sum _ _ _, mul_assoc, Finset.sum_mul] using Finset.sum_comm

private lemma fourier_coeff_convolution_aux_h_split {n : Nat} (f g : BoolFun n) (S : Finset (Fin n))
  (_h_fubini : ∑ x, (∑ y, f y * g (xor_vec x y)) * char_S S x = ∑ y, f y * ∑ x, g (xor_vec x y) * char_S S x)
  (y x : hypercube n) : char_S S x = char_S S (xor_vec x y) * char_S S y := by
  simp [chiS, ← Finset.prod_mul_distrib]
  congr 1; ext i; simp [xor_vec, boolToSign, Bool.xor]
  cases x i <;> cases y i <;> simp

private lemma fourier_coeff_convolution_aux_h_char {n : Nat} (f g : BoolFun n) (S : Finset (Fin n))
  (h_fubini : ∑ x, (∑ y, f y * g (xor_vec x y)) * char_S S x = ∑ y, f y * ∑ x, g (xor_vec x y) * char_S S x)
  (y : hypercube n) : ∑ x, g (xor_vec x y) * char_S S x = char_S S y * ∑ x, g x * char_S S x := by
  rw [Finset.mul_sum _ _ _]
  apply Finset.sum_bij (fun x _ => xor_vec x y)
  · exact fun _ _ => Finset.mem_univ _
  · unfold xor_vec; simp +decide
    exact fun a₁ a₂ h => funext fun i => by
      by_cases hi : y i <;> simpa [hi] using (congr_fun h i)
  · intro b _
    exact ⟨xor_vec b y, Finset.mem_univ _,
           funext fun i => by simp [xor_vec]⟩
  · exact fun x _ => by rw [(fourier_coeff_convolution_aux_h_split f g S h_fubini y) x]; ring

lemma fourier_coeff_convolution {n : ℕ} (f g : BoolFun n) (S : Finset (Fin n)) :
    fourier_coeff (convolution f g) S = fourier_coeff f S * fourier_coeff g S := by
  classical
  let h_char : ∀ y : hypercube n, ∑ x : hypercube n, g (xor_vec x y) * char_S S x = char_S S y * ∑ x : hypercube n, g x * char_S S x := (fourier_coeff_convolution_aux_h_char f g S (fourier_coeff_convolution_aux_h_fubini f g S))
  unfold convolution fourier_coeff inner_product expectation
  simp_all +decide [div_mul_eq_mul_div, ← Finset.sum_div, (fourier_coeff_convolution_aux_h_fubini f g S)]
  simp +decide only [← mul_assoc, ← Finset.sum_mul]; ring

end FOURIER_COEFFICIENTS

end BoolFourier
