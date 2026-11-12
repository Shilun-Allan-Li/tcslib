import Mathlib.Analysis.SpecialFunctions.Sqrt
import TCSlib.BooleanAnalysis.ThresholdFunctions.Polynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Total influence of linear threshold functions

This file develops the discrete-derivative toolkit needed for Peres's theorem and uses it to prove
that every linear threshold function on `n` variables has total influence at most `sqrt n`.

The argument is the classical one recalled in O'Donnell's Chapter 5: a linear threshold function is
*unate*, i.e. its discrete derivative in each direction has a constant sign; hence its influence in
direction `i` equals `|f̂({i})|`, and Cauchy-Schwarz together with Parseval bounds the sum of these
by `sqrt n`.

## Main definitions

* `affinePoly`: the multilinear polynomial with prescribed constant and degree-one coefficients.

## Main results

* `influence_eq_abs_fourierCoeff_of_sign`: the unate influence formula `Inf_i[f] = |f̂({i})|`.
* `IsLinearThreshold.exists_affine`: every LTF is the sign of an affine form in the `±1` variables.
* `ltf_totalInfluence_le_sqrt`: `I[f] ≤ sqrt n` for every linear threshold function.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §2.2 and §5.5.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

variable {n : ℕ}

/-! ## Discrete derivative toolkit -/

/-- Setting coordinate `i` of `x` to `b` either leaves `x` unchanged or flips its `i`-th bit. -/
private lemma update_eq_ite_flipBit (x : BoolCube n) (i : Fin n) (b : Bool) :
    Function.update x i b = if x i = b then x else flipBit x i := by
  split_ifs with h
  · rw [← h, Function.update_eq_self]
  · rw [flipBit, show b = !x i by cases b <;> simp_all]

/-- The discrete derivative written through a single bit flip.

[OD14, §2.2] -/
lemma derivative_eq_flipBit (i : Fin n) (f : BooleanFunc n) (x : BoolCube n) :
    derivative i f x = (f x - f (flipBit x i)) / 2 * boolToSign (x i) := by
  cases hx : x i <;> simp [derivative, update_eq_ite_flipBit, hx]
  ring

/-- Influence as the mean square of the discrete derivative.

[OD14, §2.2] -/
lemma influence_eq_expect_derivative_sq (i : Fin n) (f : BooleanFunc n) :
    influence i f = expect (fun x ↦ derivative i f x ^ 2) := by
  unfold influence
  congr 1
  funext x
  rw [derivative_eq_flipBit, mul_pow, boolToSign_sq, mul_one, div_pow]
  norm_num

/-- Averaging a coordinate does not change the expectation. -/
lemma expect_expectationOperator (i : Fin n) (g : BooleanFunc n) :
    expect (expectationOperator i g) = expect g := by
  have key (x : BoolCube n) : expectationOperator i g x = (g x + g (flipBit x i)) / 2 := by
    cases hx : x i <;> simp [expectationOperator, update_eq_ite_flipBit, hx]
    ring
  have hflip : ∑ x : BoolCube n, g (flipBit x i) = ∑ x : BoolCube n, g x :=
    Equiv.sum_comp
      (Function.Involutive.toPerm (fun x ↦ flipBit x i) (fun x ↦ flipBit_flipBit x i)) g
  simp only [expect, key, ← Finset.sum_div, Finset.sum_add_distrib, hflip]
  ring

/-- The degree-one Fourier coefficient is the mean of the discrete derivative.

[OD14, §2.2] -/
lemma fourierCoeff_singleton_eq_expect_derivative (i : Fin n) (f : BooleanFunc n) :
    fourierCoeff f {i} = expect (derivative i f) := by
  have h : derivative i f = expectationOperator i (fun x ↦ f x * boolToSign (x i)) := by
    funext x
    simp [derivative, expectationOperator]
    ring
  rw [h, expect_expectationOperator]
  simp [fourierCoeff, innerProduct]

/-- For a `±1`-valued function the discrete derivative takes values in `{-1, 0, 1}`, so its square
coincides with its absolute value. -/
lemma derivative_sq_eq_abs_of_pmOne {f : BooleanFunc n} (hf : isPmOne f) (i : Fin n)
    (x : BoolCube n) : derivative i f x ^ 2 = |derivative i f x| := by
  unfold derivative
  rcases hf (Function.update x i false) with h1 | h1 <;>
    rcases hf (Function.update x i true) with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- **Unate influence formula.** If `f` is `±1`-valued and its discrete derivative in direction `i`
has a constant sign, then `Inf_i[f] = |f̂({i})|`.

[OD14, §2.2]

**Proof sketch.** The influence is the mean square of the derivative, which for `±1`-valued
functions is the mean absolute value of the derivative. If the derivative has constant sign, the
mean absolute value is the absolute value of the mean, and the mean of the derivative is the
singleton Fourier coefficient. -/
lemma influence_eq_abs_fourierCoeff_of_sign {f : BooleanFunc n} (hf : isPmOne f) (i : Fin n)
    (hsign : (∀ x, 0 ≤ derivative i f x) ∨ (∀ x, derivative i f x ≤ 0)) :
    influence i f = |fourierCoeff f {i}| := by
  rw [influence_eq_expect_derivative_sq, fourierCoeff_singleton_eq_expect_derivative]
  simp_rw [derivative_sq_eq_abs_of_pmOne hf i]
  rcases hsign with h | h
  · simp_rw [abs_of_nonneg (h _)]
    exact (abs_of_nonneg (expect_nonneg h)).symm
  · simp_rw [abs_of_nonpos (h _)]
    rw [expect_neg, abs_of_nonpos]
    simpa [expect_neg] using expect_nonneg fun x ↦ neg_nonneg.mpr (h x)

/-! ## Affine multilinear polynomials -/

/-- The multilinear polynomial with constant term `c` and degree-one coefficients `a`. -/
noncomputable def affinePoly (c : ℝ) (a : Fin n → ℝ) : MultilinearPolynomial n :=
  fun S ↦ if S = ∅ then c else ∑ i : Fin n, if S = {i} then a i else 0

/-- The constant coefficient of `affinePoly c a` is `c`. -/
@[simp]
lemma affinePoly_empty (c : ℝ) (a : Fin n → ℝ) : affinePoly c a ∅ = c := by simp [affinePoly]

/-- The coefficient of `x_i` in `affinePoly c a` is `a i`. -/
@[simp]
lemma affinePoly_singleton (c : ℝ) (a : Fin n → ℝ) (i : Fin n) : affinePoly c a {i} = a i := by
  simp [affinePoly, Finset.singleton_ne_empty]

/-- `affinePoly c a` has degree at most one. -/
lemma affinePoly_hasDegreeAtMost_one (c : ℝ) (a : Fin n → ℝ) :
    (affinePoly c a).HasDegreeAtMost 1 := by
  intro S hS
  have h0 : S ≠ ∅ := by rintro rfl; simp at hS
  have h1 : ∀ i : Fin n, ¬ (S = {i}) := by
    intro i h; rw [h] at hS; simp at hS
  simp [affinePoly, h0, h1]

/-! ## Linear threshold functions as signs of affine forms -/

/-- Every linear threshold function is the sign of an affine form in the `±1` variables.

[OD14, §5.1, Eq. (5.1)] -/
lemma IsLinearThreshold.exists_affine {f : BooleanFunc n} (hf : IsLinearThreshold f) :
    ∃ (c : ℝ) (a : Fin n → ℝ),
      f = fun x ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i)) := by
  obtain ⟨p, hdeg, hrep⟩ := hf
  refine ⟨p ∅, fun i ↦ p {i}, ?_⟩
  rw [← hrep]
  funext x
  simp [MultilinearPolynomial.threshold, MultilinearPolynomial.eval_of_degree_le_one hdeg]

/-- Conversely, the sign of an affine form is a linear threshold function. -/
lemma isLinearThreshold_affine (c : ℝ) (a : Fin n → ℝ) :
    IsLinearThreshold (fun x ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i))) := by
  refine ⟨affinePoly c a, affinePoly_hasDegreeAtMost_one c a, ?_⟩
  funext x
  simp [MultilinearPolynomial.threshold,
    MultilinearPolynomial.eval_of_degree_le_one (affinePoly_hasDegreeAtMost_one c a)]

/-- Freezing coordinate `i` of an affine form splits off its `i`-th term. -/
lemma affine_form_update (c : ℝ) (a : Fin n → ℝ) (i : Fin n) (x : BoolCube n) (b : Bool) :
    c + ∑ j : Fin n, a j * boolToSign (Function.update x i b j)
      = (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)) + a i * boolToSign b := by
  have h : ∀ j ∈ Finset.univ.erase i,
      a j * boolToSign (Function.update x i b j) = a j * boolToSign (x j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Finset.sum_congr rfl h,
    Function.update_self]
  ring

/-- **Unateness of linear threshold functions**: the discrete derivative of the sign of an affine
form has the constant sign of the corresponding coefficient.

[OD14, §5.5] -/
lemma derivative_affine_threshold_sign (c : ℝ) (a : Fin n → ℝ) (i : Fin n) :
    (∀ x, 0 ≤ derivative i (fun y ↦ thresholdSign (c + ∑ j : Fin n, a j * boolToSign (y j))) x) ∨
      (∀ x, derivative i (fun y ↦ thresholdSign (c + ∑ j : Fin n, a j * boolToSign (y j))) x
        ≤ 0) := by
  simp only [derivative, affine_form_update, boolToSign_false, boolToSign_true, mul_one,
    mul_neg_one]
  rcases le_or_gt 0 (a i) with ha | ha
  · refine Or.inl fun x ↦ ?_
    linarith [thresholdSign_mono (add_le_add_left (neg_le_self ha)
      (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)))]
  · refine Or.inr fun x ↦ ?_
    linarith [thresholdSign_mono (add_le_add_left (le_neg_self_iff.mpr ha.le)
      (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)))]

/-! ## The total influence bound -/

/-- A `±1`-valued function has total degree-one Fourier weight at most one (Parseval). -/
lemma sum_singleton_fourier_sq_le_one {f : BooleanFunc n} (hf : isPmOne f) :
    ∑ i : Fin n, fourierCoeff f {i} ^ 2 ≤ 1 := by
  classical
  rw [← Finset.sum_image (f := fun S ↦ fourierCoeff f S ^ 2)
    (fun i _ j _ h ↦ Finset.singleton_injective h), ← parseval_pm_one f hf]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun S _ _ ↦ sq_nonneg _

/-- **Every linear threshold function has total influence at most `sqrt n`.**

[OD14, §5.5, proof of Peres's Theorem]

**Proof sketch.** Linear threshold functions are unate, so each influence equals `|f̂({i})|`.
Cauchy-Schwarz bounds the sum of these by `sqrt n` times the square root of the degree-one
weight, which is at most one by Parseval. -/
theorem ltf_totalInfluence_le_sqrt {f : BooleanFunc n} (hf : IsLinearThreshold f) :
    totalInfluence f ≤ Real.sqrt n := by
  obtain ⟨c, a, rfl⟩ := hf.exists_affine
  set g : BooleanFunc n := fun x ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i))
  have hpm : isPmOne g := isPmOne_thresholdSign _
  calc totalInfluence g = ∑ i : Fin n, |fourierCoeff g {i}| * 1 := by
        simp only [totalInfluence, mul_one]
        exact Finset.sum_congr rfl fun i _ ↦
          influence_eq_abs_fourierCoeff_of_sign hpm i (derivative_affine_threshold_sign c a i)
    _ ≤ Real.sqrt (∑ i : Fin n, |fourierCoeff g {i}| ^ 2) *
          Real.sqrt (∑ _i : Fin n, (1 : ℝ) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ Real.sqrt 1 * Real.sqrt n := by
        simp only [sq_abs, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        gcongr
        exact sum_singleton_fourier_sq_le_one hpm
    _ = Real.sqrt n := by rw [Real.sqrt_one, one_mul]

end ThresholdFunctions
end BooleanAnalysis
