import Mathlib.Analysis.SpecialFunctions.Sqrt
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

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

/-- The discrete derivative written through a single bit flip.

[OD14, §2.2] -/
lemma derivative_eq_flipBit (i : Fin n) (f : BooleanFunc n) (x : BoolCube n) :
    derivative i f x = (f x - f (flipBit x i)) / 2 * boolToSign (x i) := by
  cases hx : x i with
  | false =>
      have h1 : Function.update x i false = x := by
        conv_rhs => rw [← Function.update_eq_self i x]; rw [hx]
      have h2 : Function.update x i true = flipBit x i := by simp [flipBit, hx]
      simp [derivative, h1, h2]
  | true =>
      have h1 : Function.update x i true = x := by
        conv_rhs => rw [← Function.update_eq_self i x]; rw [hx]
      have h2 : Function.update x i false = flipBit x i := by simp [flipBit, hx]
      simp [derivative, h1, h2]
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
  have key : ∀ x : BoolCube n, expectationOperator i g x = (g x + g (flipBit x i)) / 2 := by
    intro x
    cases hx : x i with
    | false =>
        have h1 : Function.update x i false = x := by
          conv_rhs => rw [← Function.update_eq_self i x]; rw [hx]
        have h2 : Function.update x i true = flipBit x i := by simp [flipBit, hx]
        simp [expectationOperator, h1, h2]
    | true =>
        have h1 : Function.update x i true = x := by
          conv_rhs => rw [← Function.update_eq_self i x]; rw [hx]
        have h2 : Function.update x i false = flipBit x i := by simp [flipBit, hx]
        rw [expectationOperator, h1, h2]
        ring
  have hsum : ∑ x : BoolCube n, g (flipBit x i) = ∑ x : BoolCube n, g x :=
    Equiv.sum_comp
      (Function.Involutive.toPerm (fun x ↦ flipBit x i) (fun x ↦ flipBit_flipBit x i)) g
  simp only [expect, key]
  rw [show (∑ x : BoolCube n, (g x + g (flipBit x i)) / 2)
      = (∑ x : BoolCube n, g x + ∑ x : BoolCube n, g (flipBit x i)) / 2 by
    rw [← Finset.sum_add_distrib, Finset.sum_div]]
  rw [hsum]
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
  have h1 := hf (Function.update x i false)
  have h2 := hf (Function.update x i true)
  unfold derivative
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- **Unate influence formula.** If `f` is `±1`-valued and its discrete derivative in direction `i`
has a constant sign, then `Inf_i[f] = |f̂({i})|`.

[OD14, §2.2] -/
lemma influence_eq_abs_fourierCoeff_of_sign {f : BooleanFunc n} (hf : isPmOne f) (i : Fin n)
    (hsign : (∀ x, 0 ≤ derivative i f x) ∨ (∀ x, derivative i f x ≤ 0)) :
    influence i f = |fourierCoeff f {i}| := by
  rw [influence_eq_expect_derivative_sq]
  have habs : (fun x ↦ derivative i f x ^ 2) = fun x ↦ |derivative i f x| := by
    funext x; exact derivative_sq_eq_abs_of_pmOne hf i x
  rw [habs, fourierCoeff_singleton_eq_expect_derivative]
  rcases hsign with h | h
  · have hEq : (fun x ↦ |derivative i f x|) = derivative i f := by
      funext x; exact abs_of_nonneg (h x)
    have hnonneg : 0 ≤ expect (derivative i f) := by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ h x
    rw [hEq, abs_of_nonneg hnonneg]
  · have hEq : (fun x ↦ |derivative i f x|) = fun x ↦ -derivative i f x := by
      funext x; exact abs_of_nonpos (h x)
    have hneg : expect (fun x ↦ -derivative i f x) = -expect (derivative i f) := by
      calc
        expect (fun x ↦ -derivative i f x) = 𝔼 x, -derivative i f x :=
          expect_eq_fintypeExpect _
        _ = -𝔼 x, derivative i f x := Finset.expect_neg_distrib _ _
        _ = -expect (derivative i f) := congrArg Neg.neg (expect_eq_fintypeExpect _).symm
    have hle : expect (derivative i f) ≤ 0 := by
      have hpos : 0 ≤ expect (fun x ↦ -derivative i f x) := by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ neg_nonneg.mpr (h x)
      rw [hneg] at hpos
      linarith
    rw [hEq, hneg, abs_of_nonpos hle]

/-! ## Affine multilinear polynomials -/

/-- The multilinear polynomial with constant term `c` and degree-one coefficients `a`. -/
noncomputable def affinePoly (c : ℝ) (a : Fin n → ℝ) : MultilinearPolynomial n :=
  fun S ↦ if S = ∅ then c else ∑ i : Fin n, if S = {i} then a i else 0

@[simp]
lemma affinePoly_empty (c : ℝ) (a : Fin n → ℝ) : affinePoly c a ∅ = c := by simp [affinePoly]

@[simp]
lemma affinePoly_singleton (c : ℝ) (a : Fin n → ℝ) (i : Fin n) : affinePoly c a {i} = a i := by
  simp [affinePoly, Finset.singleton_ne_empty]

lemma affinePoly_hasDegreeAtMost_one (c : ℝ) (a : Fin n → ℝ) :
    (affinePoly c a).HasDegreeAtMost 1 := by
  intro S hS
  have h0 : S ≠ ∅ := by rintro rfl; simp at hS
  have h1 : ∀ i : Fin n, ¬ (S = {i}) := by
    intro i h; rw [h] at hS; simp at hS
  simp [affinePoly, h0, h1]

/-- Evaluation of a multilinear polynomial of degree at most one. -/
lemma eval_of_degree_le_one {p : MultilinearPolynomial n} (hp : p.HasDegreeAtMost 1)
    (x : BoolCube n) :
    p.eval x = p ∅ + ∑ i : Fin n, p {i} * boolToSign (x i) := by
  classical
  set T : Finset (Finset (Fin n)) :=
    insert ∅ (Finset.univ.image (fun i : Fin n ↦ ({i} : Finset (Fin n)))) with hT
  have hzero : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))), S ∉ T → p S * chiS S x = 0 := by
    intro S _ hS
    have hcard : 1 < S.card := by
      rcases Nat.lt_or_ge 1 S.card with h | h
      · exact h
      · exfalso
        apply hS
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
        · rw [Finset.card_eq_zero.mp h0]
          exact Finset.mem_insert_self _ _
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [hp S hcard, zero_mul]
  have hnot : (∅ : Finset (Fin n)) ∉
      Finset.univ.image (fun i : Fin n ↦ ({i} : Finset (Fin n))) := by
    simp [eq_comm]
  rw [MultilinearPolynomial.eval, ← Finset.sum_subset (Finset.subset_univ T) hzero, hT,
    Finset.sum_insert hnot,
    Finset.sum_image (fun i _ j _ h ↦ Finset.singleton_injective h)]
  simp

/-! ## Linear threshold functions as signs of affine forms -/

lemma thresholdSign_pm_one (r : ℝ) : thresholdSign r = 1 ∨ thresholdSign r = -1 := by
  unfold thresholdSign; split_ifs <;> simp

lemma thresholdSign_mono {r s : ℝ} (h : r ≤ s) : thresholdSign r ≤ thresholdSign s := by
  unfold thresholdSign
  split_ifs with h1 h2 h2
  · exact le_refl _
  · exact absurd (le_trans h1 h) h2
  · norm_num
  · exact le_refl _

lemma isPmOne_thresholdSign (g : BoolCube n → ℝ) :
    isPmOne (fun x ↦ thresholdSign (g x)) := fun _ ↦ thresholdSign_pm_one _

/-- Every linear threshold function is the sign of an affine form in the `±1` variables.

[OD14, §5.1, Eq. (5.1)] -/
lemma IsLinearThreshold.exists_affine {f : BooleanFunc n} (hf : IsLinearThreshold f) :
    ∃ (c : ℝ) (a : Fin n → ℝ),
      f = fun x ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i)) := by
  obtain ⟨p, hdeg, hrep⟩ := hf
  refine ⟨p ∅, fun i ↦ p {i}, ?_⟩
  rw [← hrep]
  funext x
  simp [MultilinearPolynomial.threshold, eval_of_degree_le_one hdeg]

/-- Conversely, the sign of an affine form is a linear threshold function. -/
lemma isLinearThreshold_affine (c : ℝ) (a : Fin n → ℝ) :
    IsLinearThreshold (fun x ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i))) := by
  refine ⟨affinePoly c a, affinePoly_hasDegreeAtMost_one c a, ?_⟩
  funext x
  simp [MultilinearPolynomial.threshold,
    eval_of_degree_le_one (affinePoly_hasDegreeAtMost_one c a)]

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
  rcases le_or_gt 0 (a i) with ha | ha
  · left
    intro x
    simp only [derivative, affine_form_update, boolToSign_false, boolToSign_true, mul_one,
      mul_neg_one]
    have hmono := thresholdSign_mono
      (show (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)) + -a i
        ≤ (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)) + a i by linarith)
    linarith
  · right
    intro x
    simp only [derivative, affine_form_update, boolToSign_false, boolToSign_true, mul_one,
      mul_neg_one]
    have hmono := thresholdSign_mono
      (show (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)) + a i
        ≤ (c + ∑ j ∈ Finset.univ.erase i, a j * boolToSign (x j)) + -a i by linarith)
    linarith

/-! ## The total influence bound -/

lemma sum_singleton_fourier_sq_le_one {f : BooleanFunc n} (hf : isPmOne f) :
    ∑ i : Fin n, fourierCoeff f {i} ^ 2 ≤ 1 := by
  classical
  have himg : ∑ i : Fin n, fourierCoeff f {i} ^ 2
      = ∑ S ∈ Finset.univ.image (fun i : Fin n ↦ ({i} : Finset (Fin n))),
          fourierCoeff f S ^ 2 := by
    rw [Finset.sum_image (fun i _ j _ h ↦ Finset.singleton_injective h)]
  rw [himg, ← parseval_pm_one f hf]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun S _ _ ↦ sq_nonneg _

/-- **Every linear threshold function has total influence at most `sqrt n`.**

Linear threshold functions are unate, so each influence equals `|f̂({i})|`; Cauchy-Schwarz and
Parseval then give the bound.

[OD14, §5.5, proof of Peres's Theorem] -/
theorem ltf_totalInfluence_le_sqrt {f : BooleanFunc n} (hf : IsLinearThreshold f) :
    totalInfluence f ≤ Real.sqrt n := by
  obtain ⟨c, a, rfl⟩ := hf.exists_affine
  set g : BooleanFunc n := fun x ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i)) with hg
  have hpm : isPmOne g := isPmOne_thresholdSign _
  have hinf : ∀ i : Fin n, influence i g = |fourierCoeff g {i}| := by
    intro i
    exact influence_eq_abs_fourierCoeff_of_sign hpm i (derivative_affine_threshold_sign c a i)
  have hcs : ∑ i : Fin n, |fourierCoeff g {i}| * 1
      ≤ Real.sqrt (∑ i : Fin n, |fourierCoeff g {i}| ^ 2) *
        Real.sqrt (∑ _i : Fin n, (1 : ℝ) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
  have hsq : ∑ i : Fin n, |fourierCoeff g {i}| ^ 2 = ∑ i : Fin n, fourierCoeff g {i} ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [sq_abs]
  have hcard : ∑ _i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) := by simp
  have hle1 : Real.sqrt (∑ i : Fin n, fourierCoeff g {i} ^ 2) ≤ 1 := by
    have h := sum_singleton_fourier_sq_le_one hpm
    calc Real.sqrt (∑ i : Fin n, fourierCoeff g {i} ^ 2) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt h
      _ = 1 := Real.sqrt_one
  calc totalInfluence g = ∑ i : Fin n, |fourierCoeff g {i}| * 1 := by
        simp only [totalInfluence, mul_one]
        exact Finset.sum_congr rfl fun i _ ↦ hinf i
    _ ≤ Real.sqrt (∑ i : Fin n, |fourierCoeff g {i}| ^ 2) *
          Real.sqrt (∑ _i : Fin n, (1 : ℝ) ^ 2) := hcs
    _ = Real.sqrt (∑ i : Fin n, fourierCoeff g {i} ^ 2) * Real.sqrt (n : ℝ) := by
        rw [hsq, hcard]
    _ ≤ 1 * Real.sqrt (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    _ = Real.sqrt n := one_mul _

end ThresholdFunctions
end BooleanAnalysis
