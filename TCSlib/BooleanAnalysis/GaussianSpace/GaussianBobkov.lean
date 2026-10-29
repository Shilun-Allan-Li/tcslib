/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov
import TCSlib.BooleanAnalysis.GaussianSpace.BooleanBlocks
import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedBlocks

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Smooth Gaussian Bobkov inequality

## Main definitions

The existing Gaussian profile, derivative, and product Gaussian law are reused.
The gradient length is the Euclidean length of the derivative's canonical-basis
coefficients.

## Main results

* Normalized Boolean block derivatives approximate the Gaussian length
  integrand, with a vanishing accumulated error.
* `gaussian_bobkov_smooth`: Gaussian Bobkov for unit-interval functions with
  bounded Lipschitz derivative.

Finite-dimensional Gaussian approximation accepts bounded continuous tests,
so endpoint values of the closed profile require no interior regularization.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Gaussian Bobkov's inequality and its
  normalized-bit approximation proof.
-/

open MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology BoundedContinuousFunction

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- Perturbing a vector's gradient coordinates changes its length by at most
the Euclidean length of the perturbation.

**Proof sketch.** Include the unchanged scalar coordinate in an Option-indexed
Euclidean vector and apply the triangle inequality. -/
lemma sqrt_sq_add_sum_sq_le_add_error {ι : Type*} [Fintype ι]
    (P : ℝ) (d g : ι → ℝ) :
    Real.sqrt (P ^ 2 + ∑ i, d i ^ 2) ≤
      Real.sqrt (P ^ 2 + ∑ i, g i ^ 2) + Real.sqrt (∑ i, (d i - g i) ^ 2) := by
  let u : EuclideanSpace ℝ (Option ι) := WithLp.toLp 2 (fun i => i.elim P d)
  let v : EuclideanSpace ℝ (Option ι) := WithLp.toLp 2 (fun i => i.elim P g)
  have h := norm_add_le v (u - v)
  rw [add_sub_cancel] at h
  simpa [u, v, EuclideanSpace.norm_eq, Fintype.sum_option,
    Real.norm_eq_abs, sq_abs, add_comm] using h

/-- Uniform coordinate errors in a normalized repeated gradient bound the
array length by the original gradient length plus square root of the number
of entries times the error. [OD14, §11.4, Gaussian Bobkov limit]

**Proof sketch.** The repeated principal terms have the same squared norm as
the original gradient. The sum of squared errors is bounded by the number of
entries times their common squared bound. Apply the vector triangle inequality. -/
lemma sqrt_sq_add_array_sq_le {n m : ℕ} (hm : 0 < m)
    (P : ℝ) (d : Fin n → Fin m → ℝ) (g : Fin n → ℝ) (e : ℝ)
    (he : 0 ≤ e) (hd : ∀ i j, |d i j - g i / Real.sqrt m| ≤ e) :
    Real.sqrt (P ^ 2 + ∑ i, ∑ j, d i j ^ 2) ≤
      Real.sqrt (P ^ 2 + ∑ i, g i ^ 2) + Real.sqrt ((n : ℝ) * m) * e := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmain : (∑ p : Fin n × Fin m, (g p.1 / Real.sqrt m) ^ 2) =
      ∑ i : Fin n, g i ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_pow, Real.sq_sqrt (Nat.cast_nonneg m), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hm']
  have herr : (∑ p : Fin n × Fin m, (d p.1 p.2 - g p.1 / Real.sqrt m) ^ 2) ≤
      ((n : ℝ) * m) * e ^ 2 := by
    calc
      _ ≤ ∑ _p : Fin n × Fin m, e ^ 2 := by
        apply Finset.sum_le_sum
        intro p _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr (hd p.1 p.2)
      _ = _ := by simp [Fintype.card_prod, Nat.cast_mul, mul_assoc]
  have h := sqrt_sq_add_sum_sq_le_add_error P
    (fun p : Fin n × Fin m => d p.1 p.2)
    (fun p : Fin n × Fin m => g p.1 / Real.sqrt m)
  rw [hmain, Fintype.sum_prod_type] at h
  refine h.trans (add_le_add_left (Real.sqrt_le_sqrt herr) _ |>.trans_eq ?_)
  rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg he]

/-- The Gaussian Bobkov length integrand of a continuous unit-interval function
and a continuous uniformly bounded derivative family is bounded continuous.
[OD14, §11.4, Gaussian Bobkov limit]

**Proof sketch.** The profile is continuous and bounded on the compact
probability interval. Each partial derivative is bounded by the operator norm
bound, so the squared gradient sum and the full length have a uniform bound. -/
lemma exists_boundedContinuous_bobkov_integrand {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : Continuous f) (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hD : Continuous D) (M : ℝ) (hM : ∀ x, ‖D x‖ ≤ M) :
    ∃ F : (Fin n → ℝ) →ᵇ ℝ, ∀ x,
      F x = Real.sqrt (closedGaussianProfile (f x) ^ 2 +
        ∑ i : Fin n, (D x (Pi.single i 1)) ^ 2) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuousOn_closedGaussianProfile
  have hAnonneg : 0 ≤ A := (norm_nonneg _).trans (hA (f 0) (hfrange 0))
  have hMnonneg : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let H (x : Fin n → ℝ) := Real.sqrt (closedGaussianProfile (f x) ^ 2 +
    ∑ i : Fin n, (D x (Pi.single i 1)) ^ 2)
  have hH : Continuous H := by
    dsimp [H]
    exact ((continuous_closedGaussianProfile.comp hf).pow 2 |>.add
      (continuous_finset_sum _ fun i _ => (hD.clm_apply continuous_const).pow 2)).sqrt
  have hbound (x : Fin n → ℝ) : ‖H x‖ ≤ Real.sqrt (A ^ 2 + (n : ℝ) * M ^ 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    apply add_le_add
    · simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) hAnonneg).mpr (hA (f x) (hfrange x))
    · calc
        _ ≤ ∑ _i : Fin n, M ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : ‖D x (Pi.single i (1 : ℝ))‖ ≤ M := by
            have h := (D x).le_opNorm (Pi.single i 1)
            simp only [Pi.norm_single, norm_one, mul_one] at h
            exact h.trans (hM x)
          simpa only [Real.norm_eq_abs, sq_abs] using
            (sq_le_sq₀ (norm_nonneg _) hMnonneg).mpr hi
        _ = _ := by simp
  exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup H hH _ hbound, fun _ => rfl⟩

/-- The accumulated gradient approximation error tends to zero as the Boolean
block size tends to infinity. [OD14, §11.4, Gaussian Bobkov limit]

**Proof sketch.** Rewrite the error as a fixed constant times the square root
of one divided by the block size, which tends to zero. -/
lemma tendsto_block_gradient_error (n : ℕ) (C : ℝ) :
    Tendsto (fun m : ℕ => Real.sqrt ((n : ℝ) * (m + 1)) *
      (2 * C / (m + 1))) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := hi.sqrt.const_mul (2 * C * Real.sqrt n)
  simp only [Real.sqrt_zero, mul_zero] at h
  convert h using 1
  funext m
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_div (by positivity)]
  norm_num only [Real.sqrt_one]
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hroot : Real.sqrt (m + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  field_simp
  ring_nf
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + m by positivity)]
  ring

/-- Boolean Bobkov on normalized blocks is bounded by the Gaussian length
integrand evaluated on the blocks, plus an error tending to zero.
[OD14, §11.4, Gaussian Bobkov limit]

**Proof sketch.** Apply the array Boolean Bobkov inequality. Each discrete
derivative approximates its normalized partial derivative with quadratic
Taylor error. The Euclidean array-length bound accumulates those errors;
probability normalization integrates the constant error unchanged. -/
lemma bobkov_normalizedBoolBlocks_le {n m : ℕ} (hm : 0 < m)
    {f : (Fin n → ℝ) → ℝ} {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hfrange : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ z, HasFDerivAt f (D z) z) {C : ℝ≥0} (hD : LipschitzWith C D) :
    closedGaussianProfile (∫ x : Fin n → Fin m → Bool,
      f (fun i => (∑ j, boolToSign (x i j)) / Real.sqrt m)
      ∂(Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure)) ≤
      (∫ x : Fin n → Fin m → Bool,
        Real.sqrt (closedGaussianProfile
          (f (fun i => (∑ j, boolToSign (x i j)) / Real.sqrt m)) ^ 2 +
          ∑ i : Fin n,
            (D (fun k => (∑ j, boolToSign (x k j)) / Real.sqrt m) (Pi.single i 1)) ^ 2)
        ∂(Measure.pi fun _ : Fin n =>
          Measure.pi fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure)) +
        Real.sqrt ((n : ℝ) * m) * (2 * (C : ℝ) / m) := by
  let z (x : Fin n → Fin m → Bool) : Fin n → ℝ :=
    fun i => (∑ j, boolToSign (x i j)) / Real.sqrt m
  let μ : Measure (Fin n → Fin m → Bool) := Measure.pi fun _ : Fin n =>
    Measure.pi fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure
  let G (x : Fin n → Fin m → Bool) :=
    Real.sqrt (closedGaussianProfile (f (z x)) ^ 2 +
      ∑ i : Fin n, (D (z x) (Pi.single i 1)) ^ 2)
  let err := Real.sqrt ((n : ℝ) * m) * (2 * (C : ℝ) / m)
  have hb := bobkov_inequality_array (fun x => f (z x)) (fun x => hfrange (z x))
  refine hb.trans ?_
  calc
    _ ≤ ∫ x, (G x + err) ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro x
      exact sqrt_sq_add_array_sq_le hm (closedGaussianProfile (f (z x)))
        (fun i j => (f (z (Function.update x i (Function.update (x i) j false))) -
          f (z (Function.update x i (Function.update (x i) j true)))) / 2)
        (fun i => D (z x) (Pi.single i 1)) (2 * (C : ℝ) / m) (by positivity)
        (fun i j => abs_normalizedBoolBlocks_half_difference_sub_derivative_le hf hD x i j)
    _ = (∫ x, G x ∂μ) + err := by
      rw [integral_add Integrable.of_finite (integrable_const err)]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]

/-- The Gaussian profile of a smooth unit-interval function's mean is at most
its Gaussian Bobkov functional when its derivative is bounded and Lipschitz.
[OD14, §11.4, Gaussian Bobkov's inequality]
The explicit derivative family describes the function's ordinary derivative;
the full closed probability interval, including endpoint values, is allowed.

**Proof sketch.** Apply Boolean Bobkov to the function on normalized independent
Boolean blocks. Taylor linearization bounds its discrete-gradient error, whose
Euclidean accumulation tends to zero. The normalized-block limit transfers
both the function mean and the bounded continuous length integrand to their
Gaussian expectations. Continuity of the closed profile and preservation of
inequalities under limits finish the proof. -/
lemma gaussian_bobkov_smooth {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hfrange : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ z, HasFDerivAt f (D z) z) {C : ℝ≥0} (hD : LipschitzWith C D)
    (M : ℝ) (hM : ∀ z, ‖D z‖ ≤ M) :
    closedGaussianProfile (∫ z : Fin n → ℝ, f z
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ≤
      ∫ z : Fin n → ℝ,
        Real.sqrt (closedGaussianProfile (f z) ^ 2 +
          ∑ i : Fin n, (D z (Pi.single i 1)) ^ 2)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf z).continuousAt
  let F : (Fin n → ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup f hc 1 (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfrange z).1]
      exact (hfrange z).2)
  obtain ⟨G, hG⟩ := exists_boundedContinuous_bobkov_integrand hc hfrange hD.continuous M hM
  have hmean := tendsto_integral_normalizedBoolBlocks n F
  have hleft := (continuous_closedGaussianProfile.tendsto _).comp hmean
  have hright := (tendsto_integral_normalizedBoolBlocks n G).add
    (tendsto_block_gradient_error n (C : ℝ))
  simp_rw [hG] at hright
  simp only [add_zero] at hright
  refine le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun m => ?_)
  simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, F,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, Function.comp_apply] using
    bobkov_normalizedBoolBlocks_le (n := n) (Nat.succ_pos m) hfrange hf hD

/-- The Euclidean coefficient length of a continuous uniformly bounded
Gaussian derivative family is integrable under the product standard Gaussian
law. [OD14, §11.4, smooth indicator approximation]

**Proof sketch.** Set the scalar profile coordinate to zero in the bounded
continuous length integrand. Its resulting Gaussian integral is genuinely
finite because the Gaussian product law is a probability measure. -/
lemma integrable_gaussianGradient_of_bounded {n : ℕ}
    {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hD : Continuous D) (M : ℝ) (hM : ∀ x, ‖D x‖ ≤ M) :
    Integrable (fun x : Fin n → ℝ =>
      Real.sqrt (∑ i : Fin n, (D x (Pi.single i 1)) ^ 2))
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  obtain ⟨G, hG⟩ := exists_boundedContinuous_bobkov_integrand
    (f := fun _ : Fin n → ℝ => (0 : ℝ)) continuous_const (fun _ => by norm_num) hD M hM
  exact (G.integrable (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure)).congr
    (Eventually.of_forall fun x => by
    simpa only [closedGaussianProfile_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
      using hG x)

/-- The Gaussian profile of a smooth unit-interval function's mean is at most
the sum of its integral profile and integral Euclidean gradient length, when
its derivative is bounded and Lipschitz. [OD14, §11.4, smooth isoperimetric argument]

**Proof sketch.** Apply Gaussian Bobkov, then bound the Euclidean length of
the nonnegative profile and gradient coordinates by their sum. Both summands
are genuinely integrable: the profile is bounded on the probability interval
and the derivative family is uniformly bounded. -/
lemma gaussian_bobkov_smooth_le_sum {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hfrange : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ z, HasFDerivAt f (D z) z) {C : ℝ≥0} (hD : LipschitzWith C D)
    (M : ℝ) (hM : ∀ z, ‖D z‖ ≤ M) :
    closedGaussianProfile (∫ z : Fin n → ℝ, f z
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ≤
      (∫ z : Fin n → ℝ, closedGaussianProfile (f z)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) +
      ∫ z : Fin n → ℝ, Real.sqrt (∑ i : Fin n, (D z (Pi.single i 1)) ^ 2)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf z).continuousAt
  have hp := integrable_closedGaussianProfile_comp hc.measurable hfrange
    (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure)
  have hg := integrable_gaussianGradient_of_bounded hD.continuous M hM
  refine (gaussian_bobkov_smooth hfrange hf hD M hM).trans ?_
  rw [← integral_add hp hg]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
    (hp.add hg)
  filter_upwards [] with x
  change Real.sqrt (closedGaussianProfile (f x) ^ 2 +
    ∑ i : Fin n, (D x (Pi.single i 1)) ^ 2) ≤
      closedGaussianProfile (f x) + Real.sqrt (∑ i : Fin n, (D x (Pi.single i 1)) ^ 2)
  apply (Real.sqrt_le_iff).mpr
  constructor
  · exact add_nonneg (closedGaussianProfile_nonneg _) (Real.sqrt_nonneg _)
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ∑ i : Fin n,
        (D x (Pi.single i 1)) ^ 2 by positivity)
    have hP := closedGaussianProfile_nonneg (f x)
    have hG := Real.sqrt_nonneg (∑ i : Fin n, (D x (Pi.single i 1)) ^ 2)
    nlinarith

end BooleanAnalysis.GaussianSpace
