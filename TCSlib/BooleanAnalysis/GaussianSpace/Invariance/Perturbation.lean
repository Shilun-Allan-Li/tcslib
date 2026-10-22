/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Moments
import TCSlib.BooleanAnalysis.GaussianSpace.InputMoments
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lipschitz perturbations of square-integrable inputs

## Main definitions

The existing random-variable and Boolean L² norms are reused.

## Main results

Lipschitz tests change by at most the Lipschitz constant times the L² distance
between their inputs, with polynomial norm identities for standardized laws.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, proof of Corollary 11.69.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- A Lipschitz test of an integrable real input is integrable under a finite
measure. This is technical integrability glue for expectation comparison. -/
theorem integrable_lipschitz_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U : Ω → ℝ} (hU : Integrable U μ) {c : ℝ≥0}
    {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    Integrable (fun ω => ψ (U ω)) μ := by
  have hcenterLip : LipschitzWith c (fun x => ψ x - ψ 0) := by
    simpa using hψ.sub (LipschitzWith.const (ψ 0))
  have hcenter : Integrable (fun ω => ψ (U ω) - ψ 0) μ :=
    memLp_one_iff_integrable.mp
      (hcenterLip.comp_memLp (by simp) (memLp_one_iff_integrable.mpr hU))
  convert hcenter.add (integrable_const (ψ 0)) using 1
  ext ω
  simp

/-- A Lipschitz test changes in expectation by at most its Lipschitz constant
times the second norm of the input difference.
[OD14, Cor. 11.69 (proof), Cauchy–Schwarz tail comparison]

**Proof sketch.** Integrate the pointwise Lipschitz bound. The first norm of
the difference is at most its second norm on a probability space. -/
theorem lipschitz_integral_sub_le_two_norm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {U V : Ω → ℝ} (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    {c : ℝ≥0} {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    |(∫ ω, ψ (U ω) ∂μ) - ∫ ω, ψ (V ω) ∂μ| ≤
      (c : ℝ) * rvLpNorm (fun ω => U ω - V ω) μ 2 := by
  have hU1 : Integrable U μ := hU.integrable (by norm_num)
  have hV1 : Integrable V μ := hV.integrable (by norm_num)
  have hψU := integrable_lipschitz_comp hU1 hψ
  have hψV := integrable_lipschitz_comp hV1 hψ
  have hnorm :
      (∫ ω, |U ω - V ω| ∂μ) ≤ rvLpNorm (fun ω => U ω - V ω) μ 2 := by
    change (∫ ω, ‖(U - V) ω‖ ∂μ) ≤ rvLpNorm (U - V) μ 2
    rw [integral_norm_eq_lintegral_enorm (hU.sub hV).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    change (eLpNorm (fun ω => U ω - V ω) 1 μ).toReal ≤
      (eLpNorm (fun ω => U ω - V ω) (ENNReal.ofReal 2) μ).toReal
    norm_num only [ENNReal.ofReal_ofNat]
    exact ENNReal.toReal_mono (hU.sub hV).2.ne
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hU.sub hV).aestronglyMeasurable)
  rw [← integral_sub hψU hψV]
  calc
    _ ≤ ∫ ω, |ψ (U ω) - ψ (V ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (c : ℝ) * |U ω - V ω| ∂μ := by
      apply integral_mono_ae (hψU.sub hψV).abs ((hU1.sub hV1).abs.const_mul (c : ℝ))
      exact Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hψ.norm_sub_le (U ω) (V ω)
    _ = (c : ℝ) * (∫ ω, |U ω - V ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm c.coe_nonneg

/-- The second norm of a polynomial in independent standardized inputs is its
Boolean L² norm. [OD14, Remark 11.64]
Finite fourth moments are retained to use the existing coefficient identity. -/
theorem polynomial_two_norm_eq_l2Norm
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) :
    rvLpNorm (evalMultilinearRV F X) μ 2 = l2Norm F.eval := by
  have hmem : MemLp (evalMultilinearRV F X) 2 μ :=
    (evalMultilinearRV_memLp F X μ hI hX).mono_exponent (by norm_num)
  have hm := rvLpNorm_rpow (evalMultilinearRV F X) μ 2 (by norm_num) (by simpa using hmem)
  simp only [Real.rpow_two, sq_abs] at hm
  rw [MultilinearMoments.integral_eval_sq F X hI hX hmean hsecond] at hm
  unfold l2Norm innerProduct
  simp only [← pow_two]
  rw [F.expect_eval_sq, ← hm,
    Real.sqrt_sq (show 0 ≤ rvLpNorm (evalMultilinearRV F X) μ 2 from ENNReal.toReal_nonneg)]

/-- Lipschitz expectations of two polynomials in standardized independent inputs
differ by at most the Lipschitz constant times their Boolean L² distance.
[OD14, Cor. 11.69 (proof), matching polynomial second moments] -/
theorem lipschitz_polynomial_integral_sub_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : MultilinearPolynomial n) (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1)
    {c : ℝ≥0} {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
      ∫ ω, ψ (evalMultilinearRV G X ω) ∂μ| ≤
      (c : ℝ) * l2Norm (F - G).eval := by
  have hsub : (fun ω => evalMultilinearRV F X ω - evalMultilinearRV G X ω) =
      evalMultilinearRV (F - G) X := by
    funext ω
    simp only [evalMultilinearRV, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have h := lipschitz_integral_sub_le_two_norm
    ((evalMultilinearRV_memLp F X μ hI hX).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))
    ((evalMultilinearRV_memLp G X μ hI hX).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)) hψ
  simpa only [hsub, polynomial_two_norm_eq_l2Norm (F - G) X hI hX hmean hsecond] using h

/-- Lipschitz expectations on the Boolean cube differ by at most the Lipschitz
constant times the Boolean L² distance. [OD14, Cor. 11.69 (proof)] -/
theorem lipschitz_expect_sub_le_l2Norm {n : ℕ} (f g : BooleanFunc n)
    {c : ℝ≥0} {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    |expect (fun x => ψ (f x)) - expect (fun x => ψ (g x))| ≤
      (c : ℝ) * l2Norm (f - g) := by
  have heval (H : MultilinearPolynomial n) :
      evalMultilinearRV H (fun i (x : BoolCube n) => boolToSign (x i)) = H.eval := rfl
  have h := lipschitz_polynomial_integral_sub_le (fourierCoeff f) (fourierCoeff g)
    (fun i (x : BoolCube n) => boolToSign (x i))
    (iIndepFun_pi (μ := fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
      (X := fun _ : Fin n => boolToSign) (fun _ => (measurable_of_finite _).aemeasurable))
    (fun i => (hasInvarianceMoments_uniformBoolCoordinate i).reasonable.memLp)
    (fun i => (hasInvarianceMoments_uniformBoolCoordinate i).mean)
    (fun i => (hasInvarianceMoments_uniformBoolCoordinate i).second) hψ
  simpa only [heval, MultilinearPolynomial.eval_fourierCoeff,
    integral_uniformBool_pi_eq_expect, MultilinearPolynomial.eval_sub] using h

/-- Lipschitz expectations of Gaussian extensions differ by at most the Lipschitz
constant times the Boolean L² distance. [OD14, Cor. 11.69 (proof)]

**Proof sketch.** Standard Gaussian coordinates have the required moments and
are independent. Apply polynomial perturbation and identify the Fourier evaluations. -/
theorem lipschitz_gaussian_extension_sub_le_l2Norm {n : ℕ} (f g : BooleanFunc n)
    {c : ℝ≥0} {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    |(∫ z : Fin n → ℝ,
        ψ (evalMultilinearRV (fourierCoeff f) (fun i z => z i) z)
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
      ∫ z : Fin n → ℝ,
        ψ (evalMultilinearRV (fourierCoeff g) (fun i z => z i) z)
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)| ≤
      (c : ℝ) * l2Norm (f - g) := by
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    hasInvarianceMoments_standardGaussian.reasonable.probability
  have hY (i : Fin n) := hasInvarianceMoments_gaussianCoordinate (n := n) i
  have hIY : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    iIndepFun_pi (μ := fun _ : Fin n => standardGaussianMeasure)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  simpa only [MultilinearPolynomial.eval_sub, MultilinearPolynomial.eval_fourierCoeff] using
    lipschitz_polynomial_integral_sub_le (fourierCoeff f) (fourierCoeff g)
      (fun (i : Fin n) (z : Fin n → ℝ) => z i) hIY
      (fun i => (hY i).reasonable.memLp) (fun i => (hY i).mean)
      (fun i => (hY i).second) hψ

end BooleanAnalysis.GaussianSpace.Invariance
