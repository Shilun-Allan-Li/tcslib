/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Linear
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.SpecificCodomains.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Smooth Gaussian Fourier averages

## Main definitions

* `gaussianFourierPairing`: coordinate pairing with the Fourier normalization.

## Main results

* `integrable_gaussianPi_norm_pow`: every norm moment is finite.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Proposition 11.16.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Every nonnegative integral power of the coordinate vector's norm is Gaussian
integrable. [OD14, §11.1, Gaussian moments] -/
lemma integrable_gaussianPi_norm_pow (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => ‖x‖ ^ k) γ := by
  apply MemLp.integrable_norm_pow' (p := k)
  apply MemLp.of_eval
  intro i
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) k).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => standardGaussianMeasure) i)

/-- The coordinate pairing normalized so that the Fourier phase is
`exp(a * (∑ i, x i * y i) * I)`. -/
noncomputable def gaussianFourierPairing (a : ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  (-a / (2 * Real.pi)) • ∑ i,
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

/-- The normalized coordinate pairing cancels the Fourier phase constant. -/
lemma gaussianFourierPairing_phase (a : ℝ) (x y : Fin n → ℝ) :
    -2 * Real.pi * gaussianFourierPairing a x y = a * ∑ i, x i * y i := by
  simp [gaussianFourierPairing, Finset.mul_sum]
  field_simp
  rw [Finset.sum_neg_distrib, neg_neg]

/-- The normalized Fourier integral is an average of complex exponential phases. -/
lemma gaussianFourierIntegral_eq (a : ℝ) (H : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar γ
      (gaussianFourierPairing a).toLinearMap₁₂ H x =
        ∫ t, Complex.exp (((a * ∑ i, t i * x i : ℝ) : ℂ) * Complex.I) * H t ∂γ := by
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply, gaussianFourierPairing_phase,
    smul_eq_mul]

/-- A Gaussian Fourier average of a bounded measurable function is smooth.
[OD14, Prop. 11.16, Fourier smoothing argument]

**Proof sketch.** Every polynomial norm moment of the Gaussian is finite.
Bound the amplitude by its constant bound in each weighted moment and apply
Mathlib's smoothness theorem for Fourier integrals. -/
lemma contDiff_gaussianFourierIntegral (a : ℝ) {H : (Fin n → ℝ) → ℂ}
    (hH : AEStronglyMeasurable H γ) (C : ℝ) (hbound : ∀ t, ‖H t‖ ≤ C) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : Fin n → ℝ =>
        ∫ t, Complex.exp (((a * ∑ i, t i * x i : ℝ) : ℂ) * Complex.I) * H t ∂γ) := by
  simp_rw [← gaussianFourierIntegral_eq]
  apply VectorFourier.contDiff_fourierIntegral
  intro k _
  apply ((integrable_gaussianPi_norm_pow k).mul_const C).mono'
    ((continuous_norm.pow k).aestronglyMeasurable.mul hH.norm)
  filter_upwards [] with t
  simpa only [Pi.mul_apply, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg t) k) (norm_nonneg (H t)))] using
      mul_le_mul_of_nonneg_left (hbound t) (pow_nonneg (norm_nonneg t) k)

/-- The exponential phase of a Gaussian linear combination averages to its
Gaussian characteristic function. [OD14, §11.1, Gaussian characteristic functions] -/
lemma integral_exp_mul_I_gaussianPi (a : Fin n → ℝ) :
    (∫ t, Complex.exp (((∑ i, a i * t i : ℝ) : ℂ) * Complex.I) ∂γ) =
      Complex.exp (-((∑ i, a i ^ 2 : ℝ) : ℂ) / 2) := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, a i • ContinuousLinearMap.proj i
  have hL (t : Fin n → ℝ) : L t = ∑ i, a i * t i := by
    simp [L, ContinuousLinearMap.sum_apply]
  have he : ∑ i, L (Pi.single i 1) ^ 2 = ∑ i, a i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [hL, Pi.single_apply, mul_ite]
  have h := charFunDual_gaussianPi L
  rw [he] at h
  simpa only [charFunDual_apply, hL] using h

/-- A Gaussian Fourier average of an integrable amplitude depends continuously
on its frequency. [OD14, §11.1, Gaussian Fourier averages] -/
lemma continuous_gaussianFourierIntegral (a : ℝ) {f : (Fin n → ℝ) → ℂ}
    (hf : Integrable f γ) :
    Continuous (fun x : Fin n → ℝ =>
      ∫ t, Complex.exp (((a * ∑ i, t i * x i : ℝ) : ℂ) * Complex.I) * f t ∂γ) := by
  simp_rw [← gaussianFourierIntegral_eq]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (gaussianFourierPairing a).continuous₂ hf

/-- A Gaussian Fourier average is uniformly bounded by the amplitude's L1 norm.
[OD14, §11.1, Gaussian Fourier averages] -/
lemma norm_gaussianFourierIntegral_le (a : ℝ) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    ‖∫ t, Complex.exp (((a * ∑ i, t i * x i : ℝ) : ℂ) * Complex.I) * f t ∂γ‖ ≤
      ∫ t, ‖f t‖ ∂γ := by
  rw [← gaussianFourierIntegral_eq]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- The exponential phase for a scalar multiple of the coordinate pairing. -/
noncomputable def gaussianPhase (a : ℝ) (x y : Fin n → ℝ) : ℂ :=
  Complex.exp (((a * ∑ i, x i * y i : ℝ) : ℂ) * Complex.I)

/-- Every Gaussian Fourier phase has norm one. -/
lemma norm_gaussianPhase (a : ℝ) (x y : Fin n → ℝ) : ‖gaussianPhase a x y‖ = 1 := by
  simp [gaussianPhase, Complex.norm_exp]

/-- Multiplying the two phases combines their coordinate coefficients. -/
lemma gaussianPhase_mul (a b : ℝ) (t x y : Fin n → ℝ) :
    gaussianPhase a t x * gaussianPhase b y t =
      gaussianPhase 1 (fun i => a * x i + b * y i) t := by
  have hs : a * ∑ i, t i * x i + b * ∑ i, y i * t i =
      ∑ i, (a * x i + b * y i) * t i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [gaussianPhase, one_mul, ← Complex.exp_add, ← add_mul,
    ← Complex.ofReal_add, hs]

/-- The product of two Gaussian Fourier phases times an integrable amplitude is
jointly integrable. [OD14, Prop. 11.16, Fourier smoothing argument] -/
lemma integrable_gaussian_double_phase (a b : ℝ) (x : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianPhase a z.1 x * gaussianPhase b z.2 z.1 * (f z.2 : ℂ)) ((γ).prod γ) := by
  have hm : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianPhase a z.1 x * gaussianPhase b z.2 z.1) := by
    unfold gaussianPhase
    fun_prop
  apply (hf.norm.comp_snd γ).mono'
    (hm.aestronglyMeasurable.mul hf.ofReal.aestronglyMeasurable.comp_snd)
  filter_upwards [] with z
  simp only [Pi.mul_apply, norm_mul, norm_gaussianPhase, one_mul, RCLike.norm_ofReal,
    Real.norm_eq_abs, le_refl]

/-- Two successive Fourier averages, the outer one Gaussian, give a Gaussian
exponential kernel. [OD14, Prop. 11.16, Fourier smoothing argument]

**Proof sketch.** The phase factors have norm one, so integrability of the input
justifies Fubini. Combine their phases and evaluate the inner Gaussian
characteristic function. -/
lemma integral_gaussian_double_phase (a b : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f γ) (x : Fin n → ℝ) :
    (∫ t, gaussianPhase a t x * (∫ y, gaussianPhase b y t * (f y : ℂ) ∂γ) ∂γ) =
      ((∫ y, f y * Real.exp (-(∑ i, (a * x i + b * y i) ^ 2) / 2) ∂γ : ℝ) : ℂ) := by
  calc
    _ = ∫ t, ∫ y, gaussianPhase a t x * gaussianPhase b y t * (f y : ℂ) ∂γ ∂γ := by
      simp only [mul_assoc, integral_const_mul]
    _ = ∫ y, ∫ t, gaussianPhase a t x * gaussianPhase b y t * (f y : ℂ) ∂γ ∂γ :=
      integral_integral_swap (integrable_gaussian_double_phase a b x hf)
    _ = ∫ y, Complex.exp (-((∑ i, (a * x i + b * y i) ^ 2 : ℝ) : ℂ) / 2) *
        (f y : ℂ) ∂γ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [gaussianPhase_mul, integral_mul_const]
      simp only [gaussianPhase, one_mul]
      rw [integral_exp_mul_I_gaussianPi]
    _ = _ := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [] with y
      simp [Complex.ofReal_exp, mul_comm]

/-- Integrating a Gaussian exponential kernel against a Gaussian integrable
function gives a smooth function of its translation parameter.
[OD14, Prop. 11.16, Fourier smoothing argument]

**Proof sketch.** Represent the kernel as two Fourier averages. The inner
average is continuous and uniformly bounded by the input's L1 norm. The outer
Gaussian Fourier average is smooth because all Gaussian moments are finite.
Take its real part. -/
lemma contDiff_integral_gaussian_exp (a b : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f γ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Fin n → ℝ =>
      ∫ y, f y * Real.exp (-(∑ i, (a * x i + b * y i) ^ 2) / 2) ∂γ) := by
  have hH := continuous_gaussianFourierIntegral b (hf.ofReal : Integrable (fun y => (f y : ℂ)) γ)
  have hd := contDiff_gaussianFourierIntegral a hH.aestronglyMeasurable
    (∫ y, ‖(f y : ℂ)‖ ∂γ)
    (norm_gaussianFourierIntegral_le b (fun y => (f y : ℂ)))
  convert Complex.reCLM.contDiff.comp hd using 1
  funext x
  exact (congrArg Complex.re (integral_gaussian_double_phase a b hf x)).symm

end BooleanAnalysis.GaussianSpace
