/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Bivariate
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Integration
import TCSlib.BooleanAnalysis.GaussianSpace.Profile
import Mathlib.Analysis.Convex.Deriv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Differential calculus for the bivariate Gaussian profile

## Main definitions

The bivariate halfspace profile and scalar Gaussian cdf and quantile are reused.

## Main results

The conditional Gaussian integral gives both first partial derivatives of the
profile in the open probability square. Its explicit slope derivatives prove
section concavity and domination of the product of the volumes. The Gaussian
density symmetry prepares the curvature calculation for interpolation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3.
* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2, Lemma 2.1.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Differentiating a continuous integrable density's cumulative integral
recovers the density. -/
private lemma hasDerivAt_integral_Iic {f : ℝ → ℝ} (hf : Integrable f)
    (hc : Continuous f) (t : ℝ) :
    HasDerivAt (fun b => ∫ x in Set.Iic b, f x) (f t) t := by
  have heq : (fun b => ∫ x in Set.Iic b, f x) =
      (fun b => (∫ x in Set.Iic (0 : ℝ), f x) + ∫ x in (0 : ℝ)..b, f x) := by
    funext b
    have hi := intervalIntegral.integral_Iic_sub_Iic
      (a := (0 : ℝ)) (b := b) hf.integrableOn hf.integrableOn
    linarith
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add _

/-- Differentiating a Gaussian cdf integral at a Gaussian quantile cancels the
density from the quantile derivative.

**Proof sketch.** Weight the bounded conditional cdf by the Gaussian density.
This gives a continuous integrable Lebesgue density, so the fundamental theorem
of calculus applies. Compose with the quantile derivative and cancel the
strictly positive marginal density. -/
private lemma hasDerivAt_quantile_conditional_integral (ρ t d : ℝ) {a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun p => ∫ x in Set.Iic (standardGaussianQuantile p),
        standardGaussianCDF ((t - ρ * x) / d) ∂standardGaussianMeasure)
      (standardGaussianCDF ((t - ρ * standardGaussianQuantile a) / d)) a := by
  let f : ℝ → ℝ := fun x =>
    standardGaussianPDF x * standardGaussianCDF ((t - ρ * x) / d)
  have hc : Continuous f := continuous_standardGaussianPDF.mul
    (continuous_standardGaussianCDF.comp (by fun_prop))
  have hi : Integrable f := (integrable_gaussianPDFReal 0 1).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,
        abs_of_pos (mul_pos (standardGaussianPDF_pos x) (standardGaussianCDF_pos _))]
      exact mul_le_of_le_one_right (standardGaussianPDF_pos x).le
        (standardGaussianCDF_lt_one _).le)
  simp_rw [integral_Iic_standardGaussianMeasure]
  have hd := (hasDerivAt_integral_Iic hi hc (standardGaussianQuantile a)).comp a
    (hasDerivAt_standardGaussianQuantile ha)
  convert hd using 1
  dsimp [f, gaussianIsoperimetric]
  field_simp [(standardGaussianPDF_pos (standardGaussianQuantile a)).ne']

/-- The first partial derivative of the bivariate probability profile is a
conditional Gaussian cdf. [MN15, §2, Lemma 2.1, quantile-coordinate form]

**Proof sketch.** Express the profile locally by its conditional integral.
The fundamental theorem of calculus and the inverse-cdf derivative cancel
the marginal Gaussian density, leaving the conditional cdf. -/
lemma hasDerivAt_gaussianBivariateStability_left (ρ : ℝ) {a b : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => gaussianBivariateStability ρ p b)
      (standardGaussianCDF ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) /
        Real.sqrt (1 - ρ ^ 2))) a := by
  apply (hasDerivAt_quantile_conditional_integral ρ (standardGaussianQuantile b)
    (Real.sqrt (1 - ρ ^ 2)) ha).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with p hp
  exact gaussianBivariateStability_eq_conditional_integral ρ p b hρ hp hb

/-- The explicit conditional-cdf expression has the displayed derivative in
its first volume. [MN15, §2, Lemma 2.1, quantile-coordinate form]
For `-1 < ρ < 1` this is the second derivative of the profile in that volume.
The expression derivative also holds for other correlations under Lean's
totalized division convention; no profile interpretation is asserted there. -/
lemma hasDerivAt_gaussianBivariateSlope_left (ρ b : ℝ) {a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => standardGaussianCDF
        ((standardGaussianQuantile b - ρ * standardGaussianQuantile p) /
          Real.sqrt (1 - ρ ^ 2)))
      (-ρ * standardGaussianPDF
        ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) /
          Real.sqrt (1 - ρ ^ 2)) /
        (Real.sqrt (1 - ρ ^ 2) * gaussianIsoperimetric a)) a := by
  convert (hasDerivAt_standardGaussianCDF _).comp a
    (((hasDerivAt_standardGaussianQuantile ha).const_mul ρ).const_sub
      (standardGaussianQuantile b) |>.div_const (Real.sqrt (1 - ρ ^ 2))) using 1
  ring

/-- The explicit conditional-cdf expression has the displayed derivative in
its second volume. [MN15, §2, Lemma 2.1, quantile-coordinate form]
For `-1 < ρ < 1` this is a mixed second derivative of the profile. Outside that
range this statement concerns only the totalized cdf expression. -/
lemma hasDerivAt_gaussianBivariateSlope_right (ρ a : ℝ) {b : ℝ}
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => standardGaussianCDF
        ((standardGaussianQuantile p - ρ * standardGaussianQuantile a) /
          Real.sqrt (1 - ρ ^ 2)))
      (standardGaussianPDF
        ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) /
          Real.sqrt (1 - ρ ^ 2)) /
        (Real.sqrt (1 - ρ ^ 2) * gaussianIsoperimetric b)) b := by
  convert (hasDerivAt_standardGaussianCDF _).comp b
    (((hasDerivAt_standardGaussianQuantile hb).sub_const
      (ρ * standardGaussianQuantile a)).div_const (Real.sqrt (1 - ρ ^ 2))) using 1
  ring

/-- The first derivative with respect to the second volume is the conditional
Gaussian cdf with the volumes exchanged.
[MN15, §2, Lemma 2.1, quantile-coordinate form] -/
lemma hasDerivAt_gaussianBivariateStability_right (ρ : ℝ) {a b : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => gaussianBivariateStability ρ a p)
      (standardGaussianCDF ((standardGaussianQuantile a - ρ * standardGaussianQuantile b) /
        Real.sqrt (1 - ρ ^ 2))) b := by
  simpa only [gaussianBivariateStability_symm ⟨hρ.1.le, hρ.2.le⟩ a] using
    hasDerivAt_gaussianBivariateStability_left ρ hρ hb ha

/-- Each interior second-volume section of the Gaussian profile is concave
in the first volume for positive correlation.
[MN15, §2, Lemma 2.1, second-derivative consequence]

**Proof sketch.** The first and second partial derivative formulas hold in
the interior. The second derivative is nonpositive because the correlation,
Gaussian density, and scale factors have the required signs. Continuity on the
closed interval extends this concavity to both endpoints. -/
lemma concaveOn_gaussianBivariateStability_left {ρ b : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun a => gaussianBivariateStability ρ a b) := by
  have hρ' : ρ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2⟩
  have hc : ContinuousOn (fun a => gaussianBivariateStability ρ a b) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_gaussianBivariateStability ⟨hρ'.1.le, hρ'.2.le⟩).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ha => ⟨ha, hb.1.le, hb.2.le⟩)
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun a => standardGaussianCDF
      ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) / Real.sqrt (1 - ρ ^ 2)))
    (f'' := fun a => -ρ * standardGaussianPDF
      ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) / Real.sqrt (1 - ρ ^ 2)) /
      (Real.sqrt (1 - ρ ^ 2) * gaussianIsoperimetric a)) hc ?_ ?_ ?_
  · intro a ha
    rw [interior_Icc] at ha
    exact (hasDerivAt_gaussianBivariateStability_left ρ hρ' ha hb).hasDerivWithinAt
  · intro a ha
    rw [interior_Icc] at ha
    exact (hasDerivAt_gaussianBivariateSlope_left ρ b ha).hasDerivWithinAt
  · intro a _
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.1.le)
        (standardGaussianPDF_pos _).le)
      (mul_nonneg (Real.sqrt_nonneg _) (standardGaussianPDF_pos _).le)

/-- For positive correlation, the bivariate Gaussian profile dominates the
product of its two volumes. [MN15, §1.6, pointwise comparison with J]

**Proof sketch.** Fix an interior second volume. Concavity of the first-volume
section bounds it below by the chord between its endpoint values zero and
the second volume. When the second volume is an endpoint the inequality is
an equality by the boundary formulas. -/
lemma mul_le_gaussianBivariateStability {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a * b ≤ gaussianBivariateStability ρ a b := by
  by_cases hb0 : b = 0
  · subst b
    simp
  by_cases hb1 : b = 1
  · subst b
    simp [gaussianBivariateStability_one_right ρ a ha]
  have hb' : b ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hb.1 (Ne.symm hb0), lt_of_le_of_ne hb.2 hb1⟩
  have hc := (concaveOn_gaussianBivariateStability_left hρ hb').2
  have hchord := hc (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (a := 1 - a) (b := a)
    (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel _ _)
  have hρ' : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  simpa [smul_eq_mul, gaussianBivariateStability_one_left hρ' b hb] using hchord

/-- The two conditional-density factorizations of a correlated Gaussian pair
agree. [MN15, §2, equality of the coefficients in equations (2.4)–(2.5)]

**Proof sketch.** Expand the Gaussian densities into exponentials. Their
exponents agree because the conditional variance is one minus correlation
squared. The common normalizing constants then give the identity. -/
lemma standardGaussianPDF_correlated_symmetry (ρ s a b : ℝ)
    (hs : s ≠ 0) (hsq : s ^ 2 = 1 - ρ ^ 2) :
    standardGaussianPDF ((b - ρ * a) / s) * standardGaussianPDF a =
      standardGaussianPDF ((a - ρ * b) / s) * standardGaussianPDF b := by
  have hexp : -((b - ρ * a) / s) ^ 2 / 2 + -a ^ 2 / 2 =
      -((a - ρ * b) / s) ^ 2 / 2 + -b ^ 2 / 2 := by
    field_simp
    linear_combination (b ^ 2 - a ^ 2) * hsq
  simp only [standardGaussianPDF_eq]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 *
        Real.exp (-((b - ρ * a) / s) ^ 2 / 2 + -a ^ 2 / 2) := by
      rw [Real.exp_add]
      ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 *
        Real.exp (-((a - ρ * b) / s) ^ 2 / 2 + -b ^ 2 / 2) := by rw [hexp]
    _ = _ := by rw [Real.exp_add]; ring

end BooleanAnalysis.GaussianSpace
