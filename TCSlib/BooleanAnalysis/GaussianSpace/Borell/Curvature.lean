/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileCalculus

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Curvature of the bivariate Gaussian profile

## Main definitions

The profile's conditional-cdf slope and joint density are reused from
`Borell.Definitions`.

## Main results

The correlation-weighted curvature quadratic factors as a nonpositive
multiple of a square. This supplies the sign in Borell interpolation.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2,
  Lemma 2.2 and equations (2.4)–(2.5).
-/

open MeasureTheory
open scoped Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The correlation-weighted curvature quadratic of the bivariate profile is
minus the correlation times its joint density times a squared normalized
difference. [MN15, §2, Lemma 2.2, pointwise curvature calculation]

**Proof sketch.** Substitute the two derivatives of the conditional-cdf slope.
The two conditional density factorizations agree, so the coefficients can be
expressed using a single joint density. Clearing their nonzero Gaussian
density denominators gives the square by a polynomial identity. -/
lemma gaussianBivariate_curvature_factor {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (u v : ℝ) :
    deriv (fun p => gaussianBivariateSlope ρ p b) a * u ^ 2 +
      2 * ρ * deriv (fun p => gaussianBivariateSlope ρ a p) b * u * v +
      deriv (fun p => gaussianBivariateSlope ρ p a) b * v ^ 2 =
        -ρ * gaussianBivariateDensity ρ a b *
          (u / gaussianIsoperimetric a - v / gaussianIsoperimetric b) ^ 2 := by
  let U := gaussianIsoperimetric a
  let V := gaussianIsoperimetric b
  let s := Real.sqrt (1 - ρ ^ 2)
  let c := standardGaussianPDF ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) / s)
  let d := standardGaussianPDF ((standardGaussianQuantile a - ρ * standardGaussianQuantile b) / s)
  have hU : U ≠ 0 := (standardGaussianPDF_pos _).ne'
  have hV : V ≠ 0 := (standardGaussianPDF_pos _).ne'
  have hv : 0 < 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hsym : c * U = d * V :=
    standardGaussianPDF_correlated_symmetry ρ s _ _ hs (Real.sq_sqrt hv.le)
  simp only [gaussianBivariateSlope,
    (hasDerivAt_gaussianBivariateSlope_left ρ b ha).deriv,
    (hasDerivAt_gaussianBivariateSlope_right ρ a hb).deriv,
    (hasDerivAt_gaussianBivariateSlope_left ρ a hb).deriv]
  change (-ρ * c / (s * U)) * u ^ 2 + 2 * ρ * (c / (s * V)) * u * v +
    (-ρ * d / (s * V)) * v ^ 2 =
      -ρ * (U * c / s) * (u / U - v / V) ^ 2
  rw [show d = c * U / V from (eq_div_iff hV).mpr hsym.symm]
  field_simp
  ring

/-- The totalized joint-density expression is nonnegative. -/
lemma gaussianBivariateDensity_nonneg (ρ a b : ℝ) :
    0 ≤ gaussianBivariateDensity ρ a b := by
  unfold gaussianBivariateDensity gaussianIsoperimetric
  exact div_nonneg
    (mul_nonneg (standardGaussianPDF_pos _).le (standardGaussianPDF_pos _).le)
    (Real.sqrt_nonneg _)

/-- The correlation-weighted curvature quadratic of the bivariate Gaussian
profile is nonpositive at interior volumes and positive correlation.
[MN15, §2, Lemma 2.2, sign of the interpolation derivative]

**Proof sketch.** The curvature factorization is minus the positive correlation
times a nonnegative joint density and a square. -/
lemma gaussianBivariate_curvature_nonpos {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (u v : ℝ) :
    deriv (fun p => gaussianBivariateSlope ρ p b) a * u ^ 2 +
      2 * ρ * deriv (fun p => gaussianBivariateSlope ρ a p) b * u * v +
      deriv (fun p => gaussianBivariateSlope ρ p a) b * v ^ 2 ≤ 0 := by
  rw [gaussianBivariate_curvature_factor ⟨by linarith [hρ.1], hρ.2⟩ ha hb u v]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.1.le)
      (gaussianBivariateDensity_nonneg ρ a b)) (sq_nonneg _)

end BooleanAnalysis.GaussianSpace
