/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianTail
import Mathlib.MeasureTheory.Measure.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian halfspace probability profiles

## Main definitions

* `gaussianHalfspaceStability`: the endpoint-aware diagonal profile Λρ.
* `gaussianBivariateStability`: the two-volume profile Jρ, with canonical endpoint values.
* `gaussianBivariateSlope`: its conditional-cdf slope in the first volume.
* `gaussianBivariateDensity`: the joint density at the two volume quantiles.

## Main results

Definitions only. `Borell.Bivariate` proves the relation between the two profiles
and their regularity properties.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3 and §11.7, equation (11.39).
* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §1.2.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The stability Λρ(α) of a Gaussian halfspace of volume α. Interior thresholds
use the existing Gaussian quantile; endpoint volumes have stability zero and one.
[OD14, §11.3, General-volume Borell; §11.7, equation (11.39)]
The existing `gaussianQuadrantProbability` covers only the threshold-zero case. -/
noncomputable def gaussianHalfspaceStability (ρ α : ℝ) : ℝ :=
  if α ≤ 0 then 0 else if 1 ≤ α then 1 else
    ((standardGaussianMeasure.prod standardGaussianMeasure)
      {z : ℝ × ℝ | z.1 ≤ standardGaussianQuantile α ∧
        ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ standardGaussianQuantile α}).toReal

/-- The joint probability Jρ(α,β) of two Gaussian lower halfspaces of volumes
α and β. [MN15, §1.2, definition of J]

Comparing the Gaussian cdf with the volumes gives the usual quantile thresholds
in the open unit square and the canonical values at its boundary. This also
extends the profile outside that square by clipping the volumes. The Gaussian
law interpretation requires correlation in `[-1,1]`. -/
noncomputable def gaussianBivariateStability (ρ α β : ℝ) : ℝ :=
  (standardGaussianMeasure.prod standardGaussianMeasure).real
    {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α ∧
      standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ β}

/-- The conditional Gaussian cdf at two volume quantiles.
On the open probability square and for `-1 < ρ < 1`, this is the first-volume
derivative of the bivariate profile. [MN15, §2, Lemma 2.1]
The expression is totalized for other arguments, without a derivative claim there. -/
noncomputable def gaussianBivariateSlope (ρ a b : ℝ) : ℝ :=
  standardGaussianCDF ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) /
    Real.sqrt (1 - ρ ^ 2))

/-- The joint Gaussian density at two volume quantiles, written as a marginal
density times a conditional density. Its intended domain is the open
probability square and `-1 < ρ < 1`. [MN15, §2, equations (2.4)–(2.5)] -/
noncomputable def gaussianBivariateDensity (ρ a b : ℝ) : ℝ :=
  gaussianIsoperimetric a * standardGaussianPDF
    ((standardGaussianQuantile b - ρ * standardGaussianQuantile a) /
      Real.sqrt (1 - ρ ^ 2)) / Real.sqrt (1 - ρ ^ 2)

end BooleanAnalysis.GaussianSpace
