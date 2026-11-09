/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.LiminfLimsup
import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianTail

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Definitions for the missing parts of O'Donnell's Chapter 11

## Main definitions

* `rotationSensitivity`: disagreement along a Gaussian rotation.
* `gaussianSurfaceArea`: the extended nonnegative rotation-limit perimeter.
* `closedGaussianProfile`: the endpoint adapter for the existing isoperimetric profile.

## Main results

There are no theorem statements here. Theorems live in `Rotation`, `SurfaceArea`,
`Bobkov`, and `Invariance`; `COVERAGE.md` records their proof status. Standard Gaussian measures,
multilinear polynomials, real-input evaluation, and influence are reused, not redeclared.
`Inputs` separately bundles Hypothesis 11.65 without making the geometric definitions
import the Boolean Fourier library. The upstream Hermite, Ornstein–Uhlenbeck, and Berry–Esseen developments are recorded
in `COVERAGE.md`; this module does not duplicate their definitions.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Chapter 11, Definitions 11.42 and 11.48,
  Hypothesis 11.65, and §11.4, equation (11.15).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The rotation sensitivity of a Borel set is the probability that membership changes
between `g` and `cos θ * g + sin θ * g'`, for independent standard Gaussian vectors.
This realizes the `cos θ`-correlated pair in [OD14, Def. 11.42; Thm. 11.43 (proof)].
The formula is total for arbitrary sets; results below explicitly require measurability.
The product law is Mathlib's `Measure.pi` applied to the existing standard Gaussian law. -/
noncomputable def rotationSensitivity {n : ℕ} (A : Set (Fin n → ℝ)) (θ : ℝ) : ℝ :=
  (((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
      (Measure.pi fun _ : Fin n => standardGaussianMeasure))
    {z : (Fin n → ℝ) × (Fin n → ℝ) |
      ¬ (z.1 ∈ A ↔ (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ A)}).toReal

/-- The Gaussian surface area of a Borel set, with values in `[0,∞]`, is
`sqrt (π/2)` times its infinitesimal rotation sensitivity. [OD14, Def. 11.48]
We use an extended nonnegative lower limit to define it before proving existence of
the right limit; `surfaceArea_rotation_limit` states that existence assertion.
Unlike a surface integral over the topological frontier, this definition is unchanged
by null modifications of a measurable set. In particular, it is not the weighted
frontier Hausdorff measure found in ProbabilityApproximation; see `COVERAGE.md`. -/
noncomputable def gaussianSurfaceArea {n : ℕ} (A : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  liminf (fun θ : ℝ =>
    ENNReal.ofReal (Real.sqrt (Real.pi / 2) * rotationSensitivity A θ / θ))
    (𝓝[>] (0 : ℝ))

/-- The Gaussian isoperimetric profile on the closed probability interval has value zero
at both endpoints and agrees with the existing `gaussianIsoperimetric` on `(0,1)`.
[OD14, Def. 5.26; §11.4, equation (11.15)]
This is an endpoint adapter, not a second construction of the interior profile:
`ThresholdFunctions.gaussianIsoperimetric` deliberately totalizes a real quantile and
only specifies its intended behavior in the open interval. That totalization does not
give the zero endpoint values required for Bobkov's inequality. Outside `[0,1]` we
also set this adapter to zero; no results use those values. -/
noncomputable def closedGaussianProfile (α : ℝ) : ℝ :=
  if α ∈ Set.Ioo (0 : ℝ) 1 then gaussianIsoperimetric α else 0

end BooleanAnalysis.GaussianSpace
