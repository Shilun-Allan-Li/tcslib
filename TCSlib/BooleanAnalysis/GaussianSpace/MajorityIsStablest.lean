/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell
import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceExtensions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantitative general-volume Majority Is Stablest: statement layer

## Main definitions

Boolean noise stability, maximum influence and noisy influence use their existing
definitions. The extremal Gaussian profile is defined in `Borell`.

## Main results

Equation (11.39), including the source's no-notables hypothesis and a universal
constant independent of correlation. The balanced qualitative theorem already
exists in `ThresholdFunctions.Gaussian` and is not restated here.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, General-Volume Majority Is Stablest, (11.39).
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- General-volume Majority Is Stablest has error
`C log(log(1/ε))/((1-ρ) log(1/ε))` for functions with no notable coordinates.
[OD14, §11.7, equation (11.39)] The bound `ε ≤ exp(-2)` specifies the source's
small-ε asymptotic regime, keeping the logarithmic error bounded away from its spurious zero at ε = exp(-1).
The constant is universal, in particular independent of `ρ`.

**Proof sketch.** Smooth the Boolean function, use no-notables invariance with
the distance-to-interval test to clip its Gaussian extension, and compare the
two stabilities. Apply Borell to the clipped extension. Balance smoothing and
invariance errors at the logarithmic scale stated in the source. -/
theorem majority_is_stablest_general_volume :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-2) →
      (∀ i, KKL.noisyInfluence (1 - 1 / Real.log (1 / ε)) i f ≤ ε) →
      ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 →
        noiseStability ρ f ≤ gaussianHalfspaceStability ρ (expect f) +
          C * Real.log (Real.log (1 / ε)) / ((1 - ρ) * Real.log (1 / ε)) := sorry

/-- The same quantitative general-volume bound holds under ordinary small
influences. [OD14, §11.7, equation (11.39), first hypothesis]
This is the source's quantitative unit-interval theorem, distinct from the
existing qualitative balanced `[-1,1]` theorem.

**Proof sketch.** Ordinary influence dominates noisy influence at the required
parameter. Apply the no-notables form with the same universal constant. -/
theorem majority_is_stablest_general_volume_maxInfluence :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-2) →
      maxInfluence f ≤ ε → ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 →
        noiseStability ρ f ≤ gaussianHalfspaceStability ρ (expect f) +
          C * Real.log (Real.log (1 / ε)) / ((1 - ρ) * Real.log (1 / ε)) := sorry

end BooleanAnalysis.GaussianSpace
