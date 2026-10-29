/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Moment hypotheses for the fourth-order invariance principle

## Main definitions

* `HasInvarianceMoments`: Hypothesis 11.65, using the existing `IsBReasonable` predicate.

## Main results

* `HasInvarianceMoments.identDistrib`: the input hypotheses depend only on the input law.

The separate definition layer reuses general-input Bonami definitions without importing
Gaussian geometry. Polynomial evaluation, degree, variance, and influence already exist.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Definition 11.63 and Hypothesis 11.65.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity

/-- An input obeys Hypothesis 11.65 when it is 9-reasonable, has mean zero and second
moment one, and has third moment zero. [OD14, Hyp. 11.65]
The existing `IsBReasonable` field supplies probability, finite fourth moment, and the
fourth-to-second moment bound; with second moment one this is exactly `E[X⁴] ≤ 9`.
Finite moments prevent the totalized real integral from hiding nonintegrability. -/
structure HasInvarianceMoments {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- The existing reasonability predicate supplies the fourth-moment hypothesis. -/
  reasonable : IsBReasonable X μ 9
  /-- The first moment vanishes. -/
  mean : (∫ ω, X ω ∂μ) = 0
  /-- The second moment is one. -/
  second : (∫ ω, X ω ^ 2 ∂μ) = 1
  /-- The third moment vanishes. -/
  third : (∫ ω, X ω ^ 3 ∂μ) = 0

/-- The moment hypotheses for invariance are preserved under equality in
distribution. [OD14, §11.6, Hyp. 11.65]

**Proof sketch.** Transfer finite fourth moments and each moment integral under
equality in distribution. These give the same moment equalities and reasonability bound. -/
theorem HasInvarianceMoments.identDistrib
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ξ → ℝ}
    (hX : HasInvarianceMoments X μ)
    (hXY : ProbabilityTheory.IdentDistrib X Y μ ν) :
    HasInvarianceMoments Y ν := by
  refine
    { reasonable :=
        { probability := inferInstance
          one_le := hX.reasonable.one_le
          memLp := hXY.memLp_snd hX.reasonable.memLp
          moment_le := ?_ }
      mean := hXY.integral_eq.symm.trans hX.mean
      second := (hXY.pow (n := 2)).integral_eq.symm.trans hX.second
      third := (hXY.pow (n := 3)).integral_eq.symm.trans hX.third }
  change (∫ ω, Y ω ^ 4 ∂ν) ≤ 9 * (∫ ω, Y ω ^ 2 ∂ν) ^ 2
  rw [← (hXY.pow (n := 4)).integral_eq, ← (hXY.pow (n := 2)).integral_eq]
  exact hX.reasonable.moment_le

end BooleanAnalysis.GaussianSpace
