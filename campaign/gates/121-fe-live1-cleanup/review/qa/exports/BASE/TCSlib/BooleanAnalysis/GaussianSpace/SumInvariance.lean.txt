/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Smoothing
import TCSlib.BooleanAnalysis.ThresholdFunctions.Gaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Invariance for sums and scalar distribution comparison

## Main definitions

* `thirdMomentSum`: the third absolute moment budget of a finite family.
* `MatchesSumMoments`: independent families with finite third moments and matching
  first and second moments, allowing different probability spaces.
* `levyDistance`: the one-dimensional Lévy distance defined by shifted CDF inequalities.

## Main results

The unnumbered sum invariance principle, Variant Berry–Esseen, Proposition 11.58,
and Corollaries 11.59 and 11.61–11.62 are statement-only obligations.
The classical Berry–Esseen theorem and Kolmogorov distance are reused from
`ThresholdFunctions.Gaussian`. No proof in this file is claimed complete.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.5, pp. 351–357.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The third absolute moment budget of a finite input family.
[OD14, §11.5, Berry–Esseen and sum invariance principles] -/
noncomputable def thirdMomentSum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Fin n → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ

/-- Two independent input families have matching first and second moments and finite
third absolute moments. The families may live on different probability spaces;
independence between the two families is unnecessary. [OD14, §11.5, sum invariance] -/
structure MatchesSumMoments {n : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ)
    (μ : Measure Ω) (ν : Measure Ξ) : Prop where
  /-- The first family is independent. -/
  independent_left : iIndepFun X μ
  /-- The second family is independent. -/
  independent_right : iIndepFun Y ν
  /-- Finite third moments for the first family. -/
  memLp_left : ∀ i, MemLp (X i) 3 μ
  /-- Finite third moments for the second family. -/
  memLp_right : ∀ i, MemLp (Y i) 3 ν
  /-- Matching means; no zero-mean assumption is imposed. -/
  first : ∀ i, (∫ ω, X i ω ∂μ) = ∫ ω, Y i ω ∂ν
  /-- Matching second moments; no normalization is imposed. -/
  second : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = ∫ ω, Y i ω ^ 2 ∂ν

/-- The one-dimensional Lévy distance between probability laws is the infimum of
nonnegative shifts making their CDFs sandwich one another. This is the source's
CDF metric, distinct from the general-space Lévy–Prokhorov metric.
[OD14, Cor. 11.61 and §11.6, Cor. 11.70]
The formula is total on measures; its intended domain is probability measures. -/
noncomputable def levyDistance (μ ν : Measure ℝ) : ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ ∀ u : ℝ,
    (ν (Set.Iic (u - ε))).toReal - ε ≤ (μ (Set.Iic u)).toReal ∧
      (μ (Set.Iic u)).toReal ≤ (ν (Set.Iic (u + ε))).toReal + ε}

/-- Matching first and second moments give a third-order comparison for sums with
the exact Taylor constant `C/6`. [OD14, §11.5, Invariance Principle for Sums]

**Proof sketch.** Independently couple the two families and replace one coordinate
at a time. Taylor-expand the test to order two; the matching moments cancel those
terms. Bound the cubic remainders and sum them along the replacement sequence. -/
theorem sum_invariance {n : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ) (hXY : MatchesSumMoments X Y μ ν)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ) (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ t, |iteratedDeriv 3 ψ t| ≤ C) :
    |(∫ ω, ψ (∑ i, X i ω) ∂μ) - (∫ ω, ψ (∑ i, Y i ω) ∂ν)| ≤
      (C / 6) * (thirdMomentSum X μ + thirdMomentSum Y ν) := sorry

/-- A centered variance-one sum is close to a standard Gaussian under a C³ test,
with the exact constant from the third absolute Gaussian moment.
[OD14, §11.5, Variant Berry–Esseen Theorem, equation (11.28)]

**Proof sketch.** Compare each summand to an independent Gaussian of the same
variance using sum invariance. Bound the sum of Gaussian third moments by
`2 sqrt(2/π)` times the original third-moment budget using monotonicity of norms. -/
theorem variant_berryEsseen {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hI : iIndepFun X μ) (hX : ∀ i, MemLp (X i) 3 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hvar : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) = 1)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ) (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ t, |iteratedDeriv 3 ψ t| ≤ C) :
    |(∫ ω, ψ (∑ i, X i ω) ∂μ) - (∫ z, ψ z ∂standardGaussianMeasure)| ≤
      ((1 + 2 * Real.sqrt (2 / Real.pi)) / 6) * C * thirdMomentSum X μ := sorry

/-- Every Lipschitz real function has a single smooth approximation controlling
all positive derivative orders; the constants depend only on the order.
[OD14, Prop. 11.58] This is the full C∞ statement, supplementing the existing C⁴
interval-average construction used in the proved invariance theorem.

**Proof sketch.** Convolve with a Gaussian of width `η`. The first absolute
Gaussian moment bounds the approximation error. Differentiate the Gaussian
kernel and use cancellation to bound each derivative by a Lipschitz increment. -/
theorem exists_smooth_lipschitz_approximation :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ → ∀ η : ℝ, 0 < η →
        ∃ ψs : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψs ∧
          (∀ t, |ψ t - ψs t| ≤ (c : ℝ) * η) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ t,
            |iteratedDeriv k ψs t| ≤ C k * (c : ℝ) / η ^ (k - 1) := sorry

/-- A Lipschitz test compares matching-moment sums at cube-root error in their
third-moment budget, with a universal constant. [OD14, Cor. 11.59]

**Proof sketch.** Smooth the test at width the cube root of the moment budget,
apply sum invariance, and add the two uniform approximation errors. Treat zero
budget by equality of the deterministic input laws. -/
theorem sum_invariance_lipschitz :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} {Ω Ξ : Type*}
      [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ), MatchesSumMoments X Y μ ν →
      ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
        |(∫ ω, ψ (∑ i, X i ω) ∂μ) - (∫ ω, ψ (∑ i, Y i ω) ∂ν)| ≤
          K * (c : ℝ) * (thirdMomentSum X μ + thirdMomentSum Y ν) ^ (1 / 3 : ℝ) := sorry

/-- The Lévy distance of matching-moment sums has fourth-root error in their
third-moment budget. [OD14, Cor. 11.61]

**Proof sketch.** Sandwich a half-line indicator between translated smooth
cutoffs, whose third derivatives are of order the inverse cube of the width.
Choose the fourth root of the moment budget as width and take the CDF infimum. -/
theorem sum_invariance_levy :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} {Ω Ξ : Type*}
      [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ), MatchesSumMoments X Y μ ν →
        levyDistance (μ.map fun ω => ∑ i, X i ω) (ν.map fun ω => ∑ i, Y i ω) ≤
          K * (thirdMomentSum X μ + thirdMomentSum Y ν) ^ (1 / 4 : ℝ) := sorry

/-- The elementary replacement proof gives a fourth-root Kolmogorov estimate
for a centered variance-one sum. [OD14, Cor. 11.62]
The sharper classical linear-error theorem is already `ThresholdFunctions.berryEsseen`.

**Proof sketch.** Apply the Lévy comparison with independent Gaussians of matching
variances, then bound the Gaussian probability of a short interval by its length
times the maximum density. Absorb the Gaussian third moments into the budget. -/
theorem berryEsseen_quarter_power :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ),
      iIndepFun X μ → (∀ i, MemLp (X i) 3 μ) →
      (∀ i, (∫ ω, X i ω ∂μ) = 0) → (∑ i, ∫ ω, X i ω ^ 2 ∂μ) = 1 →
        kolmogorovDistance (μ.map fun ω => ∑ i, X i ω) standardGaussianMeasure ≤
          K * thirdMomentSum X μ ^ (1 / 4 : ℝ) := sorry

end BooleanAnalysis.GaussianSpace
