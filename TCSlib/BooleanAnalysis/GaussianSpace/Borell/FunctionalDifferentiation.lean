/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileSmoothness
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false

/-!
# Differentiation of the integrated Gaussian profile

## Main definitions

The bivariate profile and its conditional cdf slopes are reused.

## Main results

* `hasDerivAt_integral_gaussianBivariateStability`: the chain rule for the
  profile functional under a locally integrable derivative bound.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
/-- The conditional cdf slope lies in the closed unit interval for all arguments. -/
lemma gaussianBivariateSlope_mem_unitInterval (ρ a b : ℝ) :
    gaussianBivariateSlope ρ a b ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(standardGaussianCDF_pos _).le, (standardGaussianCDF_lt_one _).le⟩
/-- The conditional Gaussian cdf slope of two measurable functions with
interior probability values is measurable. -/
lemma measurable_gaussianBivariateSlope_comp {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ℝ) {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfrange : ∀ x, f x ∈ Set.Ioo (0 : ℝ) 1)
    (hgrange : ∀ x, g x ∈ Set.Ioo (0 : ℝ) 1) :
    Measurable (fun x => gaussianBivariateSlope ρ (f x) (g x)) := by
  have hq : ContinuousOn standardGaussianQuantile (Set.Ioo (0 : ℝ) 1) :=
    fun a ha => (hasDerivAt_standardGaussianQuantile ha).continuousAt.continuousWithinAt
  have hqf : Measurable (fun x => standardGaussianQuantile (f x)) :=
    hq.restrict.measurable.comp (hf.subtype_mk (h := hfrange))
  have hqg : Measurable (fun x => standardGaussianQuantile (g x)) :=
    hq.restrict.measurable.comp (hg.subtype_mk (h := hgrange))
  exact continuous_standardGaussianCDF.measurable.comp
    ((hqg.sub (hqf.const_mul ρ)).div_const _)
/-- For two measurable time-dependent functions with interior probability
values, a common locally integrable bound on their time derivatives permits
differentiating their integrated Gaussian profile. The derivative is the
integral of the two conditional cdf slopes times the corresponding derivatives.
[MN15, §2, differentiation of the interpolation functional]

**Proof sketch.** The profile gradient gives the pointwise chain rule. Each
slope lies between zero and one, so the sum of the absolute input derivatives
dominates the profile derivative. The profile itself is bounded and the
prescribed dominating function is integrable; differentiation under the
integral follows. -/
lemma hasDerivAt_integral_gaussianBivariateStability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (f g f' g' : ℝ → Ω → ℝ) {r δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ q, Measurable (f q)) (hg : ∀ q, Measurable (g q))
    (hf' : Measurable (f' r)) (hg' : Measurable (g' r))
    (hfrange : ∀ q ∈ Metric.ball r δ, ∀ x, f q x ∈ Set.Ioo (0 : ℝ) 1)
    (hgrange : ∀ q ∈ Metric.ball r δ, ∀ x, g q x ∈ Set.Ioo (0 : ℝ) 1)
    (hfd : ∀ x q, q ∈ Metric.ball r δ → HasDerivAt (fun t => f t x) (f' q x) q)
    (hgd : ∀ x q, q ∈ Metric.ball r δ → HasDerivAt (fun t => g t x) (g' q x) q)
    (B : Ω → ℝ) (hB : Integrable B μ)
    (hbound : ∀ x q, q ∈ Metric.ball r δ → |f' q x| + |g' q x| ≤ B x) :
    Integrable (fun x => gaussianBivariateSlope ρ (f r x) (g r x) * f' r x +
        gaussianBivariateSlope ρ (g r x) (f r x) * g' r x) μ ∧
    HasDerivAt (fun q => ∫ x, gaussianBivariateStability ρ (f q x) (g q x) ∂μ)
      (∫ x, gaussianBivariateSlope ρ (f r x) (g r x) * f' r x +
        gaussianBivariateSlope ρ (g r x) (f r x) * g' r x ∂μ) r := by
  let F := fun q x => gaussianBivariateStability ρ (f q x) (g q x)
  let D := fun q x => gaussianBivariateSlope ρ (f q x) (g q x) * f' q x +
    gaussianBivariateSlope ρ (g q x) (f q x) * g' q x
  have hr : r ∈ Metric.ball r δ := Metric.mem_ball_self hδ
  have hunitf (q) (hq : q ∈ Metric.ball r δ) (x) : f q x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hfrange q hq x).1.le, (hfrange q hq x).2.le⟩
  have hunitg (q) (hq : q ∈ Metric.ball r δ) (x) : g q x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hgrange q hq x).1.le, (hgrange q hq x).2.le⟩
  have hFmeas : ∀ᶠ q in 𝓝 r, AEStronglyMeasurable (F q) μ := by
    filter_upwards [Metric.ball_mem_nhds r hδ] with q hq
    exact (measurable_gaussianBivariateStability_comp ⟨hρ.1.le, hρ.2.le⟩
      (hf q) (hg q) (hunitf q hq) (hunitg q hq)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D r) μ :=
    (((measurable_gaussianBivariateSlope_comp ρ (hf r) (hg r)
      (hfrange r hr) (hgrange r hr)).mul hf').add
      ((measurable_gaussianBivariateSlope_comp ρ (hg r) (hf r)
        (hgrange r hr) (hfrange r hr)).mul hg')).aestronglyMeasurable
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) hδ hFmeas
    (integrable_gaussianBivariateStability_comp μ ⟨hρ.1.le, hρ.2.le⟩
      (hf r) (hg r) (hunitf r hr) (hunitg r hr)) hDmeas
    (Eventually.of_forall fun x q hq => ?_) hB
    (Eventually.of_forall fun x q hq => ?_)
  · calc
      ‖D q x‖ ≤ |gaussianBivariateSlope ρ (f q x) (g q x) * f' q x| +
          |gaussianBivariateSlope ρ (g q x) (f q x) * g' q x| := norm_add_le _ _
      _ ≤ |f' q x| + |g' q x| := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (gaussianBivariateSlope_mem_unitInterval _ _ _).1]
          exact mul_le_of_le_one_left (abs_nonneg _) (gaussianBivariateSlope_mem_unitInterval _ _ _).2
        · rw [abs_mul, abs_of_nonneg (gaussianBivariateSlope_mem_unitInterval _ _ _).1]
          exact mul_le_of_le_one_left (abs_nonneg _) (gaussianBivariateSlope_mem_unitInterval _ _ _).2
      _ ≤ B x := hbound x q hq
  · simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, D, F]
      using (hasFDerivAt_gaussianBivariateStability hρ (hfrange q hq x)
        (hgrange q hq x)).comp_hasDerivAt q ((hfd x q hq).prodMk (hgd x q hq))
end BooleanAnalysis.GaussianSpace
