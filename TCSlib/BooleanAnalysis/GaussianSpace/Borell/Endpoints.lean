/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Regularization
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Endpoint limits for Gaussian profile interpolation

## Main definitions

The existing Ornstein–Uhlenbeck averaging and profile functional are reused.

## Main results

The time profile converges to the original profile functional at time zero
and to the profile of the Gaussian mean at infinite time.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
/-- Ornstein–Uhlenbeck averaging converges to the original Gaussian
integrable function in L1 as positive time tends to zero.
[MN15, §2, semigroup endpoint at time zero] -/
lemma gaussianNoise_exp_neg_tendsto_self_L1
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => gaussianNoise (Real.exp (-t)) f x - f x) 1 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((Real.continuous_exp.comp continuous_neg).continuousAt.tendsto
        (x := (0 : ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  exact (gaussianNoise_tendsto_one hf).comp he


/-- At positive time Gaussian averaging of a clipped measurable function
is measurable and has values in the closed unit interval. -/
lemma gaussianNoise_exp_neg_unitInterval_data {δ : ℝ} (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) (hi : Integrable f γ)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ)) {t : ℝ} (ht : 0 < t) :
    Measurable (gaussianNoise (Real.exp (-t)) f) ∧
      ∀ x, gaussianNoise (Real.exp (-t)) f x ∈ Set.Icc (0 : ℝ) 1 := by
  have hr : Real.exp (-t) ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_trans (by norm_num) (Real.exp_pos _),
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
  refine ⟨(gaussianNoise_smooth hr hi).continuous.measurable, fun x => ?_⟩
  have hx := gaussianNoise_mem_clippedInterval hδ hf hrange (Real.exp (-t)) x
  exact ⟨hδ.le.trans hx.1, by linarith [hx.2]⟩

/-- For a clipped measurable function, the time profile functional converges
to the original profile integral as positive time tends to zero.
[MN15, §2, interpolation endpoint at zero]

**Proof sketch.** The Gaussian averages converge to the input in L1 and
remain measurable and bounded in the unit interval. Apply L1 continuity
of the bivariate profile functional. -/
lemma tendsto_integral_gaussianBivariateStability_noise_time_zero
    {ρ δ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ)) :
    Tendsto (fun t : ℝ => ∫ z, gaussianBivariateStability ρ
      (gaussianNoise (Real.exp (-t)) f z.1) (gaussianNoise (Real.exp (-t)) f z.2)
      ∂correlatedGaussianMeasure ρ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
        ∂correlatedGaussianMeasure ρ)) := by
  have hu (x) : f x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hδ.le.trans (hrange x).1, by linarith [(hrange x).2]⟩
  have hi : Integrable f γ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu x).1]
      exact (hu x).2)
  apply tendsto_integral_gaussianBivariateStability_of_L1 hρ hf hu
    _ (gaussianNoise_exp_neg_tendsto_self_L1 hi)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact gaussianNoise_exp_neg_unitInterval_data hδ hf hi hrange ht

/-- For a clipped measurable function, the time profile functional converges
to the profile at its two equal Gaussian means as time tends to infinity.
[MN15, §2, interpolation endpoint at infinity]

**Proof sketch.** Gaussian averages converge in L1 to their constant mean.
Apply L1 continuity of the profile functional and integrate the limiting
constant under the correlated Gaussian probability law. -/
lemma tendsto_integral_gaussianBivariateStability_noise_time_infty
    {ρ δ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ)) :
    Tendsto (fun t : ℝ => ∫ z, gaussianBivariateStability ρ
      (gaussianNoise (Real.exp (-t)) f z.1) (gaussianNoise (Real.exp (-t)) f z.2)
      ∂correlatedGaussianMeasure ρ) atTop
      (𝓝 (gaussianBivariateStability ρ (∫ x, f x ∂γ) (∫ x, f x ∂γ))) := by
  haveI : IsProbabilityMeasure (correlatedGaussianMeasure (n := n) ρ) := by
    rw [correlatedGaussianMeasure_eq]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hu (x) : f x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hδ.le.trans (hrange x).1, by linarith [(hrange x).2]⟩
  have hi : Integrable f γ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu x).1]
      exact (hu x).2)
  have hdata : ∀ᶠ t : ℝ in atTop, Measurable (gaussianNoise (Real.exp (-t)) f) ∧
      ∀ x, gaussianNoise (Real.exp (-t)) f x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact gaussianNoise_exp_neg_unitInterval_data hδ hf hi hrange ht
  have h := tendsto_integral_gaussianBivariateStability_of_L1 hρ
    (measurable_const : Measurable (fun _ : Fin n → ℝ => ∫ x, f x ∂γ))
    (fun _ => gaussianMean_mem_unitInterval hf hu) hdata
    (gaussianNoise_exp_neg_tendsto_mean_L1 hi)
  simpa only [integral_const, smul_eq_mul, measureReal_univ_eq_one, one_mul] using h


/-- Monotonicity of the positive-time profile functional implies Gaussian
Jensen for the initial clipped function. [MN15, §2, semigroup comparison]

**Proof sketch.** Every positive-time value is at most the limit at infinity.
Let time tend to zero from above to bound the initial profile integral. -/
lemma gaussianBivariateStability_jensen_clipped_of_time_monotone
    {ρ δ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ))
    (hmono : MonotoneOn (fun t : ℝ => ∫ z, gaussianBivariateStability ρ
      (gaussianNoise (Real.exp (-t)) f z.1) (gaussianNoise (Real.exp (-t)) f z.2)
      ∂correlatedGaussianMeasure ρ) (Set.Ioi (0 : ℝ))) :
    (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2) ∂correlatedGaussianMeasure ρ) ≤
      gaussianBivariateStability ρ (∫ x, f x ∂γ) (∫ x, f x ∂γ) := by
  have hle (t : ℝ) (ht : 0 < t) :
      (∫ z, gaussianBivariateStability ρ (gaussianNoise (Real.exp (-t)) f z.1)
        (gaussianNoise (Real.exp (-t)) f z.2) ∂correlatedGaussianMeasure ρ) ≤
      gaussianBivariateStability ρ (∫ x, f x ∂γ) (∫ x, f x ∂γ) := by
    apply ge_of_tendsto (tendsto_integral_gaussianBivariateStability_noise_time_infty hρ hδ hf hrange)
    filter_upwards [eventually_ge_atTop t] with u hu
    exact hmono ht (ht.trans_le hu) hu
  apply le_of_tendsto (tendsto_integral_gaussianBivariateStability_noise_time_zero hρ hδ hf hrange)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hle t ht


end BooleanAnalysis.GaussianSpace
