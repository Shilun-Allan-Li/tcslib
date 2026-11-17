/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.FunctionalContinuity
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.NoiseBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Smooth approximation for the Gaussian Jensen inequality

## Main definitions

Gaussian averaging and the bivariate profile functional are reused.

## Main results

Gaussian averaging preserves a closed interior probability interval. A Jensen
inequality for smooth functions with bounded derivatives extends to measurable
functions in that interval by Gaussian regularization.

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

/-- Averaging a measurable function with values in `[δ,1-δ]`, for positive δ,
preserves that interval, at every real correlation parameter.
[MN15, §2, regularization of clipped functions] -/
lemma gaussianNoise_mem_clippedInterval {δ : ℝ} (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ)) (r : ℝ) (x : Fin n → ℝ) :
    gaussianNoise r f x ∈ Set.Icc δ (1 - δ) := by
  have hm : Measurable (fun y : Fin n → ℝ =>
      f (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i)) := hf.comp (by fun_prop)
  have hi : Integrable (fun y : Fin n → ℝ =>
      f (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i)) γ :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hδ.le.trans (hrange _).1)]
      linarith [(hrange (fun i => r * x i + Real.sqrt (1 - r ^ 2) * y i)).2])
  constructor
  · calc
      δ = ∫ _y : Fin n → ℝ, δ ∂γ := by simp
      _ ≤ gaussianNoise r f x := integral_mono (integrable_const _) hi (fun y => (hrange _).1)
  · calc
      gaussianNoise r f x ≤ ∫ _y : Fin n → ℝ, (1 - δ) ∂γ :=
        integral_mono hi (integrable_const _) (fun y => (hrange _).2)
      _ = 1 - δ := by simp

/-- To prove Gaussian Jensen for a clipped measurable function, it suffices
to prove it for C2 functions with bounded first and second derivatives in the
same clipped interval. [MN15, §2, Gaussian smoothing approximation]

**Proof sketch.** Gaussian noise at correlations tending to one approximates
the input in L1 and preserves its clipped range. At each interior correlation
the smoothed function is C2 and has uniformly bounded first and second
spatial derivatives. Apply the smooth inequality to these functions and pass
to the limit using L1 continuity of the profile functional. -/
lemma gaussianBivariateStability_jensen_clipped_of_smooth {ρ δ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hδ : 0 < δ)
    (hsmooth : ∀ g : (Fin n → ℝ) → ℝ, ContDiff ℝ 2 g →
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ g x‖ ≤ M) →
      (∃ K : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K) →
      (∀ x, g x ∈ Set.Icc δ (1 - δ)) →
      (∫ z, gaussianBivariateStability ρ (g z.1) (g z.2)
        ∂correlatedGaussianMeasure ρ) ≤
      gaussianBivariateStability ρ (∫ x, g x ∂γ) (∫ x, g x ∂γ))
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ)) :
    (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
      ∂correlatedGaussianMeasure ρ) ≤
    gaussianBivariateStability ρ (∫ x, f x ∂γ) (∫ x, f x ∂γ) := by
  have hu (x) : f x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hδ.le.trans (hrange x).1, by linarith [(hrange x).2]⟩
  have hb (x) : |f x| ≤ 1 := by rw [abs_of_nonneg (hu x).1]; exact (hu x).2
  have hi : Integrable f γ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hevent : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r ∈ Set.Ioo (-1 : ℝ) 1 := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hl hr
    exact ⟨hl, hr⟩
  have hF : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), Measurable (gaussianNoise r f) ∧
      ∀ x, gaussianNoise r f x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hevent] with r hr
    refine ⟨(gaussianNoise_smooth hr hi).continuous.measurable, fun x => ?_⟩
    have hx := gaussianNoise_mem_clippedInterval hδ hf hrange r x
    exact ⟨hδ.le.trans hx.1, by linarith [hx.2]⟩
  apply gaussianBivariateStability_jensen_of_L1 hρ hf hu hF
    (gaussianNoise_tendsto_one hi)
  filter_upwards [hevent] with r hr
  exact hsmooth (gaussianNoise r f) ((gaussianNoise_smooth hr hi).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    ⟨(n : ℝ) * (1 + 1 / (1 - r ^ 2)), norm_fderiv_gaussianNoise_le hr hf hb⟩
    ⟨(n : ℝ) ^ 2 * (2 / (1 - r ^ 2)), norm_fderiv_fderiv_gaussianNoise_le hr hf hb⟩
    (gaussianNoise_mem_clippedInterval hδ hf hrange r)

/-- Gaussian Jensen inequalities for every positive clipping level imply
Gaussian Jensen for all measurable unit-interval functions.
[MN15, §2, removal of the endpoint clipping]

**Proof sketch.** Replace f by `δ + (1-2δ)f`. This has range `[δ,1-δ]`,
and its pointwise distance from f is at most δ. Consequently the L1 error
vanishes as δ tends to zero through positive values. Pass the clipped
inequalities to the limit using the L1 closure lemma. -/
lemma gaussianBivariateStability_jensen_of_clipped {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (hclipped : ∀ δ : ℝ, 0 < δ → ∀ g : (Fin n → ℝ) → ℝ,
      Measurable g → (∀ x, g x ∈ Set.Icc δ (1 - δ)) →
      (∫ z, gaussianBivariateStability ρ (g z.1) (g z.2)
        ∂correlatedGaussianMeasure ρ) ≤
      gaussianBivariateStability ρ (∫ x, g x ∂γ) (∫ x, g x ∂γ))
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
      ∂correlatedGaussianMeasure ρ) ≤
    gaussianBivariateStability ρ (∫ x, f x ∂γ) (∫ x, f x ∂γ) := by
  let F := fun δ x => δ + (1 - 2 * δ) * f x
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
        nhdsWithin_le_nhds] with δ hl hu
    exact ⟨hl, hu⟩
  have hFmeas (δ : ℝ) : Measurable (F δ) := by dsimp [F]; fun_prop
  have hFclip (δ : ℝ) (hδ : 0 < δ ∧ δ < 1 / 2) (x) :
      F δ x ∈ Set.Icc δ (1 - δ) := by
    have ha : 0 ≤ 1 - 2 * δ := by linarith [hδ.2]
    have h₀ := mul_nonneg ha (hrange x).1
    have h₁ := mul_nonneg ha (sub_nonneg.mpr (hrange x).2)
    dsimp [F]
    constructor <;> nlinarith
  have hF : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), Measurable (F δ) ∧
      ∀ x, F δ x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hevent] with δ hδ
    refine ⟨hFmeas δ, fun x => ?_⟩
    have hx := hFclip δ hδ x
    exact ⟨hδ.1.le.trans hx.1, by linarith [hx.2]⟩
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      eLpNorm (fun x => F δ x - f x) 1 γ ≤ ENNReal.ofReal δ := by
    filter_upwards [hevent] with δ hδ
    have hb (x) : ‖F δ x - f x‖ ≤ δ := by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      have h₀ := mul_nonneg hδ.1.le (hrange x).1
      have h₁ := mul_nonneg hδ.1.le (sub_nonneg.mpr (hrange x).2)
      dsimp [F]
      constructor <;> nlinarith
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      (eLpNorm_le_of_ae_bound (μ := γ) (p := 1) (Eventually.of_forall hb))
  have ht : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun δ => eLpNorm (fun x => F δ x - f x) 1 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => zero_le _) hbound
  apply gaussianBivariateStability_jensen_of_L1 hρ hf hrange hF hlim
  filter_upwards [hevent] with δ hδ
  exact hclipped δ hδ.1 (F δ) (hFmeas δ) (hFclip δ hδ)

end BooleanAnalysis.GaussianSpace
