/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.TimeDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Endpoints
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.GeneratorSign
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Gaussian Jensen inequality

## Main definitions

The bivariate Gaussian profile and correlated Gaussian law are reused.

## Main results

* `gaussianBivariateStability_jensen`: the expected profile of two correlated
  function values is at most the profile at the two equal Gaussian means.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Nonnegative derivatives on positive times imply monotonicity there. -/
private lemma monotoneOn_Ioi_of_hasDerivAt_nonneg {F F' : ℝ → ℝ}
    (hd : ∀ t, 0 < t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, 0 < t → 0 ≤ F' t) : MonotoneOn F (Set.Ioi (0 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · rw [isOpen_Ioi.interior_eq]
    intro t ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · rw [isOpen_Ioi.interior_eq]
    intro t ht
    rw [(hd t ht).deriv]
    exact hpos t ht


/-- Gaussian Jensen holds for clipped C2 functions with bounded first and
second derivatives. [MN15, §2, semigroup proof of Gaussian Jensen]

**Proof sketch.** Average the function by the Ornstein–Uhlenbeck semigroup.
The time derivative of its profile functional is the expectation of the
two slope-weighted generators. Their sum is nonnegative by Gaussian
integration by parts and the profile curvature estimate. Thus the profile
functional increases in time. Its limits at zero and infinity give the claim. -/
lemma gaussianBivariateStability_jensen_smooth_clipped {n : ℕ} {ρ δ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {M K : ℝ}
    (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1 - δ)) :
    (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
      ∂correlatedGaussianMeasure ρ) ≤
    gaussianBivariateStability ρ
      (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) := by
  let U := fun t : ℝ => gaussianNoise (Real.exp (-t)) f
  let L := fun (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) =>
    (∑ i, fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single i 1)) -
      fderiv ℝ g x x
  let D := fun t : ℝ => ∫ z, gaussianBivariateSlope ρ (U t z.1) (U t z.2) * L (U t) z.1 +
    gaussianBivariateSlope ρ (U t z.2) (U t z.1) * L (U t) z.2 ∂correlatedGaussianMeasure ρ
  have hc : ρ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hρ.1],hρ.2⟩
  have hb (x) : |f x| ≤ 1 := by
    rw [abs_of_nonneg (hδ.le.trans (hrange x).1)]
    linarith [(hrange x).2]
  have hi : Integrable f (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    Integrable.of_bound hf.continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  apply gaussianBivariateStability_jensen_clipped_of_time_monotone
    ⟨hc.1.le,hc.2.le⟩ hδ hf.continuous.measurable hrange
  apply monotoneOn_Ioi_of_hasDerivAt_nonneg (F' := D)
  · intro t ht
    exact hasDerivAt_gaussianProfile_exp_neg hc hδ hf hm hk hrange ht
  · intro t ht
    have hr : Real.exp (-t) ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨lt_trans (by norm_num) (Real.exp_pos _), Real.exp_lt_one_iff.mpr (by linarith)⟩
    have hUt : ContDiff ℝ 2 (U t) :=
      (gaussianNoise_smooth hr hi).of_le (WithTop.coe_le_coe.mpr le_top)
    exact (integrable_nonneg_integral_bivariate_generator hρ hδ hUt
      (gaussianNoise_mem_clippedInterval hδ hf.continuous.measurable hrange (Real.exp (-t)))
      (norm_fderiv_gaussianNoise_commutation_le (hf.of_le (by norm_num)) hb hm _)
      (norm_fderiv_fderiv_gaussianNoise_commutation_le hf hb hm hk _)).2


/-- For every measurable unit-interval-valued function and positive
correlation, the expected bivariate Gaussian profile of its two correlated
values is at most the profile at its two equal Gaussian means.
[MN15, §2, Gaussian Jensen inequality, equal-input specialization]

**Proof sketch.** The smooth clipped case follows by Ornstein–Uhlenbeck
interpolation. Gaussian regularization extends it to measurable clipped
functions using L1 convergence and uniform bounds on the derivatives of
Gaussian smoothing. Finally affine clipping approaches any measurable
unit-interval function in L1, and the profile functional is L1 continuous. -/
theorem gaussianBivariateStability_jensen {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
      ∂correlatedGaussianMeasure ρ) ≤
    gaussianBivariateStability ρ
      (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) := by
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  apply gaussianBivariateStability_jensen_of_clipped hc _ f hf hrange
  intro δ hδ g hg hgrange
  apply gaussianBivariateStability_jensen_clipped_of_smooth hc hδ _ g hg hgrange
  intro u hu hM hK hurange
  obtain ⟨M, hM⟩ := hM
  obtain ⟨K, hK⟩ := hK
  exact gaussianBivariateStability_jensen_smooth_clipped hρ hδ hu hM hK hurange

end BooleanAnalysis.GaussianSpace
