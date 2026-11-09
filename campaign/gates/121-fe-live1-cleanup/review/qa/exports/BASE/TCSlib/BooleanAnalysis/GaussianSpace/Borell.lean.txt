/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Affine
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Bivariate
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Definitions
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Integration
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Interpolation
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Indicator
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Halfspace
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileCalculus
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import TCSlib.BooleanAnalysis.ThresholdFunctions.Gaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Borell's Gaussian noise-stability inequality and halfspace formulas

## Contents

* `Borell.Affine`: affine changes of Gaussian stability and expectation.
* `Borell.Bivariate`: the two-volume profile and its scalar Gaussian law.
* `Borell.Definitions`: diagonal and two-volume Gaussian halfspace profiles.
* `Borell.Integration`: Gaussian integration by parts under integrability hypotheses.
* `Borell.Interpolation`: comparison with the bivariate profile functional.
* `Borell.Indicator`: joint membership and rotation disagreement identities.
* `Borell.Halfspace`: Gaussian projections and exact homogeneous halfspace stability.
* `Borell.ProfileCalculus`: derivatives of the two-volume Gaussian profile.

## Main definitions

* `gaussianHalfspaceStability`: the endpoint-aware general-volume profile Λρ.

## Main results

Exact homogeneous halfspace stability, the half-volume profile identity, and
the balanced and rotation-sensitivity reductions to general-volume Borell.
The general-volume `borell` inequality remains the central proof obligation;
its three corollaries depend on that obligation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3, Borell's Isoperimetric Theorem.
* [Bor85] C. Borell, Geometric bounds on the Ornstein–Uhlenbeck velocity process,
  Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete 70 (1985), 1–13.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))

/-- At correlation zero, halfspace stability is the square of its volume.
[OD14, §11.1, independence at correlation zero]

**Proof sketch.** The two threshold events are independent and each has the
prescribed volume by the Gaussian quantile identity. The endpoint volumes
follow directly from the definition. -/
lemma gaussianHalfspaceStability_zero {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    gaussianHalfspaceStability 0 α = α ^ 2 := by
  by_cases h0 : α ≤ 0
  · have : α = 0 := le_antisymm h0 hα.1
    simp [this, gaussianHalfspaceStability]
  by_cases h1 : 1 ≤ α
  · have : α = 1 := le_antisymm hα.2 h1
    simp [this, gaussianHalfspaceStability]
  rw [gaussianHalfspaceStability, if_neg h0, if_neg h1]
  simp only [zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one, one_mul,
    zero_add]
  change (standardGaussianMeasure.prod standardGaussianMeasure).real
    (Set.Iic (standardGaussianQuantile α) ×ˢ Set.Iic (standardGaussianQuantile α)) = _
  rw [measureReal_prod_prod]
  rw [← ProbabilityTheory.cdf_eq_real, ← standardGaussianCDF,
    standardGaussianCDF_quantile (lt_of_not_ge h0) (lt_of_not_ge h1)]
  ring

/-- At correlation one, halfspace stability is its volume.
[OD14, §11.1, identical endpoints at correlation one]

**Proof sketch.** The second endpoint equals the first, so joint membership
is one threshold event. Its volume is the quantile's cumulative probability.
Handle endpoint volumes directly. -/
lemma gaussianHalfspaceStability_one {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    gaussianHalfspaceStability 1 α = α := by
  by_cases h0 : α ≤ 0
  · have : α = 0 := le_antisymm h0 hα.1
    simp [this, gaussianHalfspaceStability]
  by_cases h1 : 1 ≤ α
  · have : α = 1 := le_antisymm hα.2 h1
    simp [this, gaussianHalfspaceStability]
  rw [gaussianHalfspaceStability, if_neg h0, if_neg h1]
  simp only [one_pow, sub_self, Real.sqrt_zero, zero_mul, one_mul, add_zero, and_self]
  rw [show {z : ℝ × ℝ | z.1 ≤ standardGaussianQuantile α} =
    Set.Iic (standardGaussianQuantile α) ×ˢ Set.univ from Set.ext (fun z => by simp)]
  change (standardGaussianMeasure.prod standardGaussianMeasure).real
    (Set.Iic (standardGaussianQuantile α) ×ˢ Set.univ) = _
  rw [measureReal_prod_prod, measureReal_univ_eq_one, mul_one,
    ← ProbabilityTheory.cdf_eq_real, ← standardGaussianCDF]
  exact standardGaussianCDF_quantile (lt_of_not_ge h0) (lt_of_not_ge h1)

/-- At volume one half the general profile is the existing quadrant probability.
[OD14, Cor. 11.20; §11.3] **Proof sketch.** The Gaussian median is zero, so
the two defining threshold events coincide. -/
theorem gaussianHalfspaceStability_half (ρ : ℝ) :
    gaussianHalfspaceStability ρ (1 / 2) = gaussianQuadrantProbability ρ := by
  rw [gaussianHalfspaceStability, if_neg (by norm_num), if_neg (by norm_num),
    standardGaussianQuantile_eq standardGaussianCDF_zero]
  rfl

/-- Halfspaces maximize Gaussian noise stability among measurable unit-interval
functions of fixed mean. [OD14, §11.3, Borell's Isoperimetric Theorem; Bor85]

**Proof sketch.** Bound the ordinary stability by the bivariate Gaussian profile
functional, using its pointwise domination of the product. The remaining Gaussian
Jensen inequality follows by Ornstein–Uhlenbeck interpolation: its derivative is
an expected nonnegative square. Smooth and clip bounded measurable functions,
then use the profile's uniform Lipschitz bound to pass to the endpoint limits. -/
theorem borell {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    gaussianNoiseStability ρ f ≤
      gaussianHalfspaceStability ρ
        (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) := by
  refine (gaussianNoiseStability_le_bivariate_integral ρ hρ f hf hfrange).trans ?_
  rw [← gaussianBivariateStability_diag]
  sorry

/-- An unbiased bounded Gaussian function has stability at most the homogeneous
halfspace value. [OD14, §11.3, volume-one-half Borell]

**Proof sketch.** Affinely rescale the function to `[0,1]`, apply general Borell
at volume one half, and evaluate the profile with the existing Sheppard formula. -/
theorem borell_balanced {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hfrange : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) = 0) :
    gaussianNoiseStability ρ f ≤ 1 - 2 * Real.arccos ρ / Real.pi := by
  let g := fun x => (1 / 2 : ℝ) * f x + 1 / 2
  have hL2 : MemLp f 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    memLp_of_bounded (Filter.Eventually.of_forall hfrange)
    hf.aestronglyMeasurable (2 : ℝ≥0∞)
  have hgmean : (∫ x, g x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      1 / 2 := by
    rw [show g = (fun x => (1 / 2 : ℝ) * f x + 1 / 2) from rfl,
      integral_add (f := fun x => (1 / 2 : ℝ) * f x) (g := fun _ => (1 / 2 : ℝ))
        ((hL2.integrable (by norm_num)).const_mul _) (integrable_const _)]
    simp [integral_const_mul, hmean]
  have hb := borell ρ hρ g (by dsimp [g]; fun_prop)
    (fun x => by dsimp [g]; constructor <;> linarith [(hfrange x).1, (hfrange x).2])
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  rw [hgmean, gaussianHalfspaceStability_half, sheppard_formula hc] at hb
  dsimp [g] at hb
  rw [gaussianNoiseStability_affine hc hL2, hmean] at hb
  ring_nf at hb ⊢
  linarith

/-- A set's rotation sensitivity is bounded below by the halfspace of the same
volume for all angles corresponding to nonnegative correlations.
[OD14, §11.3, rotation-sensitivity reformulation of Borell]

**Proof sketch.** Write disagreement as twice the volume minus twice the joint
membership probability and apply Borell to the indicator. Handle endpoint
correlations by the deterministic and independent Gaussian laws. -/
theorem rotationSensitivity_borell {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    2 * (((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal -
      gaussianHalfspaceStability (Real.cos θ)
        (((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal)) ≤
      rotationSensitivity A θ := by
  have hvol : ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal ∈
      Set.Icc (0 : ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
  · simp [Real.cos_zero, gaussianHalfspaceStability_one hvol, rotationSensitivity]
  rcases eq_or_lt_of_le hθ.2 with heq | hθ1
  · rw [heq, Real.cos_pi_div_two, gaussianHalfspaceStability_zero hvol,
      rotationSensitivity_pi_div_two hA]
    nlinarith
  have hρ : Real.cos θ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩,
      by simpa using (Real.cos_lt_cos_of_nonneg_of_le_pi
        (by norm_num : (0 : ℝ) ≤ 0) (by linarith [Real.pi_pos] : θ ≤ Real.pi) hθ0)⟩
  have hb := borell (Real.cos θ) hρ (A.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hA) (fun x => by
      by_cases hx : x ∈ A <;> simp [Set.indicator, hx])
  simp only [integral_indicator hA, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ] at hb
  rw [rotationSensitivity_eq_stability hA θ ⟨hθ.1, by linarith [Real.pi_pos]⟩]
  simp only [Measure.real]
  linarith

/-- Every balanced Gaussian set has rotation sensitivity at least `θ/π` for
all angles between zero and `π/2`. [OD14, §11.3, balanced Borell reformulation]
This extends the already-proved grid-angle Corollary 11.44 to all such angles.

**Proof sketch.** Specialize the general-volume rotation bound at volume one
half, then evaluate the profile using Sheppard's formula. -/
theorem rotationSensitivity_balanced {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A)
    (hvolume : ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal = 1 / 2)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    θ / Real.pi ≤ rotationSensitivity A θ := by
  have h := rotationSensitivity_borell hA θ hθ
  rw [hvolume, gaussianHalfspaceStability_half,
    sheppard_formula ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩,
    Real.arccos_cos hθ.1 (by linarith [Real.pi_pos, hθ.2])] at h
  convert h using 1
  field_simp
  ring

end BooleanAnalysis.GaussianSpace
