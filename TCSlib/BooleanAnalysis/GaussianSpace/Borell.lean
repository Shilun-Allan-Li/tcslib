/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import TCSlib.BooleanAnalysis.ThresholdFunctions.Gaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Borell's Gaussian noise-stability inequality: statement layer

## Main definitions

* `gaussianHalfspaceStability`: the endpoint-aware general-volume profile Λρ.

## Main results

General-volume and balanced Borell, its rotation-sensitivity form, and the
connection to the existing zero-threshold quadrant probability. Proofs are placeholders.

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

/-- The stability Λρ(α) of a Gaussian halfspace of volume α. Interior thresholds
use the existing Gaussian quantile; endpoint volumes have stability zero and one.
[OD14, §11.3, General-volume Borell; §11.7, equation (11.39)]
The existing `gaussianQuadrantProbability` covers only the threshold-zero case. -/
noncomputable def gaussianHalfspaceStability (ρ α : ℝ) : ℝ :=
  if α ≤ 0 then 0 else if 1 ≤ α then 1 else
    ((standardGaussianMeasure.prod standardGaussianMeasure)
      {z : ℝ × ℝ | z.1 ≤ standardGaussianQuantile α ∧
        ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ standardGaussianQuantile α}).toReal

/-- At volume one half the general profile is the existing quadrant probability.
[OD14, Cor. 11.20; §11.3] **Proof sketch.** The Gaussian median is zero, so
the two defining threshold events coincide. -/
theorem gaussianHalfspaceStability_half (ρ : ℝ) :
    gaussianHalfspaceStability ρ (1 / 2) = gaussianQuadrantProbability ρ := sorry

/-- The signed indicator of a homogeneous halfspace has the exact Sheppard
stability in every dimension. [OD14, Cor. 11.20]
This transports the existing scalar `sheppard_formula` to the general noise API.

**Proof sketch.** Apply the joint Gaussian projection law to the unit normal,
then evaluate the same-sign probability using the existing scalar formula. -/
theorem gaussianNoiseStability_homogeneous_halfspace {n : ℕ}
    (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoiseStability ρ (fun x => thresholdSign (∑ i, a i * x i)) =
      1 - 2 * Real.arccos ρ / Real.pi := sorry

/-- Halfspaces maximize Gaussian noise stability among measurable unit-interval
functions of fixed mean. [OD14, §11.3, Borell's Isoperimetric Theorem; Bor85]

**Proof sketch.** Apply the Gaussian rearrangement inequality to the correlated
kernel, or integrate the corresponding two-point interpolation inequality.
Approximate measurable bounded functions and pass to their expectations. -/
theorem borell {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    gaussianNoiseStability ρ f ≤
      gaussianHalfspaceStability ρ
        (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) := sorry

/-- An unbiased bounded Gaussian function has stability at most the homogeneous
halfspace value. [OD14, §11.3, volume-one-half Borell]

**Proof sketch.** Affinely rescale the function to `[0,1]`, apply general Borell
at volume one half, and evaluate the profile with the existing Sheppard formula. -/
theorem borell_balanced {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hfrange : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) = 0) :
    gaussianNoiseStability ρ f ≤ 1 - 2 * Real.arccos ρ / Real.pi := sorry

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
      rotationSensitivity A θ := sorry

/-- Every balanced Gaussian set has rotation sensitivity at least `θ/π` for
all angles between zero and `π/2`. [OD14, §11.3, balanced Borell reformulation]
This extends the already-proved grid-angle Corollary 11.44 to all such angles.

**Proof sketch.** Specialize the general-volume rotation bound at volume one
half, then evaluate the profile using Sheppard's formula. -/
theorem rotationSensitivity_balanced {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A)
    (hvolume : ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal = 1 / 2)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    θ / Real.pi ≤ rotationSensitivity A θ := sorry

end BooleanAnalysis.GaussianSpace
