/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Indicator stability and rotation disagreement

## Main definitions

The correlated Gaussian law, stability, and rotation sensitivity are reused.

## Main results

* `gaussianNoiseStability_indicator_measure`: stability is joint membership probability.
* `rotationSensitivity_eq_stability`: disagreement is twice volume minus joint membership.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.18; §11.3; Definition 11.42.
-/

open MeasureTheory
open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))

/-- The stability of a measurable indicator equals the probability that both
correlated Gaussian endpoints lie in its set. [OD14, Def. 11.18]

**Proof sketch.** Identify the conditional noise integral with the joint
Gaussian integral. The product of two indicators is the indicator of joint
membership, whose integral is its probability. -/
lemma gaussianNoiseStability_indicator_measure {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    gaussianNoiseStability ρ (A.indicator (fun _ => (1 : ℝ))) =
      (correlatedGaussianMeasure ρ).real (A ×ˢ A) := by
  rw [gaussianNoiseStability,
    ← integral_correlatedGaussianMeasure hρ (MemLp.indicator hA (memLp_const (1 : ℝ)))
      (MemLp.indicator hA (memLp_const (1 : ℝ)))]
  convert integral_indicator_one (hA.prod hA) using 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hx : z.1 ∈ A <;> by_cases hy : z.2 ∈ A <;>
    simp [Set.indicator, hx, hy]

/-- Rotation disagreement equals twice the set's Gaussian volume minus twice
its indicator stability, for angles in `[0,π]`.
[OD14, Defs. 11.18 and 11.42, §11.3, rotation reformulation]

**Proof sketch.** Membership disagreement is the symmetric difference of the
two endpoint events. Both have the original Gaussian volume. Their intersection
has the indicator stability, so subtracting it from each marginal gives the
claimed identity. -/
lemma rotationSensitivity_eq_stability {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    rotationSensitivity A θ =
      2 * ((γ).real A -
        gaussianNoiseStability (Real.cos θ) (A.indicator (fun _ => (1 : ℝ)))) := by
  let μ := (γ).prod γ
  let E : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Prod.fst ⁻¹' A
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (fun z => fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ⁻¹' A
  have hE : MeasurableSet E := hA.preimage measurable_fst
  have hF : MeasurableSet F := hA.preimage (by fun_prop)
  have hvolE : μ.real E = (γ).real A :=
    congrArg ENNReal.toReal (measurePreserving_fst.measure_preimage hA.nullMeasurableSet)
  have hvolF : μ.real F = (γ).real A :=
    congrArg ENNReal.toReal ((measurePreserving_gaussianCombination
      (Real.cos θ) (Real.sin θ) (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      (by nlinarith [Real.sin_sq_add_cos_sq θ])).measure_preimage hA.nullMeasurableSet)
  have hstab : gaussianNoiseStability (Real.cos θ) (A.indicator (fun _ => (1 : ℝ))) =
      μ.real (E ∩ F) := by
    rw [gaussianNoiseStability_indicator_measure ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hA]
    unfold correlatedGaussianMeasure
    rw [Measure.real, Measure.map_apply (by fun_prop) (hA.prod hA)]
    rw [← Real.sin_eq_sqrt_one_sub_cos_sq hθ.1 hθ.2]
    rfl
  have hdiff : rotationSensitivity A θ = μ.real (symmDiff E F) := by
    change μ.real {z | ¬ (z.1 ∈ A ↔
      (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ A)} = _
    apply congrArg μ.real
    ext z
    simp only [E, F, Set.mem_symmDiff, Set.mem_preimage, Set.mem_setOf_eq]
    tauto
  rw [hdiff, hstab, measureReal_symmDiff_eq hE hF]
  have hEF := measureReal_diff_add_inter (μ := μ) (s := E) hF
  have hFE := measureReal_diff_add_inter (μ := μ) (s := F) hE
  rw [Set.inter_comm F E] at hFE
  rw [hvolE] at hEF
  rw [hvolF] at hFE
  linarith

end BooleanAnalysis.GaussianSpace
