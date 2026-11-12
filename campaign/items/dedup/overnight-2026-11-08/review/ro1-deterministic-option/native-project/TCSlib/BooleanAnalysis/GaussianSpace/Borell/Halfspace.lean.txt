/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Halfspace
import TCSlib.BooleanAnalysis.ThresholdFunctions.Gaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian projection laws and homogeneous halfspaces

## Main definitions

The standard Gaussian distribution and the existing threshold sign are reused.

## Main results

* `standardGaussianCDF_zero`: zero is the standard Gaussian median.
* `correlatedGaussianMeasure_projection`: projection preserves the scalar correlated law.
* `gaussianNoiseStability_homogeneous_halfspace`: exact signed halfspace stability.

The unit projection law is reused from `GaussianSpace.Halfspace`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Fact 11.7, Definition 11.18, Corollary 11.20.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

local instance : NoAtoms standardGaussianMeasure :=
  noAtoms_gaussianReal (by norm_num)

/-- The standard Gaussian median is zero, as follows from the perfectly
correlated case of Sheppard's formula. [OD14, Cor. 11.20, correlation one] -/
lemma standardGaussianCDF_zero : standardGaussianCDF 0 = 1 / 2 := by
  have h := sheppard_formula (ρ := 1) (by norm_num)
  norm_num [gaussianQuadrantProbability] at h
  have hs : {z : ℝ × ℝ | z.1 ≤ 0} = Set.Iic 0 ×ˢ Set.univ := by
    ext z
    simp
  rw [hs, Measure.prod_prod] at h
  simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, measureReal_def] using h

/-- For two standard Gaussian marginals, the signed-product mean is four times
the lower quadrant probability minus one. [OD14, Cor. 11.20, signed reformulation]

**Proof sketch.** Each marginal has lower-half-line probability one half and
zero probability at the origin. Away from those null boundaries, expand the
product of signs as four times joint lower membership minus twice each marginal
membership plus one. Integrating the four indicators gives the formula. -/
private lemma integral_thresholdSign_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MeasurePreserving X μ standardGaussianMeasure)
    (hY : MeasurePreserving Y μ standardGaussianMeasure) :
    (∫ z, thresholdSign (X z) * thresholdSign (Y z) ∂μ) =
      4 * μ.real {z | X z ≤ 0 ∧ Y z ≤ 0} - 1 := by
  let A := {z | X z ≤ 0}
  let B := {z | Y z ≤ 0}
  have hmA : MeasurableSet A := measurableSet_le hX.measurable measurable_const
  have hmB : MeasurableSet B := measurableSet_le hY.measurable measurable_const
  have hA : μ.real A = 1 / 2 := by
    change (μ (X ⁻¹' Set.Iic 0)).toReal = _
    rw [← Measure.map_apply hX.measurable measurableSet_Iic, hX.map_eq]
    simpa [standardGaussianCDF, cdf_eq_real, measureReal_def] using standardGaussianCDF_zero
  have hB : μ.real B = 1 / 2 := by
    change (μ (Y ⁻¹' Set.Iic 0)).toReal = _
    rw [← Measure.map_apply hY.measurable measurableSet_Iic, hY.map_eq]
    simpa [standardGaussianCDF, cdf_eq_real, measureReal_def] using standardGaussianCDF_zero
  have hX0 : ∀ᵐ z ∂μ, X z ≠ 0 :=
    hX.quasiMeasurePreserving.ae
      (show ∀ᵐ t ∂standardGaussianMeasure, t ≠ (0 : ℝ) from by simp [ae_iff])
  have hY0 : ∀ᵐ z ∂μ, Y z ≠ 0 :=
    hY.quasiMeasurePreserving.ae
      (show ∀ᵐ t ∂standardGaussianMeasure, t ≠ (0 : ℝ) from by simp [ae_iff])
  have heq : (fun z => thresholdSign (X z) * thresholdSign (Y z)) =ᵐ[μ]
      (fun z => 4 * (A ∩ B).indicator (fun _ => (1 : ℝ)) z -
        2 * A.indicator (fun _ => (1 : ℝ)) z -
        2 * B.indicator (fun _ => (1 : ℝ)) z + 1) := by
    filter_upwards [hX0, hY0] with z hx hy
    by_cases hx' : X z ≤ 0 <;> by_cases hy' : Y z ≤ 0 <;>
      norm_num [thresholdSign, A, B, Set.indicator, hx', hy',
        show (0 ≤ X z) ↔ ¬ X z ≤ 0 by
          constructor
          · exact fun h hc => hx (le_antisymm hc h)
          · exact fun h => (lt_of_not_ge h).le,
        show (0 ≤ Y z) ↔ ¬ Y z ≤ 0 by
          constructor
          · exact fun h hc => hy (le_antisymm hc h)
          · exact fun h => (lt_of_not_ge h).le]
  rw [integral_congr_ae heq]
  have hiA := (integrable_const (μ := μ) (1 : ℝ)).indicator hmA
  have hiB := (integrable_const (μ := μ) (1 : ℝ)).indicator hmB
  have hiAB := (integrable_const (μ := μ) (1 : ℝ)).indicator (hmA.inter hmB)
  have hsub : Integrable (fun z => 4 * (A ∩ B).indicator (fun _ => (1 : ℝ)) z -
      2 * A.indicator (fun _ => (1 : ℝ)) z) μ :=
    (hiAB.const_mul 4).sub (hiA.const_mul 2)
  have hsub' : Integrable (fun z => 4 * (A ∩ B).indicator (fun _ => (1 : ℝ)) z -
      2 * A.indicator (fun _ => (1 : ℝ)) z -
      2 * B.indicator (fun _ => (1 : ℝ)) z) μ :=
    hsub.sub (hiB.const_mul 2)
  rw [integral_add hsub' (integrable_const (μ := μ) 1),
    integral_sub hsub (hiB.const_mul 2),
    integral_sub (hiAB.const_mul 4) (hiA.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul]
  simp only [integral_indicator_const (1 : ℝ) (hmA.inter hmB),
    integral_indicator_const (1 : ℝ) hmA, integral_indicator_const (1 : ℝ) hmB,
    smul_eq_mul, mul_one, integral_const, measureReal_univ_eq_one, hA, hB]
  change 4 * μ.real (A ∩ B) - 2 * (1 / 2) - 2 * (1 / 2) + 1 =
    4 * μ.real (A ∩ B) - 1
  ring

/-- Projecting both endpoints along the same unit vector gives the scalar
correlated Gaussian pair. [OD14, Fact 11.7; Cor. 11.20]

**Proof sketch.** Apply the independent product of the two Gaussian projection
maps to the defining coupling. Linearity of projection commutes with its
correlated second endpoint. -/
lemma correlatedGaussianMeasure_projection {n : ℕ}
    (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) (ρ : ℝ) :
    (correlatedGaussianMeasure (n := n) ρ).map
        (fun z => (∑ i, a i * z.1 i, ∑ i, a i * z.2 i)) =
      (standardGaussianMeasure.prod standardGaussianMeasure).map
        (fun z => (z.1, ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)) := by
  have hP := (measurePreserving_gaussianProjection a ha).prod
    (measurePreserving_gaussianProjection a ha)
  unfold correlatedGaussianMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← hP.map_eq, Measure.map_map (by fun_prop) hP.measurable]
  congr 1
  ext z
  · rfl
  · dsimp only [Function.comp_apply, Prod.map]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The signed indicator of a homogeneous halfspace has the exact Sheppard
stability in every dimension. [OD14, Cor. 11.20]
This transports the existing scalar `sheppard_formula` to the general noise API.

**Proof sketch.** Apply the joint Gaussian projection law to the unit normal,
then evaluate the same-sign probability using the existing scalar formula. -/
theorem gaussianNoiseStability_homogeneous_halfspace {n : ℕ}
    (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoiseStability ρ (fun x => thresholdSign (∑ i, a i * x i)) =
      1 - 2 * Real.arccos ρ / Real.pi := by
  let μ := correlatedGaussianMeasure (n := n) ρ
  let L := fun x : Fin n → ℝ => ∑ i, a i * x i
  let f := fun x : Fin n → ℝ => thresholdSign (L x)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold correlatedGaussianMeasure
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hL := measurePreserving_gaussianProjection a ha
  have hX : MeasurePreserving (fun z => L z.1) μ standardGaussianMeasure :=
    hL.comp ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩
  have hY : MeasurePreserving (fun z => L z.2) μ standardGaussianMeasure :=
    hL.comp ⟨measurable_snd, correlatedGaussianMeasure_snd hρ⟩
  have hquad : μ.real {z | L z.1 ≤ 0 ∧ L z.2 ≤ 0} =
      gaussianQuadrantProbability ρ := by
    have h := congrArg (fun ν : Measure (ℝ × ℝ) =>
      ν (Set.Iic 0 ×ˢ Set.Iic 0)) (correlatedGaussianMeasure_projection a ha ρ)
    dsimp only at h
    rw [Measure.map_apply (by fun_prop) (measurableSet_Iic.prod measurableSet_Iic),
      Measure.map_apply (by fun_prop) (measurableSet_Iic.prod measurableSet_Iic)] at h
    exact congrArg ENNReal.toReal h
  have hf : Measurable f := by
    exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
      measurable_const measurable_const
  have hmem : MemLp f 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    MemLp.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        dsimp [f, thresholdSign]
        split <;> norm_num)
  calc
    _ = ∫ z, f z.1 * f z.2 ∂μ :=
      (integral_correlatedGaussianMeasure hρ hmem hmem).symm
    _ = 4 * gaussianQuadrantProbability ρ - 1 := by
      rw [integral_thresholdSign_mul μ (fun z => L z.1) (fun z => L z.2) hX hY, hquad]
    _ = _ := by rw [sheppard_formula hρ]; field_simp; ring

end BooleanAnalysis.GaussianSpace
