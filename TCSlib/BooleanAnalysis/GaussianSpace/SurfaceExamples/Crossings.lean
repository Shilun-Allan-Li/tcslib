/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Tauto
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
/-!
# Averaging Gaussian rotation crossings

## Main definitions

Uses the existing Gaussian rotation sensitivity.

## Main results

* `rotationSensitivity_mul_nat_le_of_crossings`: pointwise crossing bounds imply sensitivity bounds.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §11.4, Example 11.50.
* [Kan11] D. Kane, The Gaussian surface area and noise sensitivity of degree-d
  polynomial threshold functions, Computational Complexity 20 (2011), 389–412, §2.
-/

open MeasureTheory
open scoped BigOperators
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
/-- Integrating a pointwise uniform bound on the number of events bounds the
sum of their probabilities by that bound. -/
private lemma sum_measure_le_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ) (C : ℝ) (E : ℕ → Set X) [∀ i, DecidablePred (· ∈ E i)]
    (hE : ∀ i, MeasurableSet (E i))
    (hc : ∀ x, (∑ i ∈ Finset.range N, if x ∈ E i then (1:ℝ) else 0) ≤ C) :
    (∑ i ∈ Finset.range N, μ.real (E i)) ≤ C := by
  classical
  have hi : ∀ i, Integrable ((E i).indicator (fun _ : X => (1:ℝ))) μ :=
    fun i => (integrable_const (1:ℝ)).indicator (hE i)
  calc
    (∑ i ∈ Finset.range N, μ.real (E i)) =
        ∫ x, ∑ i ∈ Finset.range N, (E i).indicator (fun _ : X => (1:ℝ)) x ∂μ := by
      rw [integral_finset_sum _ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_indicator_one (hE i)).symm
    _ ≤ ∫ _ : X, C ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => hi i)) (integrable_const C)
      intro x
      simpa only [Set.indicator_apply] using hc x
    _ = C := by simp

/-- A pointwise bound on the number of sampled rotation crossings bounds the
number of steps times the rotation sensitivity by the same constant.
[OD14, §11.4; Kan11]

**Proof sketch.** Integrate the crossing count. Gaussian rotation invariance
identifies each step's crossing probability with the sensitivity at that angle. -/
theorem rotationSensitivity_mul_nat_le_of_crossings {n : ℕ} (A : Set (Fin n → ℝ))
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (N : ℕ) (δ C : ℝ)
    (hcount : ∀ x y : Fin n → ℝ,
      (∑ i ∈ Finset.range N, if ¬(
        (fun j => Real.cos ((i:ℝ)*δ)*x j + Real.sin ((i:ℝ)*δ)*y j) ∈ A ↔
        (fun j => Real.cos (((i+1:ℕ):ℝ)*δ)*x j +
          Real.sin (((i+1:ℕ):ℝ)*δ)*y j) ∈ A) then (1:ℝ) else 0) ≤ C) :
    (N:ℝ) * rotationSensitivity A δ ≤ C := (by
  classical
    letI : IsProbabilityMeasure standardGaussianMeasure := by
      rw [standardGaussianMeasure_eq]
      infer_instance
    let μ := (Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
      (Measure.pi fun _ : Fin n => standardGaussianMeasure)
    let E : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Prod.fst ⁻¹' A
    let f (t : ℝ) := (ContinuousLinearMap.rotation t :
      (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ))
    let B := symmDiff E (f δ ⁻¹' E)
    let D (i : ℕ) := f ((i:ℝ)*δ) ⁻¹' B
    have hE : MeasurableSet E := hA.preimage measurable_fst
    have hB : MeasurableSet B := hE.symmDiff (hE.preimage (f δ).continuous.measurable)
    have hD (i : ℕ) : MeasurableSet (D i) :=
      hB.preimage (f ((i:ℝ)*δ)).continuous.measurable
    have hstep (i : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
        f δ (f ((i:ℝ)*δ) z) = f (((i+1:ℕ):ℝ)*δ) z := by
      rw [show (((i+1:ℕ):ℝ)*δ) = (i:ℝ)*δ+δ by push_cast; ring]
      exact gaussianRotation_comp _ _ _
    have hsens : μ.real B = rotationSensitivity A δ := by
      rw [rotationSensitivity_eq]
      change μ.real B = μ.real {z | ¬ (z.1 ∈ A ↔
        (fun i => Real.cos δ * z.1 i + Real.sin δ * z.2 i) ∈ A)}
      congr 1
      ext z
      change ((z.1 ∈ A ∧
        (fun i => Real.cos δ * z.1 i + Real.sin δ * z.2 i) ∉ A) ∨
        ((fun i => Real.cos δ * z.1 i + Real.sin δ * z.2 i) ∈ A ∧ z.1 ∉ A)) ↔
        ¬(z.1 ∈ A ↔ (fun i => Real.cos δ * z.1 i + Real.sin δ * z.2 i) ∈ A)
      tauto
    have hprob (i : ℕ) : μ.real (D i) = rotationSensitivity A δ := by
      rw [(measurePreserving_gaussianRotation ((i:ℝ)*δ)).measureReal_preimage
        hB.nullMeasurableSet]
      exact hsens
    have hc (z : (Fin n → ℝ) × (Fin n → ℝ)) :
        (∑ i ∈ Finset.range N, if z ∈ D i then (1:ℝ) else 0) ≤ C := by
      let P (i : ℕ) := (f ((i:ℝ)*δ) z).1 ∈ A
      have heq (i : ℕ) : (z ∈ D i) ↔ ¬(P i ↔ P (i+1)) := by
        change (((f ((i:ℝ)*δ) z).1 ∈ A ∧
          (f δ (f ((i:ℝ)*δ) z)).1 ∉ A) ∨
          ((f δ (f ((i:ℝ)*δ) z)).1 ∈ A ∧ (f ((i:ℝ)*δ) z).1 ∉ A)) ↔ _
        rw [hstep]
        change ((P i ∧ ¬P (i+1)) ∨ (P (i+1) ∧ ¬P i)) ↔ _
        tauto
      simp_rw [heq]
      exact hcount z.1 z.2
    have hh := sum_measure_le_const μ N C D hD hc
    simpa only [hprob, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
)


end BooleanAnalysis.GaussianSpace
