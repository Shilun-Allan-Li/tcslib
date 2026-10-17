/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Fernique
import TCSlib.BooleanAnalysis.GaussianSpace.Definitions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian rotation sensitivity

## Main definitions

`rotationSensitivity` is in `Definitions`; Gaussian laws are the existing product laws.

## Main results

* `measurePreserving_gaussianRotation`: rotation invariance of the product Gaussian law.
* `rotationSensitivity_subadditive`: subadditivity under addition of angles.
* `rotationSensitivity_sum_le`: the finite-angle form of Theorem 11.43.
* `rotationSensitivity_div_nat`: the equal-step form of Theorem 11.43.
* `rotationSensitivity_pi_div_two`: independent endpoints disagree with probability
  `2α(1-α)`.
* `rotationSensitivity_balanced_grid`: Corollary 11.44 at angles `π/(2ℓ)`.

The rotation-law bridge specializes Mathlib's Gaussian rotation invariance to the
existing product laws. No general Borell or Sheppard theorem is restated; their
existing local and external locations are recorded in `COVERAGE.md`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3, Theorem 11.43 and Corollary 11.44.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ} {A : Set (Fin n → ℝ)}

/-- The rotation `(g, g') ↦ (cos t • g + sin t • g', -sin t • g + cos t • g')`
preserves the joint law of two independent standard Gaussian vectors.
[OD14, Thm. 11.43 (proof)]

**Proof sketch.** Apply centered Gaussian rotation invariance to each pair of
coordinates. Taking the product of these measure-preserving maps, then identifying
a vector of pairs with a pair of vectors, gives the stated product-law invariance. -/
theorem measurePreserving_gaussianRotation (t : ℝ) :
    MeasurePreserving
      (ContinuousLinearMap.rotation t :
        (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ))
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)) :=
  (by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  letI : ProbabilityTheory.IsGaussian standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  have hscalar :
      MeasurePreserving (ContinuousLinearMap.rotation t : ℝ × ℝ →L[ℝ] ℝ × ℝ)
        (standardGaussianMeasure.prod standardGaussianMeasure)
        (standardGaussianMeasure.prod standardGaussianMeasure) := by
    refine ⟨(ContinuousLinearMap.rotation t).continuous.measurable, ?_⟩
    exact ProbabilityTheory.IsGaussian.map_rotation_eq_self
      (by simp [standardGaussianMeasure]) t
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => standardGaussianMeasure) (fun _ => standardGaussianMeasure)
  have hpi := measurePreserving_pi
    (fun _ : Fin n => standardGaussianMeasure.prod standardGaussianMeasure)
    (fun _ : Fin n => standardGaussianMeasure.prod standardGaussianMeasure)
    (fun _ => hscalar)
  exact he.comp (hpi.comp (MeasurePreserving.symm e he))
)

/-- Gaussian rotation sensitivity is subadditive for arbitrary real angles.
[OD14, Thm. 11.43, binary form]

**Proof sketch.** Couple the three points on the random ellipse
`cos θ * g + sin θ * g'`. A disagreement between its endpoints forces a
disagreement on one of the two segments. Rotation invariance identifies the
two segment probabilities, and the union bound finishes the argument. -/
theorem rotationSensitivity_subadditive (hA : MeasurableSet A) (s t : ℝ) :
    rotationSensitivity A (s + t) ≤ rotationSensitivity A s + rotationSensitivity A t :=
  (by
  classical
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ := (Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
    (Measure.pi fun _ : Fin n => standardGaussianMeasure)
  let E : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Prod.fst ⁻¹' A
  let f (u : ℝ) := (ContinuousLinearMap.rotation u :
    (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ))
  have hE : MeasurableSet E := hA.preimage measurable_fst
  have hf (u : ℝ) : Measurable (f u) := (f u).continuous.measurable
  have hrot (z : (Fin n → ℝ) × (Fin n → ℝ)) : f t (f s z) = f (s + t) z := by
    ext i <;>
      simp [f, ContinuousLinearMap.rotation_apply, Real.cos_add, Real.sin_add,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have hsens (u : ℝ) :
      rotationSensitivity A u = μ.real (symmDiff E (f u ⁻¹' E)) := by
    change μ.real {z | ¬ (z.1 ∈ A ↔
      (fun i => Real.cos u * z.1 i + Real.sin u * z.2 i) ∈ A)} = _
    congr 1
    ext z
    change (¬ (z.1 ∈ A ↔
        (fun i => Real.cos u * z.1 i + Real.sin u * z.2 i) ∈ A)) ↔
      ((z.1 ∈ A ∧ (fun i => Real.cos u * z.1 i + Real.sin u * z.2 i) ∉ A) ∨
        ((fun i => Real.cos u * z.1 i + Real.sin u * z.2 i) ∈ A ∧ z.1 ∉ A))
    tauto
  have hpull : symmDiff (f s ⁻¹' E) (f (s + t) ⁻¹' E) =
      f s ⁻¹' symmDiff E (f t ⁻¹' E) := by
    ext z
    simp only [Set.mem_symmDiff, Set.mem_preimage]
    rw [hrot]
  rw [hsens (s + t), hsens s, hsens t]
  calc
    μ.real (symmDiff E (f (s + t) ⁻¹' E)) ≤
        μ.real (symmDiff E (f s ⁻¹' E)) +
          μ.real (symmDiff (f s ⁻¹' E) (f (s + t) ⁻¹' E)) :=
      measureReal_symmDiff_le _
    _ = μ.real (symmDiff E (f s ⁻¹' E)) +
        μ.real (symmDiff E (f t ⁻¹' E)) := by
      rw [hpull, (measurePreserving_gaussianRotation s).measureReal_preimage
        (hE.symmDiff (hE.preimage (hf t))).nullMeasurableSet]
)

/-- For finitely many real angles, rotation sensitivity at their sum is at most
the sum of their rotation sensitivities. [OD14, Thm. 11.43]

**Proof sketch.** Follow the partial sums of the angles on the same random ellipse.
If the endpoints disagree, some consecutive pair disagrees; apply the finite union
bound and identify each pair's joint Gaussian distribution. -/
theorem rotationSensitivity_sum_le (hA : MeasurableSet A) {ℓ : ℕ} (δ : Fin ℓ → ℝ) :
    rotationSensitivity A (∑ j, δ j) ≤ ∑ j, rotationSensitivity A (δ j) :=
  (by
  exact Finset.le_sum_of_subadditive (rotationSensitivity A)
    (by simp [rotationSensitivity]) (rotationSensitivity_subadditive hA)
    Finset.univ δ
)

/-- Dividing an angle into `ℓ > 0` equal steps bounds its rotation sensitivity by
`ℓ` times the sensitivity of one step. [OD14, Thm. 11.43, final assertion]

**Proof sketch.** Apply the finite-angle inequality to the constant sequence
whose value is `δ/ℓ`; its sum is `δ`. -/
theorem rotationSensitivity_div_nat (hA : MeasurableSet A) (δ : ℝ)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    rotationSensitivity A δ ≤ (ℓ : ℝ) * rotationSensitivity A (δ / ℓ) :=
  (by
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hℓ
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel₀ δ hℓ'] using
    rotationSensitivity_sum_le hA (fun _ : Fin ℓ => δ / ℓ)
)

/-- Independent Gaussian endpoints disagree on a set of volume `α` with probability
`2α(1-α)`; these endpoints correspond to angle `π/2`.
[OD14, Cor. 11.44 (proof); Thm. 11.52 (proof)]

**Proof sketch.** At angle `π/2` the endpoints are the two independent Gaussian
vectors. Split the disagreement event into the two disjoint choices of which
endpoint belongs to the set, and multiply the independent probabilities. -/
lemma rotationSensitivity_pi_div_two (hA : MeasurableSet A) :
    rotationSensitivity A (Real.pi / 2) =
      2 * ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal *
        (1 - ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal) :=
  (by
  classical
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  simp only [rotationSensitivity, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_mul, one_mul, zero_add]
  change (μ.prod μ).real {z | ¬ (z.1 ∈ A ↔ z.2 ∈ A)} =
    2 * μ.real A * (1 - μ.real A)
  have hsplit : {z : (Fin n → ℝ) × (Fin n → ℝ) | ¬ (z.1 ∈ A ↔ z.2 ∈ A)} =
      (A ×ˢ Aᶜ) ∪ (Aᶜ ×ˢ A) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, Set.mem_compl_iff]
    tauto
  rw [hsplit, measureReal_union
    (Set.disjoint_prod.mpr (Or.inl disjoint_compl_right)) (hA.compl.prod hA),
    measureReal_prod_prod, measureReal_prod_prod, measureReal_compl hA,
    measureReal_univ_eq_one]
  ring
)

/-- A measurable set of Gaussian volume one half has rotation sensitivity at least
`1/(2ℓ)` at angle `π/(2ℓ)`, for every positive integer `ℓ`.
[OD14, Cor. 11.44]

**Proof sketch.** Its sensitivity at `π/2` is one half by independence. The
equal-step inequality bounds that value above by `ℓ` times the sensitivity at
`π/(2ℓ)`; divide by the positive integer `ℓ`. -/
theorem rotationSensitivity_balanced_grid (hA : MeasurableSet A)
    (hvol : (Measure.pi fun _ : Fin n => standardGaussianMeasure) A = 1 / 2)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    1 / (2 * (ℓ : ℝ)) ≤ rotationSensitivity A (Real.pi / (2 * ℓ)) :=
  (by
  have h := rotationSensitivity_div_nat hA (Real.pi / 2) ℓ hℓ
  rw [rotationSensitivity_pi_div_two hA, hvol, div_div] at h
  norm_num at h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (ℓ : ℝ))).mpr
  nlinarith [h]
)

end BooleanAnalysis.GaussianSpace
