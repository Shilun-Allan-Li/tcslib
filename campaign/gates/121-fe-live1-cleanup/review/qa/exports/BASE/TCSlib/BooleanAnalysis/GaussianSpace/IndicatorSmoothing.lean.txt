/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Prod
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian indicator averaging

## Main definitions

* averagedGaussianIndicator: conditional averaging under the Gaussian rotation coupling.

## Main results

* integral_abs_averagedGaussianIndicator_sub_indicator: exact discrepancy formula.
* tendsto_integral_abs_averagedGaussianIndicator_sub_indicator: integral approximation.
* integral_averagedGaussianIndicator: mean preservation.
* averagedGaussianIndicator_rotation_variation_le: contraction of rotation variation.

These lemmas establish the measure-theoretic part of the indicator approximation
used for Gaussian isoperimetry. Smoothness and the Gaussian functional Bobkov
inequality are separate obligations.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Definition 11.48 and the Gaussian
  Isoperimetric Inequality.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- Average a set indicator over the second endpoint of the Gaussian rotation
coupling. This is a concrete indicator approximation for the argument in
[OD14, §11.4, Def. 11.48], parametrized by rotation angle.

This specialized indicator adapter uses the existing Gaussian laws and coupling;
it does not introduce a general Ornstein–Uhlenbeck operator. No regularity is
asserted by the definition. -/
noncomputable def averagedGaussianIndicator {n : ℕ}
    (A : Set (Fin n → ℝ)) (θ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ,
    A.indicator (fun _ => (1 : ℝ))
      (fun i => Real.cos θ * x i + Real.sin θ * y i)
    ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- An averaged indicator equals the conditional Gaussian probability of
membership at the rotated endpoint. -/
lemma averagedGaussianIndicator_eq_real_measure {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (θ : ℝ) (x : Fin n → ℝ) :
    averagedGaussianIndicator A θ x =
      (Measure.pi fun _ : Fin n => standardGaussianMeasure).real
        {y | (fun i => Real.cos θ * x i + Real.sin θ * y i) ∈ A} := by
  have hm : MeasurableSet {y : Fin n → ℝ |
      (fun i => Real.cos θ * x i + Real.sin θ * y i) ∈ A} :=
    hA.preimage (by fun_prop)
  rw [averagedGaussianIndicator, ← integral_indicator_one hm]
  congr 1

/-- Two measurable membership predicates have a measurable disagreement event. -/
private lemma measurableSet_indicatorDisagreement {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {A : Set Ξ} (hA : MeasurableSet A)
    {f g : Ω → Ξ} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {z | ¬ (f z ∈ A ↔ g z ∈ A)} := by
  convert (hA.preimage hf).symmDiff (hA.preimage hg) using 1
  ext z
  simp only [Set.mem_symmDiff, Set.mem_preimage, Set.mem_setOf_eq]
  tauto

/-- The integral absolute difference between an averaged Gaussian indicator
and its original indicator equals rotation sensitivity.
[OD14, §11.4, Def. 11.48, indicator approximation argument]

**Proof sketch.** Condition the disagreement probability on the first endpoint.
The original indicator is zero or one. In the first case the absolute difference
is the conditional membership probability; in the second it is the conditional
nonmembership probability. Both cases equal the conditional disagreement
probability. The product-measure formula integrates these conditional values. -/
lemma integral_abs_averagedGaussianIndicator_sub_indicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (θ : ℝ) :
    (∫ x : Fin n → ℝ,
      |averagedGaussianIndicator A θ x - A.indicator (fun _ => (1 : ℝ)) x|
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) = rotationSensitivity A θ := by
  classical
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  let R (x y : Fin n → ℝ) : Fin n → ℝ :=
    fun i => Real.cos θ * x i + Real.sin θ * y i
  let E : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {z | ¬ (z.1 ∈ A ↔ R z.1 z.2 ∈ A)}
  have hE : MeasurableSet E :=
    measurableSet_indicatorDisagreement hA (f := Prod.fst)
      (g := fun z => R z.1 z.2) measurable_fst (by fun_prop)
  unfold rotationSensitivity
  change (∫ x, |averagedGaussianIndicator A θ x - A.indicator (fun _ => 1) x| ∂μ) =
    ((μ.prod μ) E).toReal
  rw [Measure.prod_apply hE,
    ← integral_toReal (measurable_measure_prodMk_left (ν := μ) hE).aemeasurable
      (Eventually.of_forall fun x => measure_lt_top μ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  let S : Set (Fin n → ℝ) := (R x) ⁻¹' A
  have hS : MeasurableSet S := hA.preimage (by fun_prop)
  change |averagedGaussianIndicator A θ x - A.indicator (fun _ => 1) x| =
    μ.real (Prod.mk x ⁻¹' E)
  rw [averagedGaussianIndicator_eq_real_measure hA]
  change |μ.real S - A.indicator (fun _ => 1) x| = _
  by_cases hx : x ∈ A
  · have hsection : Prod.mk x ⁻¹' E = Sᶜ := by
      ext y
      simp [E, S, hx]
    rw [hsection, measureReal_compl hS, measureReal_univ_eq_one,
      Set.indicator_of_mem hx,
      abs_of_nonpos (sub_nonpos.mpr (measureReal_le_one (μ := μ) (s := S)))]
    ring
  · have hsection : Prod.mk x ⁻¹' E = S := by
      ext y
      simp [E, S, hx]
    rw [hsection, Set.indicator_of_notMem hx, sub_zero,
      abs_of_nonneg (measureReal_nonneg)]

/-- Averaged Gaussian indicators take values in the closed unit interval. -/
lemma averagedGaussianIndicator_mem_unitInterval {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (θ : ℝ) (x : Fin n → ℝ) :
    averagedGaussianIndicator A θ x ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  rw [averagedGaussianIndicator_eq_real_measure hA]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Averaged Gaussian indicators converge to their original indicator in
integral absolute difference as the angle tends to zero.
[OD14, §11.4, Def. 11.48, indicator approximation argument] -/
lemma tendsto_integral_abs_averagedGaussianIndicator_sub_indicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Tendsto (fun θ : ℝ => ∫ x : Fin n → ℝ,
      |averagedGaussianIndicator A θ x - A.indicator (fun _ => (1 : ℝ)) x|
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) (𝓝 (0 : ℝ)) (𝓝 0) := by
  simpa only [integral_abs_averagedGaussianIndicator_sub_indicator hA] using
    rotationSensitivity_tendsto_zero hA

/-- Averaging a measurable Gaussian indicator gives a measurable function. -/
lemma measurable_averagedGaussianIndicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (θ : ℝ) :
    Measurable (averagedGaussianIndicator A θ) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  have hm : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      A.indicator (fun _ => (1 : ℝ))
        (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i)) :=
    (measurable_const.indicator hA).comp (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- An averaged measurable Gaussian indicator is integrable under the product
standard Gaussian law. -/
lemma integrable_averagedGaussianIndicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (θ : ℝ) :
    Integrable (averagedGaussianIndicator A θ)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_averagedGaussianIndicator hA θ).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (averagedGaussianIndicator_mem_unitInterval hA θ x).1]
  exact (averagedGaussianIndicator_mem_unitInterval hA θ x).2

/-- Gaussian indicator averaging preserves the Gaussian measure of the set.
[OD14, §11.4, Def. 11.48, indicator approximation argument]

**Proof sketch.** Integrating the conditional membership probabilities gives
the membership probability at the rotated endpoint. Gaussian rotation preserves
the joint law, and its first marginal is the original Gaussian law. -/
lemma integral_averagedGaussianIndicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (θ : ℝ) :
    (∫ x : Fin n → ℝ, averagedGaussianIndicator A θ x
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      (Measure.pi fun _ : Fin n => standardGaussianMeasure).real A := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  let E : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {z | (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ A}
  have hE : MeasurableSet E := hA.preimage (by fun_prop)
  calc
    (∫ x, averagedGaussianIndicator A θ x ∂μ) =
        ∫ x, (μ (Prod.mk x ⁻¹' E)).toReal ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        averagedGaussianIndicator_eq_real_measure hA θ x
    _ = ((μ.prod μ) E).toReal := by
      rw [Measure.prod_apply hE]
      exact integral_toReal
        (measurable_measure_prodMk_left (ν := μ) hE).aemeasurable
        (Eventually.of_forall fun _ => measure_lt_top μ _)
    _ = μ.real A :=
      (measurePreserving_fst.comp
        (measurePreserving_gaussianRotation (n := n) θ)).measureReal_preimage
          hA.nullMeasurableSet


/-- Exchanging the middle coordinates preserves four identical product laws. -/
private lemma measurePreserving_middleTranspose {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] :
    MeasurePreserving (fun z : (E × E) × (E × E) =>
      ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((μ.prod μ).prod (μ.prod μ)) ((μ.prod μ).prod (μ.prod μ)) := by
  have hi := MeasurePreserving.id μ
  have hinner := measurePreserving_prodAssoc μ μ μ
  have houter := measurePreserving_prodAssoc μ μ (μ.prod μ)
  have hinnerInv := MeasurePreserving.symm MeasurableEquiv.prodAssoc hinner
  have houterInv := MeasurePreserving.symm MeasurableEquiv.prodAssoc houter
  exact houterInv.comp ((hi.prod hinner).comp
    ((hi.prod ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).prod hi)).comp
      ((hi.prod hinnerInv).comp houter)))

/-- Independently mixing corresponding coordinates of two Gaussian pairs gives
a pair of independent standard Gaussian vectors.

**Proof sketch.** Regroup the four independent vectors into two pairs. Apply
Gaussian rotation to each pair and retain its first endpoint. -/
private lemma measurePreserving_gaussianPairedEndpoint {n : ℕ} (u : ℝ) :
    MeasurePreserving
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        ((fun i => Real.cos u * z.1.1 i + Real.sin u * z.2.1 i),
         (fun i => Real.cos u * z.1.2 i + Real.sin u * z.2.2 i)))
      (((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
          (Measure.pi fun _ : Fin n => standardGaussianMeasure)).prod
        ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
          (Measure.pi fun _ : Fin n => standardGaussianMeasure)))
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  have hp : MeasurePreserving
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        fun i => Real.cos u * z.1 i + Real.sin u * z.2 i) (μ.prod μ) μ :=
    measurePreserving_fst.comp (measurePreserving_gaussianRotation u)
  exact (hp.prod hp).comp (measurePreserving_middleTranspose μ)

/-- The absolute difference of two finite real set measures is bounded by
the real measure of their symmetric difference. -/
private lemma abs_measureReal_sub_le_symmDiff {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (C D : Set E) :
    |μ.real C - μ.real D| ≤ μ.real (symmDiff C D) := by
  have hCD := measureReal_symmDiff_le (μ := μ) (s := C) (t := D) (∅ : Set E)
  have hDC := measureReal_symmDiff_le (μ := μ) (s := D) (t := C) (∅ : Set E)
  rw [symmDiff_comm D C] at hDC
  simp only [← Set.bot_eq_empty, symmDiff_bot] at hCD hDC
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The difference of two averaged indicators is bounded by the disagreement
probability under a coupled pair of averaging noises.

**Proof sketch.** Lift the first conditional membership probability by the first
noise projection, and the second by its rotated endpoint. Their difference is
bounded by the measure of the symmetric difference of these two lifted events. -/
private lemma averagedGaussianIndicator_pair_diff_le {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (u v : ℝ) (x x' : Fin n → ℝ) :
    |averagedGaussianIndicator A u x - averagedGaussianIndicator A u
        (fun i => Real.cos v * x i + Real.sin v * x' i)| ≤
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)).real
        {q | ¬ ((fun i => Real.cos u * x i + Real.sin u * q.1 i) ∈ A ↔
          (fun i => Real.cos u * (Real.cos v * x i + Real.sin v * x' i) +
            Real.sin u * (Real.cos v * q.1 i + Real.sin v * q.2 i)) ∈ A)} := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  let R (a : ℝ) (z w : Fin n → ℝ) := fun i => Real.cos a * z i + Real.sin a * w i
  let S (z : Fin n → ℝ) : Set (Fin n → ℝ) := {y | R u z y ∈ A}
  have hS (z) : MeasurableSet (S z) := hA.preimage (by fun_prop)
  let C : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Prod.fst ⁻¹' S x
  let D : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (fun q => R v q.1 q.2) ⁻¹' S (R v x x')
  have hC : (μ.prod μ).real C = μ.real (S x) :=
    measurePreserving_fst.measureReal_preimage (hS x).nullMeasurableSet
  have hp : MeasurePreserving (fun q : (Fin n → ℝ) × (Fin n → ℝ) => R v q.1 q.2)
      (μ.prod μ) μ := measurePreserving_fst.comp (measurePreserving_gaussianRotation v)
  have hD : (μ.prod μ).real D = μ.real (S (R v x x')) :=
    hp.measureReal_preimage (hS (R v x x')).nullMeasurableSet
  rw [averagedGaussianIndicator_eq_real_measure hA, averagedGaussianIndicator_eq_real_measure hA]
  change |μ.real (S x) - μ.real (S (R v x x'))| ≤ _
  rw [← hC, ← hD]
  convert abs_measureReal_sub_le_symmDiff (μ.prod μ) C D using 1
  congr 1
  ext q
  simp only [C, D, S, Set.mem_symmDiff, Set.mem_preimage, Set.mem_setOf_eq]
  tauto

/-- Gaussian indicator averaging cannot increase rotation disagreement in
integral absolute difference. This is the contraction step for the indicator
approximation in [OD14, §11.4, Def. 11.48].

**Proof sketch.** Couple the averaging noises with the same rotation as the
outer endpoints. The preceding conditional-probability bound reduces the
integral to a four-Gaussian disagreement event. Regroup the four vectors and
mix the corresponding pairs by the averaging angle; the resulting endpoints
are independent standard Gaussians. Commutation of the two linear combinations
identifies this event with the original rotation disagreement. -/
lemma averagedGaussianIndicator_rotation_variation_le {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (u v : ℝ) :
    (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
      |averagedGaussianIndicator A u z.1 - averagedGaussianIndicator A u
        (fun i => Real.cos v * z.1 i + Real.sin v * z.2 i)|
      ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))) ≤ rotationSensitivity A v := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  let ν := μ.prod μ
  let R (a : ℝ) (z w : Fin n → ℝ) := fun i => Real.cos a * z i + Real.sin a * w i
  let E : Set (((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))) :=
    {z | ¬ (R u z.1.1 z.2.1 ∈ A ↔ R u (R v z.1.1 z.1.2) (R v z.2.1 z.2.2) ∈ A)}
  have hE : MeasurableSet E :=
    measurableSet_indicatorDisagreement hA
      (f := fun z : ((Fin n → ℝ) × (Fin n → ℝ)) ×
          ((Fin n → ℝ) × (Fin n → ℝ)) => R u z.1.1 z.2.1)
      (g := fun z => R u (R v z.1.1 z.1.2) (R v z.2.1 z.2.2))
      (by fun_prop) (by fun_prop)
  calc
    (∫ p, |averagedGaussianIndicator A u p.1 -
        averagedGaussianIndicator A u (R v p.1 p.2)| ∂ν) ≤
        ∫ p, ν.real (Prod.mk p ⁻¹' E) ∂ν := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        (Measure.integrable_measure_prodMk_left hE (measure_ne_top _ _))
      exact Eventually.of_forall fun p => averagedGaussianIndicator_pair_diff_le hA u v p.1 p.2
    _ = (ν.prod ν).real E := by
      rw [measureReal_def, Measure.prod_apply hE]
      exact integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
        (Eventually.of_forall fun _ => measure_lt_top ν _)
    _ = rotationSensitivity A v := by
      let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {p | ¬ (p.1 ∈ A ↔ R v p.1 p.2 ∈ A)}
      have hF : MeasurableSet F :=
        measurableSet_indicatorDisagreement hA (f := Prod.fst)
          (g := fun p => R v p.1 p.2) measurable_fst (by fun_prop)
      have hpre : E = (fun z => (R u z.1.1 z.2.1, R u z.1.2 z.2.2)) ⁻¹' F := by
        ext z
        have hcomm : R u (R v z.1.1 z.1.2) (R v z.2.1 z.2.2) =
            R v (R u z.1.1 z.2.1) (R u z.1.2 z.2.2) := by
          funext i
          dsimp [R]
          ring
        simp only [E, F, Set.mem_setOf_eq, Set.mem_preimage]
        rw [hcomm]
      change ((ν.prod ν) E).toReal = (ν F).toReal
      rw [hpre]
      exact congrArg ENNReal.toReal
        ((measurePreserving_gaussianPairedEndpoint u).measure_preimage hF.nullMeasurableSet)


end BooleanAnalysis.GaussianSpace
