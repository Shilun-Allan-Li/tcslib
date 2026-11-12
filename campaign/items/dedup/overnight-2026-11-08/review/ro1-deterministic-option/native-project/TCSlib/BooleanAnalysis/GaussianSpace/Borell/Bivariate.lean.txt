/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Definitions
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bivariate Gaussian probability profile

## Main definitions

The endpoint-aware profile `gaussianBivariateStability` is reused from
`Borell.Definitions`.

## Main results

The two-volume profile agrees with Gaussian quantile thresholds in the interior
and with `gaussianHalfspaceStability` on the diagonal. Its Gaussian marginal
laws give symmetry, endpoint values, and a uniform Lipschitz bound on the
closed probability square. Conditional integration gives its scalar cdf formula.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3 and §11.7, equation (11.39).
* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §§1.2–2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- A standard Gaussian cdf comparison has probability equal to its unit-interval
threshold. [OD14, Def. 5.26, probability integral transform]

**Proof sketch.** The endpoint events are empty and universal. In the interior,
the comparison is a lower half-line at the inverse cdf, whose probability is
the original threshold. -/
lemma measureReal_standardGaussianCDF_le (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    standardGaussianMeasure.real {t : ℝ | standardGaussianCDF t ≤ a} = a := by
  rcases eq_or_lt_of_le ha.1 with h0 | h0
  · subst a
    have hs : {t : ℝ | standardGaussianCDF t ≤ 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr
        (fun t ht => (not_le_of_gt (standardGaussianCDF_pos t)) ht)
    simp [hs]
  rcases eq_or_lt_of_le ha.2 with h1 | h1
  · subst a
    have hs : {t : ℝ | standardGaussianCDF t ≤ 1} = Set.univ :=
      Set.eq_univ_of_forall (fun t => (standardGaussianCDF_lt_one t).le)
    simp [hs]
  have hs : {t : ℝ | standardGaussianCDF t ≤ a} =
      Set.Iic (standardGaussianQuantile a) := by
    ext t
    change standardGaussianCDF t ≤ a ↔ t ≤ standardGaussianQuantile a
    calc
      _ ↔ standardGaussianCDF t ≤
          standardGaussianCDF (standardGaussianQuantile a) := by
        rw [standardGaussianCDF_quantile h0 h1]
      _ ↔ _ := standardGaussianCDF_strictMono.le_iff_le
  rw [hs, ← cdf_eq_real, ← standardGaussianCDF]
  exact standardGaussianCDF_quantile h0 h1

/-- The cdf of any standard Gaussian random variable has uniform lower-event
probabilities on the unit interval. [OD14, Def. 5.26, probability integral transform] -/
lemma measureReal_standardGaussianCDF_comp_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ}
    (hX : MeasurePreserving X μ standardGaussianMeasure)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    μ.real {ω | standardGaussianCDF (X ω) ≤ a} = a := by
  calc
    _ = standardGaussianMeasure.real {t : ℝ | standardGaussianCDF t ≤ a} :=
      hX.measureReal_preimage
        ((measurableSet_le continuous_standardGaussianCDF.measurable
          measurable_const).nullMeasurableSet)
    _ = a := measureReal_standardGaussianCDF_le a ha

/-- Increasing a Gaussian cdf threshold changes an intersection probability
by at most the width of the added probability strip.

**Proof sketch.** The gain in an intersection lies inside the strip between
the thresholds. That strip's probability is the difference of the two uniform
cdf-event probabilities. -/
private lemma measureReal_standardGaussianCDF_inter_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MeasurePreserving X μ standardGaussianMeasure)
    (A : Set Ω) (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    μ.real ({ω | standardGaussianCDF (X ω) ≤ b} ∩ A) -
      μ.real ({ω | standardGaussianCDF (X ω) ≤ a} ∩ A) ≤ b - a := by
  have hsub : {ω | standardGaussianCDF (X ω) ≤ a} ⊆
      {ω | standardGaussianCDF (X ω) ≤ b} := fun _ hω => hω.trans hab
  calc
    _ ≤ μ.real (({ω | standardGaussianCDF (X ω) ≤ b} ∩ A) \
        ({ω | standardGaussianCDF (X ω) ≤ a} ∩ A)) := le_measureReal_diff
    _ ≤ μ.real ({ω | standardGaussianCDF (X ω) ≤ b} \
        {ω | standardGaussianCDF (X ω) ≤ a}) :=
      measureReal_mono (by
        intro ω hω
        exact ⟨hω.1.1, fun h => hω.2 ⟨h, hω.1.2⟩⟩)
    _ = b - a := by
      rw [measureReal_diff hsub
        (measurableSet_le
          (continuous_standardGaussianCDF.measurable.comp hX.measurable)
          measurable_const),
        measureReal_standardGaussianCDF_comp_le hX b hb,
        measureReal_standardGaussianCDF_comp_le hX a ha]

/-- Intersecting with a fixed event preserves the unit Lipschitz bound for
probabilities of standard Gaussian cdf comparisons.
[MN15, §1.2, regularity of the probability profile]

**Proof sketch.** For ordered thresholds, the change is bounded by the
probability of the strip between them, which equals their difference.
Exchange the thresholds for the opposite ordering. -/
lemma abs_measureReal_standardGaussianCDF_inter_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MeasurePreserving X μ standardGaussianMeasure)
    (A : Set Ω) (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |μ.real ({ω | standardGaussianCDF (X ω) ≤ a} ∩ A) -
      μ.real ({ω | standardGaussianCDF (X ω) ≤ b} ∩ A)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this b a hb ha (le_of_not_ge hab)
  have hmono : μ.real ({ω | standardGaussianCDF (X ω) ≤ a} ∩ A) ≤
      μ.real ({ω | standardGaussianCDF (X ω) ≤ b} ∩ A) :=
    measureReal_mono (fun _ hω => ⟨hω.1.trans hab, hω.2⟩)
  rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hab)]
  simpa only [neg_sub] using
    measureReal_standardGaussianCDF_inter_sub_le hX A a b ha hb hab

/-- Rotating an independent pair of standard Gaussians preserves its law.
[OD14, Fact 11.7] -/
lemma measurePreserving_scalarGaussianRotation (θ : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation θ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      (standardGaussianMeasure.prod standardGaussianMeasure)
      (standardGaussianMeasure.prod standardGaussianMeasure) := by
  letI : IsGaussian standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  exact ⟨by fun_prop, IsGaussian.map_rotation_eq_self (by simp [standardGaussianMeasure]) θ⟩

/-- A valid scalar Gaussian endpoint has the standard Gaussian law.
[OD14, Fact 11.7]
**Proof sketch.** It is the first marginal of the Gaussian rotation through
the arccosine of the correlation. -/
lemma measurePreserving_scalarGaussianEndpoint {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    MeasurePreserving
      (fun z : ℝ × ℝ => ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)
      (standardGaussianMeasure.prod standardGaussianMeasure) standardGaussianMeasure := by
  simpa only [Function.comp_def, ContinuousLinearMap.rotation_apply,
    Real.cos_arccos hρ.1 hρ.2, Real.sin_arccos, smul_eq_mul] using
    measurePreserving_fst.comp (measurePreserving_scalarGaussianRotation (Real.arccos ρ))

/-- For interior volumes, the bivariate profile uses their Gaussian quantiles
as the two thresholds. [MN15, §1.2, definition of J]

**Proof sketch.** Strict monotonicity of the cdf and its quantile inverse
identify each cdf comparison with the corresponding threshold event. -/
lemma gaussianBivariateStability_eq_threshold (ρ α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    gaussianBivariateStability ρ α β =
      (standardGaussianMeasure.prod standardGaussianMeasure).real
        {z : ℝ × ℝ | z.1 ≤ standardGaussianQuantile α ∧
          ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ standardGaussianQuantile β} := by
  unfold gaussianBivariateStability
  congr 1
  ext z
  simp only [Set.mem_setOf_eq]
  apply and_congr
  · calc
      _ ↔ standardGaussianCDF z.1 ≤ standardGaussianCDF (standardGaussianQuantile α) := by
        rw [standardGaussianCDF_quantile hα.1 hα.2]
      _ ↔ _ := standardGaussianCDF_strictMono.le_iff_le
  · calc
      _ ↔ standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤
          standardGaussianCDF (standardGaussianQuantile β) := by
        rw [standardGaussianCDF_quantile hβ.1 hβ.2]
      _ ↔ _ := standardGaussianCDF_strictMono.le_iff_le

/-- The diagonal of the two-volume profile is the existing halfspace stability
profile, including its endpoint extension. [OD14, §11.7, equation (11.39); MN15, §1.2]

**Proof sketch.** In the open interval both definitions are the same quantile
event. At nonpositive volume the cdf comparison is impossible, and at volume
at least one both cdf comparisons hold everywhere. -/
lemma gaussianBivariateStability_diag (ρ α : ℝ) :
    gaussianBivariateStability ρ α α = gaussianHalfspaceStability ρ α := by
  by_cases h0 : α ≤ 0
  · rw [gaussianHalfspaceStability, if_pos h0]
    unfold gaussianBivariateStability
    have hset : {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α ∧
        standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ α} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact (not_le_of_gt (lt_of_le_of_lt h0 (standardGaussianCDF_pos z.1))) hz.1
    simp [hset]
  by_cases h1 : 1 ≤ α
  · rw [gaussianHalfspaceStability, if_neg h0, if_pos h1]
    unfold gaussianBivariateStability
    have hset : {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α ∧
        standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ α} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      exact ⟨(standardGaussianCDF_lt_one _).le.trans h1,
        (standardGaussianCDF_lt_one _).le.trans h1⟩
    simp [hset]
  rw [gaussianBivariateStability_eq_threshold ρ α α
    ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩ ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩,
    gaussianHalfspaceStability, if_neg h0, if_neg h1]
  rfl

/-- A two-threshold Gaussian probability is the Gaussian integral of its
conditional one-dimensional cdf. [MN15, §2, conditional form of J]

**Proof sketch.** Integrate the indicator of the joint threshold event by
Fubini. For each fixed first coordinate, solve the second threshold inequality
for the independent second Gaussian; its probability is the displayed cdf. -/
lemma scalarGaussian_joint_threshold_integral (ρ s t : ℝ)
    (h : 0 < Real.sqrt (1 - ρ ^ 2)) :
    (standardGaussianMeasure.prod standardGaussianMeasure).real
        {z : ℝ × ℝ | z.1 ≤ s ∧ ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ t} =
      ∫ x in Set.Iic s, standardGaussianCDF ((t - ρ * x) / Real.sqrt (1 - ρ ^ 2))
        ∂standardGaussianMeasure := by
  let E : Set (ℝ × ℝ) :=
    {z | z.1 ≤ s ∧ ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ t}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le (show Measurable
        (fun z : ℝ × ℝ => ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) by fun_prop)
        measurable_const)
  rw [← integral_indicator_one hE,
    integral_prod (E.indicator (1 : ℝ × ℝ → ℝ))
      ((integrable_const (1 : ℝ)).indicator hE),
    ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ≤ s
  · have heq : (fun y => E.indicator (1 : ℝ × ℝ → ℝ) (x, y)) =
        (Set.Iic ((t - ρ * x) / Real.sqrt (1 - ρ ^ 2))).indicator (1 : ℝ → ℝ) := by
      ext y
      have hy : ρ * x + Real.sqrt (1 - ρ ^ 2) * y ≤ t ↔
          y ≤ (t - ρ * x) / Real.sqrt (1 - ρ ^ 2) := by
        rw [le_div_iff₀ h]
        constructor <;> intro hy <;> nlinarith
      simp [E, Set.indicator, hx, hy]
    rw [heq, integral_indicator_one measurableSet_Iic]
    simp [Set.indicator, hx, standardGaussianCDF, cdf_eq_real]
  · have heq : (fun y => E.indicator (1 : ℝ × ℝ → ℝ) (x, y)) = 0 := by
      ext y
      simp [E, Set.indicator, hx]
    rw [heq]
    simp [Set.indicator, hx]

/-- Changing the first volume changes the bivariate probability by at most
the change in volume. The second volume and correlation may be arbitrary.
[MN15, §1.2, regularity of J] -/
lemma abs_gaussianBivariateStability_sub_left_le (ρ β α α' : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1) :
    |gaussianBivariateStability ρ α β - gaussianBivariateStability ρ α' β| ≤ |α - α'| := by
  exact abs_measureReal_standardGaussianCDF_inter_sub_le measurePreserving_fst
    {z : ℝ × ℝ | standardGaussianCDF
      (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ β} α α' hα hα'

/-- For a valid correlation, changing the second volume changes the bivariate
probability by at most the change in volume. [MN15, §1.2, regularity of J] -/
lemma abs_gaussianBivariateStability_sub_right_le {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (α β β' : ℝ)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1) :
    |gaussianBivariateStability ρ α β - gaussianBivariateStability ρ α β'| ≤ |β - β'| := by
  simpa only [gaussianBivariateStability, Set.setOf_and, Set.inter_comm] using
    abs_measureReal_standardGaussianCDF_inter_sub_le (measurePreserving_scalarGaussianEndpoint hρ)
      {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α} β β' hβ hβ'

/-- The bivariate probability changes by at most the sum of the changes in
its two volumes, uniformly up to the probability endpoints.
[MN15, §1.2, regularity of J]

**Proof sketch.** Change the first volume and then the second volume, using
the two coordinatewise probability-strip bounds and the triangle inequality. -/
lemma abs_gaussianBivariateStability_sub_le {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {α β α' β' : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1) :
    |gaussianBivariateStability ρ α β - gaussianBivariateStability ρ α' β'| ≤
      |α - α'| + |β - β'| := by
  exact (abs_sub_le (gaussianBivariateStability ρ α β)
    (gaussianBivariateStability ρ α' β) (gaussianBivariateStability ρ α' β')).trans
      (add_le_add (abs_gaussianBivariateStability_sub_left_le ρ β α α' hα hα')
        (abs_gaussianBivariateStability_sub_right_le hρ α' β β' hβ hβ'))

/-- The bivariate profile is a unit-interval probability, including for its
clipped extension outside the probability square. [MN15, §1.2, definition of J] -/
lemma gaussianBivariateStability_mem_unitInterval (ρ α β : ℝ) :
    gaussianBivariateStability ρ α β ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- In the open probability square, the bivariate profile is a conditional
Gaussian cdf integrated up to the first volume's quantile. [MN15, §2, Lemma 2.1] -/
lemma gaussianBivariateStability_eq_conditional_integral (ρ α β : ℝ)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    gaussianBivariateStability ρ α β =
      ∫ x in Set.Iic (standardGaussianQuantile α),
        standardGaussianCDF ((standardGaussianQuantile β - ρ * x) /
          Real.sqrt (1 - ρ ^ 2)) ∂standardGaussianMeasure := by
  rw [gaussianBivariateStability_eq_threshold ρ α β hα hβ]
  exact scalarGaussian_joint_threshold_integral ρ _ _
    (Real.sqrt_pos.mpr (by nlinarith [hρ.1, hρ.2]))

/-- The bivariate profile vanishes when its first volume is zero.
[MN15, §1.2, boundary values of J] -/
@[simp] lemma gaussianBivariateStability_zero_left (ρ β : ℝ) :
    gaussianBivariateStability ρ 0 β = 0 := by
  unfold gaussianBivariateStability
  have hs : {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ 0 ∧
      standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ β} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr
      (fun z hz => (not_le_of_gt (standardGaussianCDF_pos z.1)) hz.1)
  simp [hs]

/-- The bivariate profile vanishes when its second volume is zero.
[MN15, §1.2, boundary values of J] -/
@[simp] lemma gaussianBivariateStability_zero_right (ρ α : ℝ) :
    gaussianBivariateStability ρ α 0 = 0 := by
  unfold gaussianBivariateStability
  have hs : {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α ∧
      standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ 0} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr
      (fun z hz => (not_le_of_gt (standardGaussianCDF_pos _)) hz.2)
  simp [hs]

/-- At first volume one, the profile is the second volume for every valid
correlation. [MN15, §1.2, boundary values of J] -/
lemma gaussianBivariateStability_one_left {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    gaussianBivariateStability ρ 1 β = β := by
  unfold gaussianBivariateStability
  have hs : {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ 1 ∧
      standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ β} =
      {z : ℝ × ℝ | standardGaussianCDF
        (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ β} := by
    ext z
    simp only [Set.mem_setOf_eq, and_iff_right_iff_imp]
    exact fun _ => (standardGaussianCDF_lt_one z.1).le
  rw [hs]
  exact measureReal_standardGaussianCDF_comp_le
    (measurePreserving_scalarGaussianEndpoint hρ) β hβ

/-- At second volume one, the profile is the first volume.
[MN15, §1.2, boundary values of J] -/
lemma gaussianBivariateStability_one_right (ρ α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    gaussianBivariateStability ρ α 1 = α := by
  unfold gaussianBivariateStability
  have hs : {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α ∧
      standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ 1} =
      {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ α} := by
    ext z
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    exact fun _ => (standardGaussianCDF_lt_one _).le
  rw [hs]
  exact measureReal_standardGaussianCDF_comp_le measurePreserving_fst α hα

/-- The bivariate profile is uniformly Lipschitz on the closed probability
square, with constant two for its maximum metric. [MN15, §1.2, regularity of J]
The sharper coordinatewise estimate is `abs_gaussianBivariateStability_sub_le`. -/
lemma lipschitzOnWith_gaussianBivariateStability {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    LipschitzOnWith 2 (fun p : ℝ × ℝ => gaussianBivariateStability ρ p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  calc
    _ ≤ |p.1 - q.1| + |p.2 - q.2| :=
      abs_gaussianBivariateStability_sub_le hρ hp.1 hp.2 hq.1 hq.2
    _ ≤ dist p q + dist p q := by
      rw [Prod.dist_eq]
      exact add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = _ := by norm_num; ring

/-- The bivariate profile is continuous on the full closed probability square.
[MN15, §1.2, regularity of J] -/
lemma continuousOn_gaussianBivariateStability {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    ContinuousOn (fun p : ℝ × ℝ => gaussianBivariateStability ρ p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
  (lipschitzOnWith_gaussianBivariateStability hρ).continuousOn

/-- Reflecting an independent standard Gaussian pair across the bisector of
its two correlated endpoints preserves its law.
[OD14, Fact 11.7; MN15, §1.2, symmetry of J]

**Proof sketch.** Rotate by the arccosine of the correlation, then negate the
second output. Both transformations preserve the independent Gaussian law. -/
lemma measurePreserving_scalarGaussianReflection {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    MeasurePreserving
      (fun z : ℝ × ℝ =>
        (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2,
         Real.sqrt (1 - ρ ^ 2) * z.1 - ρ * z.2))
      (standardGaussianMeasure.prod standardGaussianMeasure)
      (standardGaussianMeasure.prod standardGaussianMeasure) := by
  have hn : MeasurePreserving (fun x : ℝ => -x)
      standardGaussianMeasure standardGaussianMeasure :=
    ⟨measurable_neg, by simpa only [standardGaussianMeasure, neg_zero] using
      (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  simpa only [Function.comp_def, Prod.map_apply, id_eq,
    ContinuousLinearMap.rotation_apply,
    Real.cos_arccos hρ.1 hρ.2, Real.sin_arccos, smul_eq_mul,
    neg_add_rev, neg_mul, neg_neg, sub_eq_add_neg, add_comm] using
    ((MeasurePreserving.id standardGaussianMeasure).prod hn).comp
      (measurePreserving_scalarGaussianRotation (Real.arccos ρ))

/-- The bivariate Gaussian profile is symmetric in its two volumes for every
valid correlation. [MN15, §1.2, definition of J]

**Proof sketch.** The Gaussian reflection exchanges the first coordinate and
the correlated endpoint. The squared coefficients sum to one, so pulling
back the event through this reflection exchanges its two threshold clauses. -/
lemma gaussianBivariateStability_symm {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (α β : ℝ) :
    gaussianBivariateStability ρ α β = gaussianBivariateStability ρ β α := by
  let R : ℝ × ℝ → ℝ × ℝ := fun z =>
    (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2,
      Real.sqrt (1 - ρ ^ 2) * z.1 - ρ * z.2)
  have hR := measurePreserving_scalarGaussianReflection hρ
  have hnonneg : 0 ≤ 1 - ρ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ.2) (sub_nonneg.mpr hρ.1)]
  have hend (z : ℝ × ℝ) :
      ρ * (R z).1 + Real.sqrt (1 - ρ ^ 2) * (R z).2 = z.1 := by
    change ρ * (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) +
      Real.sqrt (1 - ρ ^ 2) *
        (Real.sqrt (1 - ρ ^ 2) * z.1 - ρ * z.2) = z.1
    calc
      _ = (ρ ^ 2 + Real.sqrt (1 - ρ ^ 2) ^ 2) * z.1 := by ring
      _ = z.1 := by rw [Real.sq_sqrt hnonneg]; ring
  have hE : MeasurableSet {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ β ∧
      standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ α} :=
    (measurableSet_le (continuous_standardGaussianCDF.measurable.comp measurable_fst)
      measurable_const).inter
      (measurableSet_le (continuous_standardGaussianCDF.measurable.comp (by fun_prop))
        measurable_const)
  unfold gaussianBivariateStability
  calc
    _ = (standardGaussianMeasure.prod standardGaussianMeasure).real
        (R ⁻¹' {z : ℝ × ℝ | standardGaussianCDF z.1 ≤ β ∧
          standardGaussianCDF (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ α}) := by
      congr 1
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hend]
      change _ ↔ standardGaussianCDF
        (ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2) ≤ β ∧ standardGaussianCDF z.1 ≤ α
      exact and_comm
    _ = _ := hR.measureReal_preimage hE.nullMeasurableSet

/-- Composing the bivariate Gaussian profile with two measurable unit-interval
functions gives a measurable function. [MN15, §1.2, regularity of J] -/
lemma measurable_gaussianBivariateStability_comp {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hgunit : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (fun x => gaussianBivariateStability ρ (f x) (g x)) := by
  exact (continuousOn_gaussianBivariateStability hρ).restrict.measurable.comp
    ((hf.prodMk hg).subtype_mk (h := fun x => ⟨hfunit x, hgunit x⟩))

/-- Composing the bivariate Gaussian profile with two measurable unit-interval
functions gives an integrable function on every finite measure space.
[MN15, §1.2, probability interpretation and regularity of J] -/
lemma integrable_gaussianBivariateStability_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hgunit : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun x => gaussianBivariateStability ρ (f x) (g x)) μ := by
  apply Integrable.of_bound
    (measurable_gaussianBivariateStability_comp hρ hf hg hfunit hgunit).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gaussianBivariateStability_mem_unitInterval ρ (f x) (g x)).1]
    exact (gaussianBivariateStability_mem_unitInterval ρ (f x) (g x)).2

end BooleanAnalysis.GaussianSpace
