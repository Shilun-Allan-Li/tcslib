/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Definitions
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Calculus of the Gaussian isoperimetric profile

## Main definitions

The quantile and profile are reused from `ThresholdFunctions.GaussianTail`.

## Main results

* `standardGaussianQuantile_strictMonoOn`: the quantile is increasing on `(0,1)`.
* `hasDerivAt_standardGaussianQuantile`, `hasDerivAt_gaussianIsoperimetric`: inverse calculus.
* `standardGaussianCDF_neg`, `gaussianIsoperimetric_one_sub`: Gaussian reflection.
* `convexOn_standardGaussianQuantile_sq`: convexity of the squared quantile.
* `continuousOn_closedGaussianProfile`: continuity including endpoint probabilities.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Definition 5.26 and §11.4.
* [Bob97] S. G. Bobkov, *An isoperimetric inequality on the discrete cube, and an
  elementary proof of the isoperimetric inequality in Gauss space*, Annals of
  Probability 25 (1997), 206–214, Proposition 1 and Lemmas 2–3.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace BooleanAnalysis.ThresholdFunctions

/-- The Gaussian quantile is strictly increasing on the open probability interval.
[OD14, Def. 5.26] -/
lemma standardGaussianQuantile_strictMonoOn :
    StrictMonoOn standardGaussianQuantile (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  apply standardGaussianCDF_strictMono.lt_iff_lt.mp
  simpa only [standardGaussianCDF_quantile ha.1 ha.2,
    standardGaussianCDF_quantile hb.1 hb.2] using hab

/-- The Gaussian quantile is continuous at every probability strictly between zero and one.
[OD14, Def. 5.26]

**Proof sketch.** It is strictly increasing, and its image of the open probability
interval is the whole real line, because the cdf and quantile are inverse there.
Continuity follows from the order-theoretic continuity criterion for monotone maps. -/
lemma continuousAt_standardGaussianQuantile {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt standardGaussianQuantile a := by
  apply standardGaussianQuantile_strictMonoOn.continuousAt_of_image_mem_nhds
    (Ioo_mem_nhds ha.1 ha.2)
  have himage : standardGaussianQuantile '' Ioo (0 : ℝ) 1 = univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact ⟨standardGaussianCDF x,
      ⟨standardGaussianCDF_pos x, standardGaussianCDF_lt_one x⟩,
      standardGaussianQuantile_eq rfl⟩
  rw [himage]
  exact Filter.univ_mem

/-- At an interior probability, the Gaussian quantile has derivative the reciprocal
of the isoperimetric profile. [OD14, Def. 5.26; §11.4]

**Proof sketch.** Differentiate the inverse of the strictly increasing Gaussian cdf;
its derivative is the everywhere positive Gaussian density. -/
lemma hasDerivAt_standardGaussianQuantile {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt standardGaussianQuantile (gaussianIsoperimetric a)⁻¹ a := by
  refine HasDerivAt.of_local_left_inverse (continuousAt_standardGaussianQuantile ha)
    (hasDerivAt_standardGaussianCDF _) (ne_of_gt (standardGaussianPDF_pos _)) ?_
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with y hy
  exact standardGaussianCDF_quantile hy.1 hy.2

/-- The derivative of the Gaussian isoperimetric profile on `(0,1)` is the
negative Gaussian quantile. [OD14, Def. 5.26; §11.4]

**Proof sketch.** Apply the chain rule to the density composed with the quantile;
the positive density cancels its reciprocal from the inverse derivative. -/
lemma hasDerivAt_gaussianIsoperimetric {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gaussianIsoperimetric (-standardGaussianQuantile a) a := by
  convert (hasDerivAt_standardGaussianPDF (standardGaussianQuantile a)).comp a
    (hasDerivAt_standardGaussianQuantile ha) using 1
  simp only [gaussianIsoperimetric]
  exact (mul_inv_cancel_right₀ (ne_of_gt (standardGaussianPDF_pos _)) _).symm

/-- The derivative of the negative Gaussian quantile is `-1 / U` on `(0,1)`.
Together with `hasDerivAt_gaussianIsoperimetric`, this is the identity `U U'' = -1`.
[OD14, §11.4] -/
lemma hasDerivAt_neg_standardGaussianQuantile {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => -standardGaussianQuantile p)
      (-(gaussianIsoperimetric a)⁻¹) a :=
  (hasDerivAt_standardGaussianQuantile ha).neg

/-- The standard Gaussian density is an even function. [OD14, Notation 5.14] -/
lemma standardGaussianPDF_neg (x : ℝ) :
    standardGaussianPDF (-x) = standardGaussianPDF x := by
  simp only [standardGaussianPDF_eq, neg_sq]

private lemma hasDerivAt_standardGaussianCDF_reflection_sum (x : ℝ) :
    HasDerivAt (fun t => standardGaussianCDF (-t) + standardGaussianCDF t) 0 x := by
  convert ((hasDerivAt_standardGaussianCDF (-x)).comp x (hasDerivAt_id x).neg).add
    (hasDerivAt_standardGaussianCDF x) using 1
  simp [standardGaussianPDF_neg]

/-- Reflection changes the Gaussian cdf to its complementary probability.
[OD14, Notation 5.14]

**Proof sketch.** Evenness of the density makes the sum of the cdf at opposite
arguments constant. Its limit at positive infinity is one. -/
lemma standardGaussianCDF_neg (x : ℝ) :
    standardGaussianCDF (-x) = 1 - standardGaussianCDF x := by
  have hconst := is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_standardGaussianCDF_reflection_sum t).differentiableAt)
    (fun t => (hasDerivAt_standardGaussianCDF_reflection_sum t).deriv)
  have hlim : Tendsto (fun t => standardGaussianCDF (-t) + standardGaussianCDF t)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [zero_add] using
      ((ProbabilityTheory.tendsto_cdf_atBot standardGaussianMeasure).comp
        tendsto_neg_atTop_atBot).add
        (ProbabilityTheory.tendsto_cdf_atTop standardGaussianMeasure)
  have heq : standardGaussianCDF (-x) + standardGaussianCDF x = 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr (fun t => hconst x t)) hlim
  linarith

/-- Complementing an interior probability negates its Gaussian quantile.
[OD14, Def. 5.26] -/
lemma standardGaussianQuantile_one_sub {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    standardGaussianQuantile (1 - a) = -standardGaussianQuantile a := by
  apply standardGaussianQuantile_eq
  rw [standardGaussianCDF_neg, standardGaussianCDF_quantile ha.1 ha.2]

/-- The Gaussian isoperimetric profile is invariant under complementing an
interior probability. [OD14, Def. 5.26] -/
lemma gaussianIsoperimetric_one_sub {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    gaussianIsoperimetric (1 - a) = gaussianIsoperimetric a := by
  simp only [gaussianIsoperimetric, standardGaussianQuantile_one_sub ha,
    standardGaussianPDF_neg]

/-- Moving an interior probability towards the midpoint decreases the squared
Gaussian quantile. [OD14, Def. 5.26]
The assumptions allow crossing the midpoint as far as the reflected starting point. -/
lemma standardGaussianQuantile_sq_le {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) (hsum : a + b ≤ 1) :
    standardGaussianQuantile b ^ 2 ≤ standardGaussianQuantile a ^ 2 := by
  have hleft := standardGaussianQuantile_strictMonoOn.monotoneOn ha hb hab
  have hright := standardGaussianQuantile_strictMonoOn.monotoneOn hb
    (show 1 - a ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.2], by linarith [ha.1]⟩)
    (show b ≤ 1 - a by linarith)
  rw [standardGaussianQuantile_one_sub ha] at hright
  nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)]

/-- Moving an interior probability towards the midpoint increases the Gaussian
isoperimetric profile. [OD14, Def. 5.26]
The assumptions allow crossing the midpoint as far as the reflected starting point. -/
lemma gaussianIsoperimetric_le_of_le_of_add_le_one {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) (hsum : a + b ≤ 1) :
    gaussianIsoperimetric a ≤ gaussianIsoperimetric b := by
  simp only [gaussianIsoperimetric, standardGaussianPDF_eq]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  linarith [standardGaussianQuantile_sq_le ha hb hab hsum]

/-- The squared Gaussian quantile is convex on the open probability interval.
Equivalently, the square of the derivative of the Gaussian profile is convex.
[Bob97, Lemma 2(b)]

**Proof sketch.** Its first derivative is `2 q / U`, and its second derivative
is `2 (1 + q²) / U²`, which is nonnegative. -/
lemma convexOn_standardGaussianQuantile_sq :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun p => standardGaussianQuantile p ^ 2) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun p => 2 * (standardGaussianQuantile p / gaussianIsoperimetric p))
    (f'' := fun p => 2 * (1 + standardGaussianQuantile p ^ 2) / gaussianIsoperimetric p ^ 2)
    (convex_Ioo 0 1)
    (fun p hp => ((continuousAt_standardGaussianQuantile hp).pow 2).continuousWithinAt)
    ?_ ?_ ?_
  · intro p hp
    have hp' : p ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hp
    convert ((hasDerivAt_standardGaussianQuantile hp').pow 2).hasDerivWithinAt using 1
    simp [div_eq_mul_inv, mul_assoc]
  · intro p hp
    have hp' : p ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hp
    have hn : gaussianIsoperimetric p ≠ 0 := (standardGaussianPDF_pos _).ne'
    convert (((hasDerivAt_standardGaussianQuantile hp').div
      (hasDerivAt_gaussianIsoperimetric hp') hn).const_mul 2).hasDerivWithinAt using 1
    field_simp
    ring
  · intro p hp
    positivity

/-- The product of the Gaussian profile and quantile has derivative `1 - q²`
on the open probability interval. [Bob97, calculation underlying Lemma 3]
This form packages the second derivative calculation for the squared profile. -/
lemma hasDerivAt_gaussianIsoperimetric_mul_standardGaussianQuantile {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => gaussianIsoperimetric p * standardGaussianQuantile p)
      (1 - standardGaussianQuantile a ^ 2) a := by
  convert (hasDerivAt_gaussianIsoperimetric ha).mul
    (hasDerivAt_standardGaussianQuantile ha) using 1
  have hn : gaussianIsoperimetric a ≠ 0 := (standardGaussianPDF_pos _).ne'
  rw [mul_inv_cancel₀ hn]
  ring

/-- The squared Gaussian profile has derivative `-2 U q` on the open probability
interval. [Bob97, calculation underlying Lemma 3] -/
lemma hasDerivAt_gaussianIsoperimetric_sq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun p => gaussianIsoperimetric p ^ 2)
      (-2 * (gaussianIsoperimetric a * standardGaussianQuantile a)) a := by
  convert (hasDerivAt_gaussianIsoperimetric ha).pow 2 using 1
  ring

end BooleanAnalysis.ThresholdFunctions

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- On the open probability interval the closed profile agrees with the
Gaussian density at the quantile. [OD14, Def. 5.26; §11.4] -/
lemma closedGaussianProfile_eq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    closedGaussianProfile a = gaussianIsoperimetric a :=
  if_pos ha

/-- The closed Gaussian profile vanishes at probability zero.
[OD14, §11.4, equation (11.15)] -/
@[simp] lemma closedGaussianProfile_zero : closedGaussianProfile 0 = 0 := by
  simp [closedGaussianProfile]

/-- The closed Gaussian profile vanishes at probability one.
[OD14, §11.4, equation (11.15)] -/
@[simp] lemma closedGaussianProfile_one : closedGaussianProfile 1 = 0 := by
  simp [closedGaussianProfile]

/-- The closed Gaussian profile is nonnegative at every real argument.
[OD14, Def. 5.26; §11.4] -/
lemma closedGaussianProfile_nonneg (a : ℝ) : 0 ≤ closedGaussianProfile a := by
  unfold closedGaussianProfile
  split_ifs
  · exact (standardGaussianPDF_pos _).le
  · exact le_rfl

/-- Complementing the argument leaves the closed Gaussian profile unchanged.
This includes both endpoints and the zero extension outside the probability interval.
[OD14, Def. 5.26; §11.4] -/
lemma closedGaussianProfile_one_sub (a : ℝ) :
    closedGaussianProfile (1 - a) = closedGaussianProfile a := by
  by_cases ha : a ∈ Ioo (0 : ℝ) 1
  · rw [closedGaussianProfile_eq ha,
      closedGaussianProfile_eq (show 1 - a ∈ Ioo (0 : ℝ) 1 from
        ⟨by linarith [ha.2], by linarith [ha.1]⟩), gaussianIsoperimetric_one_sub ha]
  · have hcomp : 1 - a ∉ Ioo (0 : ℝ) 1 := by
      rintro ⟨h0, h1⟩
      exact ha ⟨by linarith, by linarith⟩
    simp [closedGaussianProfile, ha, hcomp]

/-- The closed Gaussian profile tends to zero as the probability decreases to zero.
[OD14, Def. 5.26; §11.4]

**Proof sketch.** The quantile tends to negative infinity, where the Gaussian
density vanishes; near zero on the right the endpoint adapter equals that density. -/
lemma tendsto_closedGaussianProfile_zero :
    Tendsto closedGaussianProfile (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine (tendsto_standardGaussianPDF_atBot.comp tendsto_standardGaussianQuantile).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with p hp hp1
  exact (closedGaussianProfile_eq ⟨hp, hp1⟩).symm

/-- The zero extension of the Gaussian profile is continuous at probability zero.
[OD14, Def. 5.26; §11.4] -/
lemma continuousAt_closedGaussianProfile_zero : ContinuousAt closedGaussianProfile 0 := by
  refine continuousAt_iff_continuous_left_right.mpr ⟨?_, ?_⟩
  · apply (continuousWithinAt_const (b := (0 : ℝ))).congr
    · intro p hp
      simp [closedGaussianProfile, not_lt_of_ge (Set.mem_Iic.mp hp)]
    · exact closedGaussianProfile_zero
  · apply continuousWithinAt_Ioi_iff_Ici.mp
    simpa only [ContinuousWithinAt, closedGaussianProfile_zero] using
      tendsto_closedGaussianProfile_zero

/-- The zero extension of the Gaussian profile is continuous at probability one.
[OD14, Def. 5.26; §11.4] -/
lemma continuousAt_closedGaussianProfile_one : ContinuousAt closedGaussianProfile 1 := by
  have h : ContinuousAt (fun p : ℝ => closedGaussianProfile (1 - p)) 1 :=
    (show ContinuousAt closedGaussianProfile (1 - 1) by
      simpa using continuousAt_closedGaussianProfile_zero).comp
      (continuousAt_const.sub continuousAt_id)
  simpa only [closedGaussianProfile_one_sub] using h

/-- At an interior probability the closed Gaussian profile has derivative the
negative Gaussian quantile. [OD14, Def. 5.26; §11.4] -/
lemma hasDerivAt_closedGaussianProfile {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt closedGaussianProfile (-standardGaussianQuantile a) a := by
  apply (hasDerivAt_gaussianIsoperimetric ha).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with p hp
  exact closedGaussianProfile_eq hp

/-- The closed Gaussian profile is continuous on the full probability interval.
[OD14, Def. 5.26; §11.4]

**Proof sketch.** Use the interior derivative formula away from the endpoints,
and the vanishing density limits at zero and one at the endpoints. -/
lemma continuousOn_closedGaussianProfile :
    ContinuousOn closedGaussianProfile (Icc (0 : ℝ) 1) := by
  intro a ha
  rcases eq_or_lt_of_le ha.1 with h0 | h0
  · subst a
    exact continuousAt_closedGaussianProfile_zero.continuousWithinAt
  rcases eq_or_lt_of_le ha.2 with h1 | h1
  · subst a
    exact continuousAt_closedGaussianProfile_one.continuousWithinAt
  exact (hasDerivAt_closedGaussianProfile ⟨h0, h1⟩).continuousAt.continuousWithinAt

/-- The Gaussian profile extended by zero outside the probability interval is
continuous on the real line. [OD14, Def. 5.26; §11.4]

**Proof sketch.** Use the profile derivative in the interior and its vanishing
endpoint limits. Away from the closed probability interval the extension is
locally constant. -/
lemma continuous_closedGaussianProfile : Continuous closedGaussianProfile := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with p hp
    simp [closedGaussianProfile, not_lt_of_ge hp.le]
  · exact continuousAt_closedGaussianProfile_zero
  rcases lt_trichotomy x 1 with hx1 | rfl | hx1
  · exact (hasDerivAt_closedGaussianProfile ⟨hx, hx1⟩).continuousAt
  · exact continuousAt_closedGaussianProfile_one
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx1] with p hp
    simp [closedGaussianProfile, not_lt_of_ge hp.le]

/-- The closed Gaussian profile of a measurable unit-interval-valued function
is integrable on every finite measure space. [OD14, §11.4, equation (11.15)]

**Proof sketch.** Continuity makes the composition measurable, and compactness
bounds the profile uniformly on the probability interval. Dominate by that
constant, which is integrable for a finite measure. -/
lemma integrable_closedGaussianProfile_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hfrange : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x => closedGaussianProfile (f x)) μ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuousOn_closedGaussianProfile
  exact (integrable_const M).mono'
    (continuous_closedGaussianProfile.measurable.comp hf).aestronglyMeasurable
    (Eventually.of_forall fun x => hM (f x) (hfrange x))

end BooleanAnalysis.GaussianSpace
