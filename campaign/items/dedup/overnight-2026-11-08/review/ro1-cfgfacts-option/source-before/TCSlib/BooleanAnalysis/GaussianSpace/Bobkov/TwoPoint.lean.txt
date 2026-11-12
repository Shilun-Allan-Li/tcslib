/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Profile

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Analytic estimates for Bobkov's two-point inequality

## Main definitions

The Gaussian quantile and isoperimetric profile are reused without alteration.

## Main results

The symmetric squared-profile estimates give an elementary calculus proof of
the scalar inequality, following Bobkov's original argument.

## References

* [Bob97] S. G. Bobkov, *An isoperimetric inequality on the discrete cube, and an
  elementary proof of the isoperimetric inequality in Gauss space*, Annals of
  Probability 25 (1997), 206–214, Proposition 1 and Lemmas 2–3.
* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Bobkov's Two-Point Inequality.
-/

open Filter Set
open scoped Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A bound on the squared difference of two nonnegative quantities implies
the square-root average inequality used in Bobkov's argument.
[Bob97, Prop. 1, equations (17)–(20)]

**Proof sketch.** Rearrange the hypothesis into a bound on the square of
`4 c² - A - B`. If the desired square-root inequality failed, both factors
of its difference from `4 A B` would be positive, a contradiction. -/
private lemma sqrt_average_of_sq_difference_le (c A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : (A - B) ^ 2 ≤ 8 * c ^ 2 * (A + B - 2 * c ^ 2)) :
    c ≤ (Real.sqrt A + Real.sqrt B) / 2 := by
  have ha := Real.sqrt_nonneg A
  have hb := Real.sqrt_nonneg B
  have ha2 := Real.sq_sqrt hA
  have hb2 := Real.sq_sqrt hB
  have hab2 := congrArg₂ (fun x y : ℝ => x * y) ha2 hb2
  have hgap : (4 * c ^ 2 - A - B) ^ 2 ≤ 4 * A * B := by nlinarith [h]
  by_contra hle
  have hs : Real.sqrt A + Real.sqrt B < 2 * c := by linarith
  have hs2 : (Real.sqrt A + Real.sqrt B) ^ 2 < 4 * c ^ 2 := by nlinarith
  have hdiff : 0 < 4 * c ^ 2 - A - B - 2 * Real.sqrt A * Real.sqrt B := by
    nlinarith
  have hsum : 0 < 4 * c ^ 2 - A - B + 2 * Real.sqrt A * Real.sqrt B :=
    lt_of_lt_of_le hdiff (by nlinarith [mul_nonneg ha hb])
  have hpos := mul_pos hdiff hsum
  nlinarith [hpos]

private lemma shifted_probabilities_mem {a b t : ℝ} (hb : 0 ≤ b)
    (hminus : 0 < a - b) (hplus : a + b < 1) (ht : t ∈ Icc (0 : ℝ) b) :
    a + t ∈ Ioo (0 : ℝ) 1 ∧ a - t ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
    ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

private lemma hasDerivAt_profile_sq_pair (a t k : ℝ)
    (hp : a + t ∈ Ioo (0 : ℝ) 1) (hm : a - t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => gaussianIsoperimetric (a + x) ^ 2 +
      k * gaussianIsoperimetric (a - x) ^ 2)
      (-2 * (gaussianIsoperimetric (a + t) * standardGaussianQuantile (a + t)) +
        2 * k * (gaussianIsoperimetric (a - t) * standardGaussianQuantile (a - t))) t := by
  convert ((hasDerivAt_gaussianIsoperimetric_sq hp).comp t
    ((hasDerivAt_id t).const_add a)).add
    (((hasDerivAt_gaussianIsoperimetric_sq hm).comp t
      ((hasDerivAt_const t a).sub (hasDerivAt_id t))).const_mul k) using 1
  ring

private lemma hasDerivAt_profile_sq_pair_derivative (a t k : ℝ)
    (hp : a + t ∈ Ioo (0 : ℝ) 1) (hm : a - t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x =>
      -2 * (gaussianIsoperimetric (a + x) * standardGaussianQuantile (a + x)) +
        2 * k * (gaussianIsoperimetric (a - x) * standardGaussianQuantile (a - x)))
      (2 * (standardGaussianQuantile (a + t) ^ 2 +
        k * standardGaussianQuantile (a - t) ^ 2 - 1 - k)) t := by
  convert (((hasDerivAt_gaussianIsoperimetric_mul_standardGaussianQuantile hp).comp t
    ((hasDerivAt_id t).const_add a)).const_mul (-2)).add
    (((hasDerivAt_gaussianIsoperimetric_mul_standardGaussianQuantile hm).comp t
      ((hasDerivAt_const t a).sub (hasDerivAt_id t))).const_mul (2 * k)) using 1
  ring

/-- Below the midpoint, the difference of squared profile values at symmetric
arguments is concave as a function of the nonnegative displacement.
[Bob97, Prop. 1, proof of equation (22)]

**Proof sketch.** Its second derivative is twice the difference of squared
quantiles at the symmetric arguments. The argument nearer the midpoint has
the smaller squared quantile, so this second derivative is nonpositive. -/
private lemma concaveOn_profile_sq_difference {a b : ℝ} (hb : 0 ≤ b)
    (hminus : 0 < a - b) (hplus : a + b < 1) (ha : a ≤ 1 / 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) b)
      (fun x => gaussianIsoperimetric (a + x) ^ 2 -
        gaussianIsoperimetric (a - x) ^ 2) := by
  have hmem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) b) :=
    shifted_probabilities_mem hb hminus hplus hx
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := fun x =>
      -2 * (gaussianIsoperimetric (a + x) * standardGaussianQuantile (a + x)) +
        2 * (-1) * (gaussianIsoperimetric (a - x) * standardGaussianQuantile (a - x)))
    (f'' := fun x => 2 * (standardGaussianQuantile (a + x) ^ 2 +
      (-1) * standardGaussianQuantile (a - x) ^ 2 - 1 - (-1)))
    (convex_Icc _ _) ?_ ?_ ?_ ?_
  · intro x hx
    simpa only [neg_one_mul, sub_eq_add_neg] using
      (hasDerivAt_profile_sq_pair a x (-1) (hmem hx).1 (hmem hx).2).continuousAt.continuousWithinAt
  · intro x hx
    simpa only [neg_one_mul, sub_eq_add_neg] using
      (hasDerivAt_profile_sq_pair a x (-1) (hmem (interior_subset hx)).1
        (hmem (interior_subset hx)).2).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_profile_sq_pair_derivative a x (-1)
      (hmem (interior_subset hx)).1 (hmem (interior_subset hx)).2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have hq := standardGaussianQuantile_sq_le (hmem hx').2 (hmem hx').1
      (by linarith [hx'.1]) (by linarith)
    linarith

/-- The squared difference of the two symmetric squared profile values is
bounded by the squared tangent estimate at the midpoint.
[Bob97, Prop. 1, equations (21)–(22)]

**Proof sketch.** Below probability one half, the symmetric difference is
nonnegative and concave in the displacement, so it lies below its tangent at
zero. Squaring gives the claim. -/
private lemma profile_sq_difference_bound {a b : ℝ} (hb : 0 ≤ b)
    (hminus : 0 < a - b) (hplus : a + b < 1) (ha : a ≤ 1 / 2) :
    (gaussianIsoperimetric (a + b) ^ 2 - gaussianIsoperimetric (a - b) ^ 2) ^ 2 ≤
      16 * gaussianIsoperimetric a ^ 2 * standardGaussianQuantile a ^ 2 * b ^ 2 := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp
  have hmem := shifted_probabilities_mem hb.le hminus hplus (show b ∈ Icc (0 : ℝ) b from ⟨hb.le, le_rfl⟩)
  have ha' : a ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hd : HasDerivAt (fun x => gaussianIsoperimetric (a + x) ^ 2 -
      gaussianIsoperimetric (a - x) ^ 2)
      (-4 * (gaussianIsoperimetric a * standardGaussianQuantile a)) 0 := by
    convert hasDerivAt_profile_sq_pair a 0 (-1) (by simpa using ha')
      (by simpa using ha') using 1
    · funext x
      ring
    · simp only [add_zero, sub_zero]
      ring
  have hs := (concaveOn_profile_sq_difference hb.le hminus hplus ha).slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb.le⟩)
    (show b ∈ Icc (0 : ℝ) b from ⟨hb.le, le_rfl⟩) hb hd
  simp only [slope_def_field, add_zero, sub_zero, sub_self] at hs
  have hu := (div_le_iff₀ hb).mp hs
  have hi := gaussianIsoperimetric_le_of_le_of_add_le_one hmem.2 hmem.1
    (by linarith) (by linarith)
  have hnonneg : 0 ≤ gaussianIsoperimetric (a + b) ^ 2 -
      gaussianIsoperimetric (a - b) ^ 2 := by
    nlinarith [show 0 < gaussianIsoperimetric (a - b) from standardGaussianPDF_pos _]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (add_nonneg hnonneg (hnonneg.trans hu))]

/-- Subtracting the quadratic tangent correction makes the symmetric squared
profile sum convex in the displacement. [Bob97, Lemma 3]

**Proof sketch.** Differentiate twice. The second derivative is twice the
symmetric deficit of the squared quantile, hence nonnegative by its convexity. -/
private lemma convexOn_profile_sq_deficit {a b : ℝ}
    (hminus : 0 < a - b) (hplus : a + b < 1) :
    ConvexOn ℝ (Icc (-b) b) (fun x =>
      gaussianIsoperimetric (a + x) ^ 2 + gaussianIsoperimetric (a - x) ^ 2 +
        2 * (1 - standardGaussianQuantile a ^ 2) * x ^ 2) := by
  let R' : ℝ → ℝ := fun x =>
    -2 * (gaussianIsoperimetric (a + x) * standardGaussianQuantile (a + x)) +
      2 * (gaussianIsoperimetric (a - x) * standardGaussianQuantile (a - x)) +
      4 * (1 - standardGaussianQuantile a ^ 2) * x
  let R'' : ℝ → ℝ := fun x =>
    2 * (standardGaussianQuantile (a + x) ^ 2 +
      standardGaussianQuantile (a - x) ^ 2 - 2 * standardGaussianQuantile a ^ 2)
  have hmem (x : ℝ) (hx : x ∈ Icc (-b) b) :
      (a + x ∈ Ioo (0 : ℝ) 1) ∧ (a - x ∈ Ioo (0 : ℝ) 1) := by
    constructor <;> constructor <;> linarith [hx.1, hx.2]
  have hR (x : ℝ) (hx : x ∈ Icc (-b) b) :
      HasDerivAt (fun t =>
        gaussianIsoperimetric (a + t) ^ 2 + gaussianIsoperimetric (a - t) ^ 2 +
          2 * (1 - standardGaussianQuantile a ^ 2) * t ^ 2) (R' x) x := by
    convert (hasDerivAt_profile_sq_pair a x 1 (hmem x hx).1 (hmem x hx).2).add
      ((hasDerivAt_pow 2 x).const_mul (2 * (1 - standardGaussianQuantile a ^ 2))) using 1
    dsimp [R']
    all_goals first | (funext t; dsimp; ring) | ring
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := R') (f'' := R'')
    (convex_Icc _ _) (fun x hx => (hR x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hR x (interior_subset hx)).hasDerivWithinAt) ?_ ?_
  · intro x hx
    convert ((hasDerivAt_profile_sq_pair_derivative a x 1
      (hmem x (interior_subset hx)).1 (hmem x (interior_subset hx)).2).add
      ((hasDerivAt_id x).const_mul (4 * (1 - standardGaussianQuantile a ^ 2)))).hasDerivWithinAt using 1
    dsimp [R', R'']
    all_goals first | (funext t; dsimp; ring) | ring
  · intro x hx
    have hh := convexOn_standardGaussianQuantile_sq.2
      (hmem x (interior_subset hx)).1 (hmem x (interior_subset hx)).2
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have heq : (1 / 2 : ℝ) • (a + x) + (1 / 2 : ℝ) • (a - x) = a := by
      simp only [smul_eq_mul]
      ring
    rw [heq] at hh
    dsimp [R'']
    simp only [smul_eq_mul] at hh
    linarith

/-- The symmetric squared-profile deficit dominates the quadratic term given
by the squared quantile at its midpoint. [Bob97, Lemma 3]

**Proof sketch.** Evaluate convexity of the even corrected profile sum at
opposite displacements; its value at zero is its minimum. -/
private lemma profile_sq_central_deficit {a b : ℝ} (hb : 0 ≤ b)
    (hminus : 0 < a - b) (hplus : a + b < 1) :
    2 * standardGaussianQuantile a ^ 2 * b ^ 2 ≤
      gaussianIsoperimetric (a + b) ^ 2 + gaussianIsoperimetric (a - b) ^ 2 +
        2 * b ^ 2 - 2 * gaussianIsoperimetric a ^ 2 := by
  have hh := (convexOn_profile_sq_deficit hminus hplus).2
    (show -b ∈ Icc (-b) b from ⟨le_rfl, by linarith⟩)
    (show b ∈ Icc (-b) b from ⟨by linarith, le_rfl⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have heq : (1 / 2 : ℝ) • (-b) + (1 / 2 : ℝ) • b = 0 := by
    simp only [smul_eq_mul]
    ring
  rw [heq] at hh
  simp only [add_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    ← sub_eq_add_neg, sub_neg_eq_add, neg_sq, smul_eq_mul] at hh
  nlinarith

/-- Bobkov's two-point bound holds for interior arguments whose midpoint is
at most one half and whose displacement is nonnegative.
[Bob97, Prop. 1, equations (17)–(22)]

**Proof sketch.** Combine the lower bound for the symmetric deficit with the
upper bound for the squared symmetric difference. The algebraic square-root
criterion then gives the desired inequality. -/
private lemma two_point_interior_half {a b : ℝ} (hb : 0 ≤ b)
    (hminus : 0 < a - b) (hplus : a + b < 1) (ha : a ≤ 1 / 2) :
    gaussianIsoperimetric a ≤
      (Real.sqrt (gaussianIsoperimetric (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (gaussianIsoperimetric (a - b) ^ 2 + b ^ 2)) / 2 := by
  apply sqrt_average_of_sq_difference_le _ _ _ (by positivity) (by positivity)
  have hu := profile_sq_difference_bound hb hminus hplus ha
  have hl := mul_le_mul_of_nonneg_left (profile_sq_central_deficit hb hminus hplus)
    (show 0 ≤ 8 * gaussianIsoperimetric a ^ 2 by positivity)
  nlinarith

/-- Bobkov's two-point inequality holds for positive displacement and interior
endpoint probabilities. [Bob97, Prop. 1]

**Proof sketch.** Reflect the midpoint across one half if necessary, using
symmetry of the Gaussian profile. -/
private lemma two_point_interior_nonneg {a b : ℝ} (hb : 0 ≤ b)
    (hminus : a - b ∈ Ioo (0 : ℝ) 1) (hplus : a + b ∈ Ioo (0 : ℝ) 1) :
    gaussianIsoperimetric a ≤
      (Real.sqrt (gaussianIsoperimetric (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (gaussianIsoperimetric (a - b) ^ 2 + b ^ 2)) / 2 := by
  by_cases ha : a ≤ 1 / 2
  · exact two_point_interior_half hb hminus.1 hplus.2 ha
  have ha' : a ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hminus.1], by linarith [hplus.2]⟩
  have h := two_point_interior_half (a := 1 - a) hb
    (by linarith [hplus.2]) (by linarith [hminus.1]) (by linarith)
  simpa only [show 1 - a + b = 1 - (a - b) by ring,
    show 1 - a - b = 1 - (a + b) by ring,
    gaussianIsoperimetric_one_sub ha', gaussianIsoperimetric_one_sub hminus,
    gaussianIsoperimetric_one_sub hplus, add_comm] using h

/-- Bobkov's two-point inequality holds when both endpoint probabilities are
strictly between zero and one. [Bob97, Prop. 1]

**Proof sketch.** Negating the displacement exchanges the two endpoint terms. -/
private lemma two_point_interior {a b : ℝ}
    (hminus : a - b ∈ Ioo (0 : ℝ) 1) (hplus : a + b ∈ Ioo (0 : ℝ) 1) :
    gaussianIsoperimetric a ≤
      (Real.sqrt (gaussianIsoperimetric (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (gaussianIsoperimetric (a - b) ^ 2 + b ^ 2)) / 2 := by
  rcases le_total 0 b with hb | hb
  · exact two_point_interior_nonneg hb hminus hplus
  · simpa only [← sub_eq_add_neg, sub_neg_eq_add, neg_sq, add_comm] using
      two_point_interior_nonneg (a := a) (b := -b) (neg_nonneg.mpr hb)
        (by simpa only [sub_neg_eq_add] using hplus)
        (by simpa only [← sub_eq_add_neg] using hminus)

private lemma contracted_probability_mem {a b ρ : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hp : a + b ∈ Icc (0 : ℝ) 1)
    (hρ : ρ ∈ Ico (0 : ℝ) 1) : a + ρ * b ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hρ.2) ha.1, mul_nonneg hρ.1 hp.1]
  · nlinarith [mul_pos (sub_pos.mpr hρ.2) (sub_pos.mpr ha.2),
      mul_nonneg hρ.1 (sub_nonneg.mpr hp.2)]

/-- The profile along a line segment in the probability interval tends to its
endpoint value as the segment parameter increases to one. -/
private lemma tendsto_closedGaussianProfile_affine_left {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + b ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun ρ : ℝ => closedGaussianProfile (a + ρ * b))
      (𝓝[<] (1 : ℝ)) (𝓝 (closedGaussianProfile (a + b))) := by
  apply (continuousOn_closedGaussianProfile (a + b) hab).tendsto.comp
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun ρ : ℝ => a + ρ * b) ?_ ?_
  · have h : Tendsto (fun ρ : ℝ => a + ρ * b) (𝓝 1) (𝓝 (a + 1 * b)) :=
      tendsto_const_nhds.add (tendsto_id.mul_const b)
    simpa only [one_mul] using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))]
      with ρ hρ1 hρ0
    convert (convex_Icc (0 : ℝ) 1) ha hab
      (show 0 ≤ 1 - ρ by linarith [show ρ < 1 from hρ1]) hρ0.le (by ring) using 1
    simp only [smul_eq_mul]
    ring

/-- Bobkov's two-point inequality allows endpoint probabilities zero and one
when their midpoint is interior. [Bob97, Prop. 1; OD14, §11.4]

**Proof sketch.** Multiply the displacement by a parameter less than one to
move both endpoints into the open interval. Apply the interior inequality and
let the parameter increase to one, using continuity of the closed profile. -/
lemma closedGaussianProfile_two_point_of_mem_Ioo {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hplus : a + b ∈ Icc (0 : ℝ) 1)
    (hminus : a - b ∈ Icc (0 : ℝ) 1) :
    closedGaussianProfile a ≤
      (Real.sqrt (closedGaussianProfile (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (closedGaussianProfile (a - b) ^ 2 + b ^ 2)) / 2 := by
  have hp := tendsto_closedGaussianProfile_affine_left ⟨ha.1.le, ha.2.le⟩ hplus
  have hm := tendsto_closedGaussianProfile_affine_left (b := -b) ⟨ha.1.le, ha.2.le⟩
    (by simpa only [← sub_eq_add_neg] using hminus)
  have hb : Tendsto (fun ρ : ℝ => (ρ * b) ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 (b ^ 2)) := by
    simpa only [one_mul] using ((tendsto_id.mul_const b).pow 2).mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  have hlim := (((hp.pow 2).add hb).sqrt.add (((hm.pow 2).add hb).sqrt)).div_const 2
  apply ge_of_tendsto (by simpa only [← sub_eq_add_neg, mul_neg] using hlim)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))]
    with ρ hρ1 hρ0
  have hρ : ρ ∈ Ico (0 : ℝ) 1 := ⟨hρ0.le, hρ1⟩
  have hp' := contracted_probability_mem ha hplus hρ
  have hm' : a - ρ * b ∈ Ioo (0 : ℝ) 1 := by
    simpa only [mul_neg, ← sub_eq_add_neg] using
      contracted_probability_mem (b := -b) ha
        (by simpa only [← sub_eq_add_neg] using hminus) hρ
  simpa only [closedGaussianProfile_eq ha, closedGaussianProfile_eq hp',
    closedGaussianProfile_eq hm'] using two_point_interior hm' hp'

end BooleanAnalysis.GaussianSpace
