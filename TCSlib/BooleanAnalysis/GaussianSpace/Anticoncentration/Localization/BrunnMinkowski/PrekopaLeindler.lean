/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Real
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-dimensional Prékopa–Leindler by level sets

## Main definitions

No new definitions.

## Main results

* `prekopaLeindler_integral_arithmetic_le_of_isLUB_one`: the normalized
  one-dimensional arithmetic integral bound underlying Prékopa–Leindler.
* `prekopaLeindler_integral_le_of_bddAbove`: the multiplicative inequality
  for bounded first and second functions.

## References

* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405,
  Theorem 4.1, first proof. Author manuscript October 25, 2001, pp.6–7:
  https://faculty.gardner.wwu.edu/gorizia12.pdf.
-/

open MeasureTheory
open scoped Pointwise

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- For nonnegative integrable real functions, the one-dimensional
Prékopa–Leindler hypothesis implies an arithmetic integral bound when the
suprema of the first two functions are one.
[Gar02, Theorem 4.1, first proof]

The suprema need not be attained. No compact support or pointwise upper
bound on the third function is required. This is the normalized
arithmetic step; the usual multiplicative conclusion follows later by
rescaling and the weighted arithmetic-geometric mean inequality.

**Proof sketch.** At every height strictly between zero and one, the
superlevel sets of the first two functions are nonempty. Their weighted
Minkowski sum lies in the superlevel set of the third function: the
weighted geometric mean of two numbers at least the height is at least
that height. Apply the weighted real sum-set volume inequality. Integrate
the resulting inequality over heights using layer cake. The first two
functions are bounded above by one, and the exceptional endpoint height
one has measure zero. Convert the nonnegative Lebesgue integrals to
ordinary integrals using integrability. -/
theorem prekopaLeindler_integral_arithmetic_le_of_isLUB_one
    {f g h : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfint : Integrable f) (hgint : Integrable g) (hhint : Integrable h)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 ≤ g x)
    (hhnonneg : ∀ x : ℝ, 0 ≤ h x)
    (hfsup : IsLUB (Set.range f) 1)
    (hgsup : IsLUB (Set.range g) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hfg : ∀ x y : ℝ,
      (f x) ^ (1 - t) * (g y) ^ t ≤ h ((1 - t) * x + t * y)) :
    (1 - t) * (∫ x : ℝ, f x) + t * (∫ x : ℝ, g x) ≤
      ∫ x : ℝ, h x :=
  (by
  have ht0 : 0 ≤ t := ht.1.le
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2.le
  let F (u : ℝ) := volume {x | u ≤ f x}
  let G (u : ℝ) := volume {x | u ≤ g x}
  let H (u : ℝ) := volume {x | u ≤ h x}
  have hFm : Measurable F :=
    (show Antitone F from fun u v huv => measure_mono (fun x hx => huv.trans hx)).measurable
  have hGm : Measurable G :=
    (show Antitone G from fun u v huv => measure_mono (fun x hx => huv.trans hx)).measurable
  have hlevel (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
      ENNReal.ofReal (1 - t) * F u + ENNReal.ofReal t * G u ≤ H u := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (lt_isLUB_iff hfsup).mp hu1
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := (lt_isLUB_iff hgsup).mp hu1
    apply ofReal_mul_volume_add_le_of_smul_add_subset
      (measurableSet_le measurable_const hf) (measurableSet_le measurable_const hg)
      ⟨x, hx.le⟩ ⟨y, hy.le⟩ h1t ht0
    rintro z ⟨x', hx', y', hy', rfl⟩
    obtain ⟨x', hx', rfl⟩ := hx'
    obtain ⟨y', hy', rfl⟩ := hy'
    change u ≤ h ((1 - t) * x' + t * y')
    calc
      u = u ^ (1 - t) * u ^ t := by
        rw [← Real.rpow_add hu, sub_add_cancel, Real.rpow_one]
      _ ≤ (f x') ^ (1 - t) * (g y') ^ t :=
        mul_le_mul (Real.rpow_le_rpow hu.le hx' h1t)
          (Real.rpow_le_rpow hu.le hy' ht0) (Real.rpow_nonneg hu.le _)
          (Real.rpow_nonneg (hfnonneg x') _)
      _ ≤ _ := hfg x' y'
  have hae : ∀ᵐ u : ℝ, u ≠ 1 := by
    rw [ae_iff]
    simp
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ENNReal.ofReal (1 - t) * F u + ENNReal.ofReal t * G u ≤ H u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hae] with u hu hne
    by_cases hu1 : u < 1
    · exact hlevel u hu hu1
    · have hgt : 1 < u := lt_of_le_of_ne (le_of_not_gt hu1) (Ne.symm hne)
      have heF : {x | u ≤ f x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (not_le_of_gt ((hfsup.1 ⟨x, rfl⟩).trans_lt hgt)) hx
      have heG : {x | u ≤ g x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (not_le_of_gt ((hgsup.1 ⟨x, rfl⟩).trans_lt hgt)) hx
      simp only [F, G, heF, heG, measure_empty, mul_zero, zero_add, zero_le]
  have hineq := lintegral_mono_ae hpoint
  rw [lintegral_add_left (measurable_const.mul hFm), lintegral_const_mul _ hFm,
    lintegral_const_mul _ hGm] at hineq
  have hfl := lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hfnonneg) hf.aemeasurable
  have hgl := lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hgnonneg) hg.aemeasurable
  have hhl := lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hhnonneg) hh.aemeasurable
  change ENNReal.ofReal (1 - t) * (∫⁻ u in Set.Ioi (0 : ℝ), F u) +
    ENNReal.ofReal t * (∫⁻ u in Set.Ioi (0 : ℝ), G u) ≤ ∫⁻ u in Set.Ioi (0 : ℝ), H u at hineq
  rw [← hfl, ← hgl, ← hhl,
    ← ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall hfnonneg),
    ← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall hgnonneg),
    ← ofReal_integral_eq_lintegral_ofReal hhint (Filter.Eventually.of_forall hhnonneg)] at hineq
  have hfn : 0 ≤ ∫ x, f x := integral_nonneg hfnonneg
  have hgn : 0 ≤ ∫ x, g x := integral_nonneg hgnonneg
  rw [← ENNReal.ofReal_mul h1t, ← ENNReal.ofReal_mul ht0,
    ← ENNReal.ofReal_add (mul_nonneg h1t hfn) (mul_nonneg ht0 hgn)] at hineq
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hhnonneg)).mp hineq
)

/-- The one-dimensional Prékopa–Leindler inequality for nonnegative
integrable measurable functions when the first two functions are bounded.
[Gar02, Theorem 4.1, first proof]

Only the first two functions need pointwise upper bounds; the third
function may be unbounded. No compact support or attainment of a supremum
is required.

**Proof sketch.** Let the two suprema be `F` and `G`. If either is zero,
the corresponding nonnegative function is identically zero and the
conclusion follows from nonnegativity of the third integral. Otherwise
divide the first two functions by `F` and `G`, and the third function by
`F ^ (1 - t) * G ^ t`. Apply the normalized arithmetic integral
inequality. Weighted arithmetic-geometric mean bounds the geometric mean
of the two normalized integrals by their weighted sum. Multiply by the
positive normalizing factor and simplify the powers of quotients. -/
theorem prekopaLeindler_integral_le_of_bddAbove
    {f g h : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfint : Integrable f) (hgint : Integrable g) (hhint : Integrable h)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 ≤ g x)
    (hhnonneg : ∀ x : ℝ, 0 ≤ h x)
    (hfbdd : BddAbove (Set.range f)) (hgbdd : BddAbove (Set.range g))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hfg : ∀ x y : ℝ,
      (f x) ^ (1 - t) * (g y) ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫ x : ℝ, f x) ^ (1 - t) * (∫ x : ℝ, g x) ^ t ≤
      ∫ x : ℝ, h x :=
  (by
  let F := sSup (Set.range f)
  let G := sSup (Set.range g)
  have hF : IsLUB (Set.range f) F := isLUB_csSup (Set.range_nonempty f) hfbdd
  have hG : IsLUB (Set.range g) G := isLUB_csSup (Set.range_nonempty g) hgbdd
  have hFn : 0 ≤ F := (hfnonneg 0).trans (hF.1 ⟨0, rfl⟩)
  have hGn : 0 ≤ G := (hgnonneg 0).trans (hG.1 ⟨0, rfl⟩)
  by_cases hF0 : F = 0
  · have hf0 : f = fun _ => 0 := funext fun x =>
      le_antisymm (hF0 ▸ hF.1 ⟨x, rfl⟩) (hfnonneg x)
    rw [hf0, integral_zero, Real.zero_rpow (ne_of_gt (sub_pos.mpr ht.2)), zero_mul]
    exact integral_nonneg hhnonneg
  by_cases hG0 : G = 0
  · have hg0 : g = fun _ => 0 := funext fun x =>
      le_antisymm (hG0 ▸ hG.1 ⟨x, rfl⟩) (hgnonneg x)
    rw [hg0, integral_zero, Real.zero_rpow (ne_of_gt ht.1), mul_zero]
    exact integral_nonneg hhnonneg
  have hFp : 0 < F := lt_of_le_of_ne hFn (Ne.symm hF0)
  have hGp : 0 < G := lt_of_le_of_ne hGn (Ne.symm hG0)
  let N := F ^ (1 - t) * G ^ t
  have hNp : 0 < N := mul_pos (Real.rpow_pos_of_pos hFp _) (Real.rpow_pos_of_pos hGp _)
  have hnorm {k : ℝ → ℝ} {M : ℝ} (hM : IsLUB (Set.range k) M) (hMp : 0 < M) :
      IsLUB (Set.range (fun x => k x / M)) 1 := by
    simpa only [← Set.range_comp, ← div_eq_mul_inv, div_self hMp.ne'] using
      (IsLUB.mul_right (inv_nonneg.mpr hMp.le) hM)
  have hnormalized : ∀ x y : ℝ,
      (f x / F) ^ (1 - t) * (g y / G) ^ t ≤
        h ((1 - t) * x + t * y) / N := by
    intro x y
    rw [Real.div_rpow (hfnonneg x) hFn, Real.div_rpow (hgnonneg y) hGn,
      div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hfg x y) hNp.le
  have harith := prekopaLeindler_integral_arithmetic_le_of_isLUB_one
    (hf.div_const F) (hg.div_const G) (hh.div_const N)
    (hfint.div_const F) (hgint.div_const G) (hhint.div_const N)
    (fun x => div_nonneg (hfnonneg x) hFn)
    (fun x => div_nonneg (hgnonneg x) hGn)
    (fun x => div_nonneg (hhnonneg x) hNp.le)
    (hnorm hF hFp) (hnorm hG hGp) ht hnormalized
  rw [integral_div, integral_div, integral_div] at harith
  have hfi : 0 ≤ ∫ x, f x := integral_nonneg hfnonneg
  have hgi : 0 ≤ ∫ x, g x := integral_nonneg hgnonneg
  have hmean := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr ht.2.le) ht.1.le (div_nonneg hfi hFn) (div_nonneg hgi hGn)
    (show (1 - t) + t = 1 by ring)
  have hquot : ((∫ x, f x) ^ (1 - t) * (∫ x, g x) ^ t) / N ≤ (∫ x, h x) / N := by
    calc
      _ = ((∫ x, f x) / F) ^ (1 - t) * ((∫ x, g x) / G) ^ t := by
        rw [Real.div_rpow hfi hFn, Real.div_rpow hgi hGn, div_mul_div_comm]
      _ ≤ (1 - t) * ((∫ x, f x) / F) + t * ((∫ x, g x) / G) := hmean
      _ ≤ _ := harith
  exact (div_le_div_iff_of_pos_right hNp).mp hquot
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
