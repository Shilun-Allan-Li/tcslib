/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Action

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Brunn–Minkowski for compact sets

## Main definitions

No new definitions.

## Main results

* `volumeReal_rpow_mul_rpow_le_of_smul_add_subset`: the multiplicative
  volume inequality for compact sets and a compact containing set.
* `volumeReal_rpow_le_of_smul_add_subset_of_pos`: the dimension-root volume
  inequality for positive-volume compact sets.
* `mul_volumeReal_rpow_le_of_affine_image_subset`: translated-dilation
  comparisons of dimension-root volumes.
* `volumeReal_rpow_le_of_smul_add_subset`: the full dimension-root inequality,
  including endpoint weights and zero-volume nonempty inputs.

## References

* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405,
  Theorem 5.2 and Corollary 5.3, applying Theorem 4.2 to indicator functions. Author
  manuscript October 25, 2001, p.9:
  https://faculty.gardner.wwu.edu/gorizia12.pdf.
-/

open MeasureTheory
open scoped Pointwise

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- The weighted geometric mean of the volumes of two compact sets is
at most the volume of a compact set containing their weighted Minkowski
sum.
[Gar02, Theorem 5.2, compact-set specialization]

No convexity, nonemptiness or positive-volume assumption is required.
The dimension may be zero. Volumes are expressed as real numbers because
all three sets have finite volume.

**Proof sketch.** Apply finite-dimensional Prékopa–Leindler to the three
indicator functions with value one. Compactness gives measurability,
compact support and integrability; all indicators are nonnegative and
bounded by one. When both source points belong to their respective sets,
the containing-set hypothesis places their weighted sum in the third
set. Otherwise a zero indicator raised to a positive exponent makes
the pointwise product zero. The integrals of the indicators are exactly
the corresponding real volumes. -/
theorem volumeReal_rpow_mul_rpow_le_of_smul_add_subset
    {n : ℕ} {A B C : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hsub : (1 - t) • A + t • B ⊆ C) :
    (volume.real A) ^ (1 - t) * (volume.real B) ^ t ≤ volume.real C :=
  (by
  classical
  let I (S : Set (Fin n → ℝ)) := S.indicator (fun _ => (1 : ℝ))
  have prep (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
      Measurable (I S) ∧ Integrable (I S) ∧
        (∀ x, 0 ≤ I S x) ∧ BddAbove (Set.range (I S)) ∧ HasCompactSupport (I S) := by
    have hSm := hS.isClosed.measurableSet
    refine ⟨measurable_const.indicator hSm,
      (integrableOn_const hS.measure_ne_top).integrable_indicator hSm, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ S <;> simp [I, hx]
    · refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ S <;> simp [I, hx]
    · exact HasCompactSupport.of_support_subset_isCompact hS Set.support_indicator_subset
  obtain ⟨hf, hfi, hfn, hfb, hfc⟩ := prep A hA
  obtain ⟨hg, hgi, hgn, hgb, hgc⟩ := prep B hB
  obtain ⟨hh, hhi, hhn, hhb, hhc⟩ := prep C hC
  have hpoint (x y : Fin n → ℝ) :
      I A x ^ (1 - t) * I B y ^ t ≤ I C ((1 - t) • x + t • y) := by
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hz : (1 - t) • x + t • y ∈ C :=
          hsub (Set.mem_add.mpr ⟨(1 - t) • x, Set.smul_mem_smul_set hx,
            t • y, Set.smul_mem_smul_set hy, rfl⟩)
        simp only [I, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hz, Real.one_rpow, one_mul, le_refl]
      · simp only [I, Set.indicator_of_notMem hy,
          Real.zero_rpow (ne_of_gt ht.1), mul_zero]
        exact hhn _
    · simp only [I, Set.indicator_of_notMem hx,
        Real.zero_rpow (ne_of_gt (sub_pos.mpr ht.2)), zero_mul]
      exact hhn _
  have h := prekopaLeindler_integral_le_of_bddAbove_hasCompactSupport
    hf hg hh hfi hgi hhi hfn hgn hhn hfb hgb hhb hfc hgc hhc ht hpoint
  simpa only [I, integral_indicator_const (1 : ℝ) hA.isClosed.measurableSet,
    integral_indicator_const (1 : ℝ) hB.isClosed.measurableSet,
    integral_indicator_const (1 : ℝ) hC.isClosed.measurableSet, smul_eq_mul, mul_one] using h
)

/-- For compact sets of positive volume and strictly interior weights,
the weighted sum of their dimension-root volumes is at most the
dimension-root volume of a compact set containing their weighted sum.
[Gar02, Corollary 5.3, positive-volume normalization step]

This is the positive-volume core: both input volumes and both weights
are strictly positive. Nonemptiness hypotheses are unnecessary because
they follow from the positive volumes.

**Proof sketch.** Let `a` and `b` be the dimension roots of the two
positive input volumes, and put `S = (1 - t) * a + t * b`.
The dilations of the inputs by `1 / a` and `1 / b` have volume one.
Give them weights `(1 - t) * a / S` and `t * b / S`. Their weighted
sum lies in the dilation of the containing set by `1 / S`.
Multiplicative Brunn–Minkowski gives volume at least one for this
containing dilation. Volume homogeneity gives `S ^ n ≤ volume.real C`;
taking the positive dimension root yields the conclusion. -/
theorem volumeReal_rpow_le_of_smul_add_subset_of_pos
    {n : ℕ} (hn : 1 ≤ n) {A B C : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    (hApos : 0 < volume.real A) (hBpos : 0 < volume.real B)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hsub : (1 - t) • A + t • B ⊆ C) :
    (1 - t) * (volume.real A) ^ (1 / (n : ℝ)) +
      t * (volume.real B) ^ (1 / (n : ℝ)) ≤
        (volume.real C) ^ (1 / (n : ℝ)) :=
  (by
  have hn0 : n ≠ 0 := by omega
  have hscale (r : ℝ) (hr : 0 ≤ r) (D : Set (Fin n → ℝ)) :
      volume.real (r • D) = r ^ n * volume.real D := by
    have he := congrArg ENNReal.toReal
      (Measure.addHaar_smul_of_nonneg (volume : Measure (Fin n → ℝ)) hr D)
    have hd : Module.finrank ℝ (Fin n → ℝ) = n := by simp
    rw [hd] at he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n)] using he
  let a := (volume.real A) ^ ((n : ℝ)⁻¹)
  let b := (volume.real B) ^ ((n : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos hApos _
  have hb : 0 < b := Real.rpow_pos_of_pos hBpos _
  have han : a ^ n = volume.real A := Real.rpow_inv_natCast_pow hApos.le hn0
  have hbn : b ^ n = volume.real B := Real.rpow_inv_natCast_pow hBpos.le hn0
  let S := (1 - t) * a + t * b
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hS : 0 < S := add_pos (mul_pos ht1 ha) (mul_pos ht.1 hb)
  let u := t * b / S
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (mul_pos ht.1 hb) hS
    · apply (div_lt_one hS).mpr
      change t * b < (1 - t) * a + t * b
      linarith [mul_pos ht1 ha]
  have h1u : 1 - u = (1 - t) * a / S := by
    change 1 - t * b / S = (1 - t) * a / S
    apply (eq_div_iff hS.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hS.ne']
    dsimp [S]
    ring
  have hvolA : volume.real (a⁻¹ • A) = 1 := by
    rw [hscale _ (inv_nonneg.mpr ha.le), inv_pow, ← han, inv_mul_cancel₀ (pow_ne_zero n ha.ne')]
  have hvolB : volume.real (b⁻¹ • B) = 1 := by
    rw [hscale _ (inv_nonneg.mpr hb.le), inv_pow, ← hbn, inv_mul_cancel₀ (pow_ne_zero n hb.ne')]
  have hcoefA : (1 - u) * a⁻¹ = S⁻¹ * (1 - t) := by
    rw [h1u]
    field_simp
  have hcoefB : u * b⁻¹ = S⁻¹ * t := by
    dsimp [u]
    field_simp
  have hcontain : (1 - u) • (a⁻¹ • A) + u • (b⁻¹ • B) ⊆ S⁻¹ • C := by
    rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, _, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(1 - t) • x + t • y,
      hsub (Set.mem_add.mpr ⟨_, Set.smul_mem_smul_set hx, _, Set.smul_mem_smul_set hy, rfl⟩), ?_⟩
    simp only [smul_add, smul_smul, hcoefA, hcoefB]
  have hmul := volumeReal_rpow_mul_rpow_le_of_smul_add_subset
    (hA.smul a⁻¹) (hB.smul b⁻¹) (hC.smul S⁻¹) hu hcontain
  have hunit : 1 ≤ volume.real (S⁻¹ • C) := by
    simpa only [hvolA, hvolB, Real.one_rpow, one_mul] using hmul
  rw [hscale _ (inv_nonneg.mpr hS.le), inv_pow] at hunit
  have hpow : S ^ n ≤ volume.real C := by
    have hh : 1 ≤ volume.real C / S ^ n := by
      simpa only [div_eq_mul_inv, mul_comm] using hunit
    simpa only [one_mul] using (le_div_iff₀ (pow_pos hS n)).mp hh
  have hroot := Real.rpow_le_rpow (pow_nonneg hS.le n) hpow
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  rw [Real.pow_rpow_inv_natCast hS.le hn0] at hroot
  simpa only [S, a, b, one_div] using hroot
)

/-- A translated nonnegative dilation contained in a compact set gives
the corresponding comparison of dimension-root volumes.
[Gar02, Corollary 5.3, homogeneity and degenerate-volume cases]

Neither set needs to be nonempty or convex, and the dilation factor may
be zero.

**Proof sketch.** Translation invariance and volume homogeneity identify
the volume of the affine image as `r ^ n * volume.real B`.
Containment and finiteness of the target volume bound this by
`volume.real C`. Take the nonnegative dimension root and use its
compatibility with products and natural powers. -/
theorem mul_volumeReal_rpow_le_of_affine_image_subset
    {n : ℕ} (hn : 1 ≤ n) {B C : Set (Fin n → ℝ)}
    (hB : IsCompact B) (hC : IsCompact C)
    (a : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hsub : Set.image (fun x : Fin n → ℝ => a + r • x) B ⊆ C) :
    r * (volume.real B) ^ (1 / (n : ℝ)) ≤
      (volume.real C) ^ (1 / (n : ℝ)) :=
  (by
  have hn0 : n ≠ 0 := by omega
  have himage : Set.image (fun x : Fin n → ℝ => a + r • x) B = a +ᵥ (r • B) := by
    change Set.image (fun x => a + r • x) B =
      Set.image (fun x => a + x) (Set.image (fun x => r • x) B)
    rw [Set.image_image]
  have hvol : volume.real (Set.image (fun x : Fin n → ℝ => a + r • x) B) =
      r ^ n * volume.real B := by
    change (volume (Set.image (fun x : Fin n → ℝ => a + r • x) B)).toReal = _
    rw [himage, measure_vadd volume a (r • B),
      Measure.addHaar_smul_of_nonneg volume hr]
    have hd : Module.finrank ℝ (Fin n → ℝ) = n := by simp
    rw [hd, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n), measureReal_def]
  have hvolume := measureReal_mono hsub hC.measure_ne_top (μ := volume)
  rw [hvol] at hvolume
  have hroot := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hr n) measureReal_nonneg)
    hvolume (inv_nonneg.mpr (Nat.cast_nonneg n))
  rw [Real.mul_rpow (pow_nonneg hr n) measureReal_nonneg,
    Real.pow_rpow_inv_natCast hr hn0] at hroot
  simpa only [one_div] using hroot
)

/-- The weighted sum of the dimension roots of the volumes of two
nonempty compact sets is bounded by the dimension root of the volume of
any compact set containing their weighted Minkowski sum.
[Gar02, Corollary 5.3, compact-set specialization]

No convexity or positive-volume assumption is required. The dimension is
positive, and both endpoint weights are allowed.

**Proof sketch.** At an endpoint the containing set contains the
corresponding input set. If an input volume is zero, a point of that
nonempty set gives a translate of the scaled other set inside the
containing set; volume monotonicity and homogeneity give the result.
Otherwise let the two volume roots be `a` and `b`, and let
`S = (1 - t) * a + t * b`. Dilate the inputs to volume one and choose
new weights `(1 - t) * a / S` and `t * b / S`. Their weighted sum is
contained in the dilation of the containing set by `1 / S`.
Multiplicative Brunn–Minkowski therefore gives volume at least one for
that dilation. Homogeneity and monotonicity of the positive dimension
root yield the claimed inequality. -/
theorem volumeReal_rpow_le_of_smul_add_subset
    {n : ℕ} (hn : 1 ≤ n) {A B C : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hsub : (1 - t) • A + t • B ⊆ C) :
    (1 - t) * (volume.real A) ^ (1 / (n : ℝ)) +
      t * (volume.real B) ^ (1 / (n : ℝ)) ≤
        (volume.real C) ^ (1 / (n : ℝ)) :=
  (by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have hleft : (1 - t) * (volume.real A) ^ (1 / (n : ℝ)) ≤
      (volume.real C) ^ (1 / (n : ℝ)) := by
    apply mul_volumeReal_rpow_le_of_affine_image_subset hn hA hC (t • b) (sub_nonneg.mpr ht.2)
    rintro _ ⟨x, hx, rfl⟩
    simpa only [add_comm] using hsub
      (Set.mem_add.mpr ⟨(1 - t) • x, Set.smul_mem_smul_set hx,
        t • b, Set.smul_mem_smul_set hb, rfl⟩)
  have hright : t * (volume.real B) ^ (1 / (n : ℝ)) ≤
      (volume.real C) ^ (1 / (n : ℝ)) := by
    apply mul_volumeReal_rpow_le_of_affine_image_subset hn hB hC ((1 - t) • a) ht.1
    rintro _ ⟨y, hy, rfl⟩
    exact hsub (Set.mem_add.mpr ⟨_, Set.smul_mem_smul_set ha, _, Set.smul_mem_smul_set hy, rfl⟩)
  by_cases ht0 : t = 0
  · simpa only [ht0, sub_zero, one_mul, zero_mul, add_zero] using hleft
  by_cases ht1 : t = 1
  · simpa only [ht1, sub_self, zero_mul, one_mul, zero_add] using hright
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : 1 / (n : ℝ) ≠ 0 := one_div_ne_zero hn0
  by_cases hAv : volume.real A = 0
  · simpa only [hAv, Real.zero_rpow hpow, mul_zero, zero_add] using hright
  by_cases hBv : volume.real B = 0
  · simpa only [hBv, Real.zero_rpow hpow, mul_zero, add_zero] using hleft
  exact volumeReal_rpow_le_of_smul_add_subset_of_pos hn hA hB hC
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hAv))
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hBv))
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩ hsub
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
