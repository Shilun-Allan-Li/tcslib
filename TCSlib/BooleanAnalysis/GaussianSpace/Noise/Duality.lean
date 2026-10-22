/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded tests for converse Hölder estimates

## Main definitions

The existing real Lp seminorms and Bochner integrals are reused.

## Main results

* `eLpNorm_le_of_bounded_pairing`: nonnegative bounded functions dominated by
  an input inherit the norm bound supplied by its bounded Hölder tests.
* `memLp_and_eLpNorm_le_of_bounded_pairing`: bounded Hölder tests imply Lq
  membership and the corresponding norm bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Theorem 11.23. The bounded tests are
  technical duality glue for the Lp-to-Lq formulation.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

/-- If all bounded Hölder tests against an integrable real input have operator
bound `C`, every bounded nonnegative function dominated by its absolute value
has Lq seminorm at most `C`, when `q > 1`.

**Proof sketch.** Test against the input's sign times the dominated function
raised to `q-1`. Its dual norm is the `q`th moment raised to `(q-1)/q`, while
the pairing dominates that moment. Cancel the positive power of the moment;
the zero-moment case is immediate. -/
lemma eLpNorm_le_of_bounded_pairing {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (q : ℝ) (hq : 1 < q)
    {u : α → ℝ} (hu : Integrable u μ) (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ g : α → ℝ, MemLp g ⊤ μ →
      |∫ x, u x * g x ∂μ| ≤ C * (eLpNorm g (ENNReal.ofReal (q / (q - 1))) μ).toReal)
    {v : α → ℝ} (hv : AEStronglyMeasurable v μ)
    (hv0 : 0 ≤ᵐ[μ] v) (hvu : ∀ᵐ x ∂μ, v x ≤ |u x|)
    (B : ℝ) (hvB : ∀ᵐ x ∂μ, v x ≤ B) :
    eLpNorm v (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  let r := q / (q - 1)
  have hr0 : 0 < r := div_pos hq0 (sub_pos.mpr hq)
  let s : Set α := {x | 0 ≤ u x}
  let w : α → ℝ := fun x => v x ^ (q - 1)
  let g : α → ℝ := s.indicator w - sᶜ.indicator w
  have hs : NullMeasurableSet s μ :=
    nullMeasurableSet_le aemeasurable_const hu.aestronglyMeasurable.aemeasurable
  have hw : AEStronglyMeasurable w μ := (hv.aemeasurable.pow_const _).aestronglyMeasurable
  have hg : AEStronglyMeasurable g μ := (hw.indicator₀ hs).sub (hw.indicator₀ hs.compl)
  have hgabs : ∀ᵐ x ∂μ, |g x| = v x ^ (q - 1) := by
    filter_upwards [hv0] with x hx
    by_cases hux : 0 ≤ u x <;>
      simp [g, s, w, hux, abs_of_nonneg (Real.rpow_nonneg hx _)]
  have hgprod (x : α) : u x * g x = |u x| * v x ^ (q - 1) := by
    by_cases hux : 0 ≤ u x
    · simp [g, s, w, hux, abs_of_nonneg hux]
    · simp [g, s, w, hux, abs_of_neg (lt_of_not_ge hux)]
  have hgtop : MemLp g ⊤ μ := by
    apply MemLp.of_bound hg (B ^ (q - 1))
    filter_upwards [hv0, hvB, hgabs] with x hx hxB hxg
    rw [Real.norm_eq_abs, hxg]
    exact Real.rpow_le_rpow hx hxB (sub_nonneg.mpr hq.le)
  have hvp : MemLp v (ENNReal.ofReal q) μ := by
    apply MemLp.of_bound hv B
    filter_upwards [hv0, hvB] with x hx hxB
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hxB
  let A := ∫ x, v x ^ q ∂μ
  have hA0 : 0 ≤ A := integral_nonneg_of_ae (hv0.mono fun x hx => Real.rpow_nonneg hx _)
  have hAint : Integrable (fun x => v x ^ q) μ := by
    apply (hvp.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top).congr
    filter_upwards [hv0] with x hx
    simp only [ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs, abs_of_nonneg hx]
  -- The signed power has the dual moment dictated by Hölder's equality case.
  have hmoment : (∫ x, ‖g x‖ ^ r ∂μ) = A := by
    apply integral_congr_ae
    filter_upwards [hv0, hgabs] with x hx hxg
    rw [Real.norm_eq_abs, hxg, ← Real.rpow_mul hx]
    congr 1
    dsimp [r]
    field_simp [show q - 1 ≠ 0 by linarith]
  have hgnorm : eLpNorm g (ENNReal.ofReal r) μ = ENNReal.ofReal (A ^ r⁻¹) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top
      (hgtop.mono_exponent le_top), ENNReal.toReal_ofReal hr0.le, hmoment]
  have hpair : Integrable (fun x => u x * g x) μ := hu.mul_of_top_left hgtop
  have hA : A ≤ C * A ^ r⁻¹ := by
    calc
      A ≤ ∫ x, u x * g x ∂μ := by
        apply integral_mono_ae hAint hpair
        filter_upwards [hv0, hvu] with x hx hxu
        rw [hgprod]
        calc
          v x ^ q = v x * v x ^ (q - 1) := by
            conv_lhs =>
              rw [show q = (1 : ℝ) + (q - 1) by ring,
                Real.rpow_add' hx (by linarith), Real.rpow_one]
          _ ≤ |u x| * v x ^ (q - 1) :=
            mul_le_mul_of_nonneg_right hxu (Real.rpow_nonneg hx _)
      _ ≤ |∫ x, u x * g x ∂μ| := le_abs_self _
      _ ≤ C * (eLpNorm g (ENNReal.ofReal r) μ).toReal := htest g hgtop
      _ = C * A ^ r⁻¹ := by
        rw [hgnorm, ENNReal.toReal_ofReal (Real.rpow_nonneg hA0 _)]
  -- Cancel the positive complementary power; treat a zero moment separately.
  have hroot : A ^ q⁻¹ ≤ C := by
    by_cases hAz : A = 0
    · simpa only [hAz, Real.zero_rpow (inv_ne_zero hq0.ne')] using hC
    · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
      have hsplit : A = A ^ q⁻¹ * A ^ r⁻¹ := by
        rw [← Real.rpow_add hApos]
        conv_lhs => rw [← Real.rpow_one A]
        congr 1
        dsimp [r]
        field_simp [hq0.ne', show q - 1 ≠ 0 by linarith]
        ring
      apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hApos r⁻¹)).mp
      rwa [← hsplit]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top hvp,
    ENNReal.toReal_ofReal hq0.le]
  apply ENNReal.ofReal_le_ofReal
  convert hroot using 2
  apply integral_congr_ae
  filter_upwards [hv0] with x hx
  simp only [Real.norm_eq_abs, abs_of_nonneg hx]

/-- An integrable real function whose pairings against all bounded functions
satisfy Hölder's estimate with bound `C` belongs to Lq with norm at most `C`.

**Proof sketch.** Clip the absolute value at each natural number and apply the
bounded dominated-function estimate. These clips converge pointwise to the
absolute value, so lower semicontinuity of the Lq seminorm gives the same bound
for the input. The finite bound also supplies Lq membership. -/
lemma memLp_and_eLpNorm_le_of_bounded_pairing {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (q : ℝ) (hq : 1 < q)
    {u : α → ℝ} (hu : Integrable u μ) (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ g : α → ℝ, MemLp g ⊤ μ →
      |∫ x, u x * g x ∂μ| ≤ C * (eLpNorm g (ENNReal.ofReal (q / (q - 1))) μ).toReal) :
    MemLp u (ENNReal.ofReal q) μ ∧
      eLpNorm u (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
  let v : ℕ → α → ℝ := fun m x => min ‖u x‖ (m : ℝ)
  have hv (m : ℕ) : AEStronglyMeasurable (v m) μ :=
    (hu.aestronglyMeasurable.norm.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hbound (m : ℕ) : eLpNorm (v m) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
    apply eLpNorm_le_of_bounded_pairing μ q hq hu C hC htest (hv m)
      (Filter.Eventually.of_forall fun x => le_min (norm_nonneg _) (Nat.cast_nonneg _))
      (Filter.Eventually.of_forall fun x => ?_) (m : ℝ)
      (Filter.Eventually.of_forall fun x => min_le_right _ _)
    simpa only [Real.norm_eq_abs] using min_le_left ‖u x‖ (m : ℝ)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun m => v m x) atTop (𝓝 ‖u x‖) := by
    apply Filter.Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge ‖u x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with m hm
    exact (min_eq_left (hN.trans (Nat.cast_le.mpr hm))).symm
  have hnorm : eLpNorm u (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
    rw [← eLpNorm_norm u]
    exact (Lp.eLpNorm_lim_le_liminf_eLpNorm hv _ hlim).trans
      (liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbound))
  exact ⟨⟨hu.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩

end BooleanAnalysis.GaussianSpace
