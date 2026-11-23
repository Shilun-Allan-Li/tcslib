/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Basic
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Remez
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exponential-weighted polynomial estimates

## Main definitions

No new definitions.

## Main results

* `abs_eval_le_of_bound_on_set_of_exp_mass`: bounds a polynomial on the
  nonnegative half-line using its bound on a set of positive exponential mass.
* `lintegral_sq_eval_exp_neg_le_of_bound_on_set_of_exp_mass`: integrates the
  squared envelope with an explicit factorial bound.
* `exp_mass_smallBall_le_of_le_lintegral_sq`: a square-integral lower bound
  gives a small-ball estimate with constant linear in the degree.

* `abs_eval_le_of_bound_on_set_of_exp_mass_all_real`: a weighted Remez
  envelope from half-line mass controlling evaluation on the whole line.

## References

* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn, Mathematical Research Letters
  8 (2001), 233–248, §4.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- A polynomial bounded by `M` on a measurable subset of the
nonnegative half-line with exponential mass at least `m > 0` satisfies
`|p(x)| ≤ M * (16 * exp 2 * (1 + |x|) / m) ^ d` at every real point.

This is an explicit, coarse-constant exponential-weighted Remez bound,
following the method in [CW01, §4]. The pointwise whole-line envelope
and the displayed constant are the formulation used here.

**Proof sketch.** The cumulative-volume estimate supplies a nonnegative
parameter `t` for which the original set intersected with `(-∞,t]`
has volume greater than `(m / 4) * (1 + t)`. This intersection lies
in `[0,t]`, hence also in `[min x 0, max x t]`, an interval containing
the arbitrary evaluation point `x`. Apply interval Remez there.
The interval length is at most `|x| + t`, and hence at most
`(1 + |x|) * (1 + t)`. The selected volume lower bound then gives
the stated factor, without any sign assumption on `x`. -/
theorem abs_eval_le_of_bound_on_set_of_exp_mass_all_real
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d)
    (E : Set ℝ) (hE : MeasurableSet E) (hnonneg : E ⊆ Ici 0)
    (M m : ℝ) (hM : 0 ≤ M) (hm : 0 < m)
    (hvalue : ∀ y ∈ E, |p.eval y| ≤ M)
    (hmass :
      ENNReal.ofReal m ≤
        ∫⁻ y in E, ENNReal.ofReal (Real.exp (-y)) ∂volume)
    (x : ℝ) :
    |p.eval x| ≤ M * (16 * Real.exp 2 * (1 + |x|) / m) ^ d :=
  (by
  classical
  obtain ⟨t, ht, htvol⟩ : ∃ t : ℝ, 0 ≤ t ∧
      ENNReal.ofReal (m / 4) * ENNReal.ofReal (1 + t) < volume (E ∩ Iic t) := by
    by_contra! h
    have hbound := lintegral_exp_neg_le_of_volume_initial_le E hE hnonneg
      (ENNReal.ofReal (m / 4)) h
    have heq : 2 * ENNReal.ofReal (m / 4) = ENNReal.ofReal (m / 2) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [heq] at hbound
    have hlt : ENNReal.ofReal (m / 2) < ENNReal.ofReal m :=
      (ENNReal.ofReal_lt_ofReal_iff hm).mpr (by linarith)
    exact (not_lt_of_ge (hmass.trans hbound)) hlt
  let A : Set ℝ := E ∩ Iic t
  have hA : A ⊆ Icc (0 : ℝ) t := by
    intro y hy
    exact ⟨hnonneg hy.1, hy.2⟩
  have hAfin : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hA)
  have hstrict : (m / 4) * (1 + t) < volume.real A := by
    have heq : ENNReal.ofReal (volume.real A) = volume A := by
      rw [measureReal_def, ENNReal.ofReal_toReal hAfin]
    change ENNReal.ofReal (m / 4) * ENNReal.ofReal (1 + t) < volume A at htvol
    rw [← ENNReal.ofReal_mul (by positivity), ← heq] at htvol
    exact ENNReal.ofReal_lt_ofReal_iff'.mp htvol |>.1
  have hApos : 0 < volume.real A := lt_trans (by positivity) hstrict
  have hAinterval : A ⊆ Icc (min x 0) (max x t) := by
    intro y hy
    exact ⟨(min_le_right _ _).trans (hA hy).1, (hA hy).2.trans (le_max_right _ _)⟩
  have hwidth : 0 ≤ max x t - min x 0 :=
    sub_nonneg.mpr ((min_le_left _ _).trans (le_max_left _ _))
  have hremez := abs_eval_le_of_bound_on_set p d hp A (min x 0) (max x t) M
    (sub_nonneg.mp hwidth) hAinterval hApos hM
    (fun y hy => hvalue y hy.1) x ⟨min_le_left _ _, le_max_left _ _⟩
  have hlength : max x t - min x 0 ≤ |x| + t := by
    by_cases hx : 0 ≤ x
    · rw [min_eq_right hx, abs_of_nonneg hx, sub_zero]
      exact max_le (by linarith) (by linarith)
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [min_eq_left hx', max_eq_right (hx'.trans ht), abs_of_nonpos hx']
      linarith
  have hmax : max x t - min x 0 ≤ (1 + |x|) * (1 + t) := by
    nlinarith [abs_nonneg x]
  have hratio : 4 * Real.exp 2 * (max x t - min x 0) / volume.real A ≤
      16 * Real.exp 2 * (1 + |x|) / m := by
    apply (div_le_div_iff₀ hApos hm).mpr
    have he := Real.exp_pos 2
    nlinarith [
      mul_le_mul_of_nonneg_left hmax
        (show 0 ≤ 4 * Real.exp 2 * m by positivity),
      mul_le_mul_of_nonneg_left hstrict.le
        (show 0 ≤ 16 * Real.exp 2 * (1 + |x|) by positivity)]
  exact hremez.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg (mul_nonneg (by positivity) hwidth) hApos.le)
      hratio d) hM)
)

/-- A polynomial bounded by `M` on a measurable subset of the nonnegative
half-line with exponential mass at least `m > 0` is bounded at every
nonnegative `x` by `M * (16 * exp 2 * (1 + x) / m) ^ d`.

This is an explicit, coarse-constant exponential-weighted Remez bound,
following the Remez method used in [CW01, §4]; the displayed constant and
pointwise envelope are the formulation used here.

**Proof sketch.** Apply the whole-line weighted Remez envelope and use
`|x| = x` at the nonnegative evaluation point. -/
theorem abs_eval_le_of_bound_on_set_of_exp_mass
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d)
    (E : Set ℝ) (hE : MeasurableSet E) (hnonneg : E ⊆ Ici 0)
    (M m : ℝ) (hM : 0 ≤ M) (hm : 0 < m)
    (hvalue : ∀ y ∈ E, |p.eval y| ≤ M)
    (hmass :
      ENNReal.ofReal m ≤
        ∫⁻ y in E, ENNReal.ofReal (Real.exp (-y)) ∂volume)
    (x : ℝ) (hx : 0 ≤ x) :
    |p.eval x| ≤ M * (16 * Real.exp 2 * (1 + x) / m) ^ d :=
  (by
  simpa only [abs_of_nonneg hx] using
    abs_eval_le_of_bound_on_set_of_exp_mass_all_real
      p d hp E hE hnonneg M m hM hm hvalue hmass x
)



/-- A polynomial of degree at most `d`, bounded by `M` on a measurable subset
of the nonnegative half-line with exponential mass at least `m > 0`, has
exponentially weighted square integral at most
`M ^ 2 * (16 * exp 2 / m) ^ (2 * d) * exp 1 * (2 * d)!`.

This is technical integration glue combining the exponential-weighted Remez
envelope with the shifted exponential moment bound.

**Proof sketch.** Square the pointwise envelope, whose two sides are
nonnegative, and separate its constant factor from `(1 + x) ^ (2 * d)`.
Multiply by the nonnegative exponential density and integrate over the
nonnegative half-line. Factor out the constant and apply the shifted
exponential moment bound at exponent `2 * d`. -/
theorem lintegral_sq_eval_exp_neg_le_of_bound_on_set_of_exp_mass
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d)
    (E : Set ℝ) (hE : MeasurableSet E) (hnonneg : E ⊆ Ici 0)
    (M m : ℝ) (hM : 0 ≤ M) (hm : 0 < m)
    (hvalue : ∀ y ∈ E, |p.eval y| ≤ M)
    (hmass :
      ENNReal.ofReal m ≤
        ∫⁻ y in E, ENNReal.ofReal (Real.exp (-y)) ∂volume) :
    (∫⁻ x in Ici (0 : ℝ),
      ENNReal.ofReal ((p.eval x) ^ 2) *
        ENNReal.ofReal (Real.exp (-x)) ∂volume) ≤
      ENNReal.ofReal
        (M ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d) *
          Real.exp 1 * ((2 * d).factorial : ℝ)) :=
  (by
  let C : ℝ := M ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hsquare (x : ℝ) (hx : 0 ≤ x) :
      (p.eval x) ^ 2 ≤ C * (1 + x) ^ (2 * d) := by
    have hbound := abs_eval_le_of_bound_on_set_of_exp_mass
      p d hp E hE hnonneg M m hM hm hvalue hmass x hx
    have heq : 16 * Real.exp 2 * (1 + x) / m =
        (16 * Real.exp 2 / m) * (1 + x) := by ring
    rw [heq] at hbound
    have h := pow_le_pow_left₀ (abs_nonneg (p.eval x)) hbound 2
    dsimp only [C]
    simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm d 2, mul_assoc] using h
  calc
    _ ≤ ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal C *
        (ENNReal.ofReal ((1 + x) ^ (2 * d)) *
          ENNReal.ofReal (Real.exp (-x))) := by
      apply setLIntegral_mono' measurableSet_Ici
      intro x hx
      calc
        _ ≤ ENNReal.ofReal (C * (1 + x) ^ (2 * d)) *
            ENNReal.ofReal (Real.exp (-x)) :=
          mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hsquare x hx)) _
        _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]
    _ = ENNReal.ofReal C * ∫⁻ x in Ici (0 : ℝ),
        ENNReal.ofReal ((1 + x) ^ (2 * d)) *
          ENNReal.ofReal (Real.exp (-x)) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ ENNReal.ofReal C *
        ENNReal.ofReal (Real.exp 1 * ((2 * d).factorial : ℝ)) :=
      mul_le_mul_left' (lintegral_one_add_pow_mul_exp_neg_le (2 * d)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      dsimp only [C]
      ring
)


/-- If a polynomial of degree at most `d ≥ 1` has exponentially weighted
square integral at least `a ^ 2`, where `a > 0`, then the exponential mass
of its `ε`-sublevel set on the nonnegative half-line is at most
`32 * exp 3 * d * (ε / a) ^ (1 / d)` for every `ε > 0`.

This is an explicit one-dimensional exponential-weighted small-ball bound
following the Remez method in [CW01, §4]. The lower-bound normalization and
coarse explicit constant are the formulation used here.

**Proof sketch.** Let `m` be the real value of the exponential mass of the
sublevel set. The case `m = 0` is immediate. Otherwise its nonnegative-real
embedding is bounded by that mass, so apply the weighted square-integral
bound with `M = ε` and mass lower bound `m`. Combined with the assumed
lower bound, this gives
`a ^ 2 ≤ ε ^ 2 * (16 * exp 2 / m) ^ (2 * d) * exp 1 * (2 * d)!`.
Apply the shared scalar factorial and root comparison to this bound. -/
theorem exp_mass_smallBall_le_of_le_lintegral_sq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a : ℝ) (ha : 0 < a)
    (hlower :
      ENNReal.ofReal (a ^ 2) ≤
        ∫⁻ x in Ici (0 : ℝ),
          ENNReal.ofReal ((p.eval x) ^ 2) *
            ENNReal.ofReal (Real.exp (-x)) ∂volume)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | 0 ≤ x ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (-x)) ∂volume).toReal ≤
      32 * Real.exp 3 * (d : ℝ) * (ε / a) ^ (1 / (d : ℝ)) :=
  (by
  let E : Set ℝ := {x : ℝ | 0 ≤ x ∧ |p.eval x| ≤ ε}
  let m : ℝ := (∫⁻ x in E, ENNReal.ofReal (Real.exp (-x))).toReal
  change m ≤ _
  by_cases hm : 0 < m
  · have hE : MeasurableSet E := by
      exact (measurableSet_le measurable_const measurable_id).inter
        (measurableSet_le p.continuous.abs.measurable measurable_const)
    have hupper := lintegral_sq_eval_exp_neg_le_of_bound_on_set_of_exp_mass
      p d hp E hE (fun x hx => hx.1) ε m hε.le hm
      (fun x hx => hx.2) ENNReal.ofReal_toReal_le
    have hraw : a ^ 2 ≤ ε ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d) *
        Real.exp 1 * ((2 * d).factorial : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlower.trans hupper)
    exact le_exp_mul_degree_mul_rpow_of_sq_le_factorial_bound
      d hd a ε m ha hε hm hraw
  · exact (le_of_not_gt hm).trans (by positivity)
)


end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
