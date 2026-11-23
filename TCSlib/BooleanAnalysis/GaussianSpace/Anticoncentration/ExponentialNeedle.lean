/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.WeightedRemez

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial small-ball bounds on finite exponential intervals

## Main definitions

No new definitions.

## Main results

* `truncated_exp_smallBall_le_of_lintegral_sq_eq_of_le_one`: bounds the
  normalized exponential mass of a polynomial sublevel set on `[0, L]`
  when `0 < L ≤ 1`.
* `truncated_exp_smallBall_le_of_lintegral_sq_eq_of_one_le`: handles `1 ≤ L`.
* `truncated_exp_smallBall_le_of_lintegral_sq_eq`: combines the cases for every `L > 0`.

## References

* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn, Mathematical Research Letters
  8 (2001), 233–248, §4.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- On an interval `[0, L]` with `0 < L ≤ 1`, a polynomial of degree at most
`d ≥ 1`, whose square integral against the normalized exponential density
is one, has normalized exponential mass at most
`4 * exp 3 * ε ^ (1 / d)` where its absolute value is at most `ε > 0`.

This is a short-interval consequence of the Remez method in [CW01, §4].
The exponential normalization and explicit constant are the formulation
used here.

**Proof sketch.** Write `Z = 1 - exp (-L)` and let `r` be the unnormalized
exponential mass of the sublevel set. The case `r = 0` is immediate.
Otherwise the sublevel set has positive Lebesgue volume at least `r`,
because the exponential density is at most one. Interval Remez therefore
bounds the polynomial throughout `[0, L]` by
`ε * (4 * exp 2 * L / r) ^ d`. Integrate the square of this uniform bound
against the exponential density. Its interval mass and the assumed square
integral both equal `Z > 0`, so cancellation and comparison of positive
`2 * d`-th powers give `r ≤ 4 * exp 2 * L * ε ^ (1 / d)`.
Finally, the density on this interval is at least `exp (-1)`, hence
`Z ≥ L / exp 1`. Divide by `Z` to obtain the claimed estimate. -/
theorem truncated_exp_smallBall_le_of_lintegral_sq_eq_of_le_one
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (L : ℝ) (hL : 0 < L) (hLone : L ≤ 1)
    (hnorm :
      (∫⁻ x in Icc (0 : ℝ) L,
        ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (-x)) ∂volume) =
        ENNReal.ofReal (1 - Real.exp (-L)))
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc (0 : ℝ) L ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (-x)) ∂volume).toReal /
        (1 - Real.exp (-L)) ≤
      4 * Real.exp 3 * ε ^ (1 / (d : ℝ)) :=
  (by
  let E : Set ℝ := {x : ℝ | x ∈ Icc (0 : ℝ) L ∧ |p.eval x| ≤ ε}
  let r : ℝ := (∫⁻ x in E, ENNReal.ofReal (Real.exp (-x))).toReal
  let A : ℝ := 4 * Real.exp 2 * L
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hZ : 0 < 1 - Real.exp (-L) := by
    have := Real.exp_lt_one_iff.mpr (show -L < 0 by linarith)
    linarith
  have hZlower : L / Real.exp 1 ≤ 1 - Real.exp (-L) := by
    have h : ENNReal.ofReal (Real.exp (-1) * L) ≤
        ENNReal.ofReal (1 - Real.exp (-L)) := by
      calc
        _ = ∫⁻ x in Icc (0 : ℝ) L, ENNReal.ofReal (Real.exp (-1)) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ ≤ ∫⁻ x in Icc (0 : ℝ) L, ENNReal.ofReal (Real.exp (-x)) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro x hx
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hx.2]))
        _ = _ := lintegral_exp_neg_Icc L hL.le
    have hh := (ENNReal.ofReal_le_ofReal_iff hZ.le).mp h
    simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using hh
  change r / (1 - Real.exp (-L)) ≤ _
  by_cases hr : 0 < r
  · have hE : MeasurableSet E := measurableSet_Icc.inter
      (measurableSet_le p.continuous.abs.measurable measurable_const)
    have hEsub : E ⊆ Icc (0 : ℝ) L := fun x hx => hx.1
    have hEfin : volume E ≠ ⊤ :=
      ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hEsub)
    have hrvol : r ≤ volume.real E := by
      apply ENNReal.toReal_mono hEfin
      calc
        _ ≤ ∫⁻ x in E, (1 : ENNReal) := by
          apply setLIntegral_mono' hE
          intro x hx
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.1.1))
        _ = _ := by simp
    have hV : 0 < volume.real E := lt_of_lt_of_le hr hrvol
    have hbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) L) :
        |p.eval x| ≤ ε * (A / r) ^ d := by
      have hb := abs_eval_le_of_bound_on_set p d hp E 0 L ε hL.le
        hEsub hV hε.le (fun y hy => hy.2) x hx
      have hratio : 4 * Real.exp 2 * (L - 0) / volume.real E ≤ A / r := by
        rw [sub_zero]
        exact div_le_div_of_nonneg_left hA hr hrvol
      exact hb.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hL.le)) hV.le)
          hratio d) hε.le)
    have hB : 1 ≤ ε * (A / r) ^ d :=
      one_le_of_bound_of_lintegral_sq_exp_neg_eq (fun x => p.eval x) L hL
        (ε * (A / r) ^ d) (by positivity) hbound hnorm
    have hrbound : r ≤ A * ε ^ (1 / (d : ℝ)) := by
      have hd0 : d ≠ 0 := by omega
      have hroot : (ε ^ (1 / (d : ℝ))) ^ d = ε := by
        rw [one_div, Real.rpow_inv_natCast_pow hε.le hd0]
      apply (pow_le_pow_iff_left₀ hr.le
        (by positivity : 0 ≤ A * ε ^ (1 / (d : ℝ))) hd0).mp
      rw [mul_pow, hroot]
      have h : 1 * r ^ d ≤ A ^ d * ε := (le_div_iff₀ (pow_pos hr d)).mp (by
        calc
          _ ≤ ε * (A / r) ^ d := hB
          _ = _ := by rw [div_pow]; ring)
      simpa only [one_mul] using h
    apply (div_le_iff₀ hZ).mpr
    calc
      _ ≤ A * ε ^ (1 / (d : ℝ)) := hrbound
      _ = (4 * Real.exp 3 * ε ^ (1 / (d : ℝ))) * (L / Real.exp 1) := by
        dsimp only [A]
        rw [show Real.exp 3 = Real.exp 2 * Real.exp 1 by
          rw [← Real.exp_add]; norm_num]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hZlower (by positivity)
  · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hZ.le).trans (by positivity)
)


/-- On an interval `[0, L]` with `L ≥ 1`, a polynomial of degree at most
`d ≥ 1`, whose square integral against the normalized exponential density
is one, has normalized exponential mass at most
`128 * exp 3 * d * ε ^ (1 / d)` where its absolute value is at most `ε > 0`.

This is a long-interval consequence of the exponential-weighted Remez
method in [CW01, §4]. The interval normalization and coarse explicit
constant are the formulation used here.

**Proof sketch.** Write `Z = 1 - exp (-L)`. Since `L ≥ 1`, the inequality
`exp 1 ≥ 2` gives `1 / 2 ≤ Z ≤ 1`. The full half-line square integral is
at least its integral on `[0, L]`, which is `Z ≥ (1 / 2) ^ 2`. Apply the
half-line small-ball bound with `a = 1 / 2`. The truncated sublevel mass
is at most the full half-line sublevel mass. Moreover `0 < 1 / d ≤ 1`,
so `(ε / (1 / 2)) ^ (1 / d) ≤ 2 * ε ^ (1 / d)`.
Finally divide by `Z ≥ 1 / 2`, losing another factor two. -/
theorem truncated_exp_smallBall_le_of_lintegral_sq_eq_of_one_le
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (L : ℝ) (hL : 1 ≤ L)
    (hnorm :
      (∫⁻ x in Icc (0 : ℝ) L,
        ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (-x)) ∂volume) =
        ENNReal.ofReal (1 - Real.exp (-L)))
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc (0 : ℝ) L ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (-x)) ∂volume).toReal /
        (1 - Real.exp (-L)) ≤
      128 * Real.exp 3 * (d : ℝ) * ε ^ (1 / (d : ℝ)) :=
  (by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdreal
  have hZ : (1 : ℝ) / 2 ≤ 1 - Real.exp (-L) := by
    have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hneg : Real.exp (-L) ≤ (1 : ℝ) / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hexp
    linarith
  have hZpos : 0 < 1 - Real.exp (-L) := lt_of_lt_of_le (by norm_num) hZ
  have hlower :
      ENNReal.ofReal (((1 : ℝ) / 2) ^ 2) ≤
        ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (-x)) := by
    calc
      _ ≤ ENNReal.ofReal (1 - Real.exp (-L)) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ∫⁻ x in Icc (0 : ℝ) L, ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (-x)) := hnorm.symm
      _ ≤ _ := lintegral_mono_set (fun x hx => hx.1)
  have hsmall := exp_mass_smallBall_le_of_le_lintegral_sq p d hp hd
    ((1 : ℝ) / 2) (by norm_num) hlower ε hε
  have htotal : (∫⁻ x in Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-x))) = 1 :=
    lintegral_exp_neg_Ici_eq_one
  have hfin : (∫⁻ x in {x : ℝ | 0 ≤ x ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (-x))) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (1 : ENNReal) ≠ ⊤ by simp)
    calc
      _ ≤ ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-x)) :=
        lintegral_mono_set (fun x hx => hx.1)
      _ = _ := htotal
  have hmass :
      (∫⁻ x in {x : ℝ | x ∈ Icc (0 : ℝ) L ∧ |p.eval x| ≤ ε},
        ENNReal.ofReal (Real.exp (-x))).toReal ≤
      (∫⁻ x in {x : ℝ | 0 ≤ x ∧ |p.eval x| ≤ ε},
        ENNReal.ofReal (Real.exp (-x))).toReal :=
    ENNReal.toReal_mono hfin (lintegral_mono_set (fun x hx => ⟨hx.1.1, hx.2⟩))
  have hrootle : 1 / (d : ℝ) ≤ 1 := (div_le_one hdpos).mpr hdreal
  have hrpow : (ε / ((1 : ℝ) / 2)) ^ (1 / (d : ℝ)) ≤
      2 * ε ^ (1 / (d : ℝ)) := by
    rw [show ε / ((1 : ℝ) / 2) = 2 * ε by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num) hrootle) (by positivity)
  apply (div_le_iff₀ hZpos).mpr
  calc
    _ ≤ 32 * Real.exp 3 * (d : ℝ) *
        (ε / ((1 : ℝ) / 2)) ^ (1 / (d : ℝ)) := hmass.trans hsmall
    _ ≤ 32 * Real.exp 3 * (d : ℝ) * (2 * ε ^ (1 / (d : ℝ))) :=
      mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = (128 * Real.exp 3 * (d : ℝ) * ε ^ (1 / (d : ℝ))) *
        ((1 : ℝ) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by positivity)
)



/-- Let `L > 0`. If a polynomial of degree at most `d ≥ 1` has square
integral one against the normalized exponential density on `[0, L]`, then
its `ε`-sublevel set has normalized exponential mass at most
`128 * exp 3 * d * ε ^ (1 / d)` for every `ε > 0`.

This is an explicit finite-interval exponential-weighted small-ball bound
following the Remez method in [CW01, §4]. The interval normalization and
coarse explicit constant are the formulation used here.

**Proof sketch.** Split according to whether `L ≤ 1` or `1 ≤ L`.
In the first case, apply the short-interval estimate and absorb its constant
`4 * exp 3` into `128 * exp 3 * d` using `d ≥ 1`.
In the second case, apply the long-interval estimate directly. -/
theorem truncated_exp_smallBall_le_of_lintegral_sq_eq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (L : ℝ) (hL : 0 < L)
    (hnorm :
      (∫⁻ x in Icc (0 : ℝ) L,
        ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (-x)) ∂volume) =
        ENNReal.ofReal (1 - Real.exp (-L)))
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc (0 : ℝ) L ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (-x)) ∂volume).toReal /
        (1 - Real.exp (-L)) ≤
      128 * Real.exp 3 * (d : ℝ) * ε ^ (1 / (d : ℝ)) :=
  (by
  rcases le_total L 1 with hshort | hlong
  · apply (truncated_exp_smallBall_le_of_lintegral_sq_eq_of_le_one
      p d hp hd L hL hshort hnorm ε hε).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Real.exp_pos 3]
  · exact truncated_exp_smallBall_le_of_lintegral_sq_eq_of_one_le
      p d hp hd L hlong hnorm ε hε
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
