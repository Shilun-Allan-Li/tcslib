/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.ExponentialNeedle
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.UniformNeedle

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial small-ball bounds on affine exponential intervals

## Main definitions

No new definitions.

## Main results

* `decreasing_exp_smallBall_le_of_lintegral_sq_eq`: normalized small-ball
  bounds for decreasing exponential densities on any nondegenerate interval.

* `increasing_exp_smallBall_le_of_lintegral_sq_eq`: the reflected increasing case.
* `exp_smallBall_le_of_lintegral_sq_eq`: every real exponential slope, including zero.

* `exp_smallBall_pow_mul_lintegral_sq_le`: homogeneous moment-and-mass form for localization.

## References

* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn, Mathematical Research Letters
  8 (2001), 233–248, §4.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- On a nondegenerate interval `[a, b]`, a polynomial of degree at most
`d ≥ 1`, whose square integral against the normalized density `exp (-r * x)`
is one, has normalized sublevel mass at most
`128 * exp 3 * d * ε ^ (1 / d)` for every `r > 0` and `ε > 0`.

This is an affine reformulation of the finite-interval exponential bound
following [CW01, §4], with the same coarse explicit constant.

**Proof sketch.** Substitute `u = r * (x - a)`, set
`L = r * (b - a) > 0`, and compose the polynomial with `u ↦ u / r + a`.
Its degree remains at most `d`. The weighted substitution identity gives
the common positive factor `exp (-r * a) / r` for the square integral,
the density mass, and the sublevel mass. Cancel this factor in the
normalization and apply the normalized exponential bound on `[0, L]`.
It also cancels from the quotient of the two real masses, giving the
stated estimate. -/
theorem decreasing_exp_smallBall_le_of_lintegral_sq_eq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a b r : ℝ) (hab : a < b) (hr : 0 < r)
    (hnorm :
      (∫⁻ x in Icc a b,
        ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (-r * x)) ∂volume) =
        ∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (-r * x)) ∂volume)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (-r * x)) ∂volume).toReal /
        (∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (-r * x)) ∂volume).toReal ≤
      128 * Real.exp 3 * (d : ℝ) * ε ^ (1 / (d : ℝ)) :=
  (by
  let L : ℝ := r * (b - a)
  let c : ℝ := Real.exp (-r * a) / r
  let q : Polynomial ℝ := p.comp (Polynomial.C r⁻¹ * Polynomial.X + Polynomial.C a)
  have hL : 0 < L := mul_pos hr (sub_pos.mpr hab)
  have hc : 0 < c := div_pos (Real.exp_pos _) hr
  have heval (u : ℝ) : q.eval u = p.eval (u / r + a) := by
    dsimp only [q]
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    ring
  have hq : q.natDegree ≤ d := by
    have hlin : (Polynomial.C r⁻¹ * Polynomial.X + Polynomial.C a).natDegree ≤ 1 := by
      apply (Polynomial.natDegree_add_le _ _).trans
      rw [Polynomial.natDegree_C_mul_X _ (inv_ne_zero hr.ne'), Polynomial.natDegree_C]
      norm_num
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul hp hlin).trans (by omega))
  have hmass :
      (∫⁻ x in Icc a b, ENNReal.ofReal (Real.exp (-r * x))) =
        ENNReal.ofReal c * ENNReal.ofReal (1 - Real.exp (-L)) := by
    have h := lintegral_mul_exp_neg_mul_Icc_eq (fun _ => 1) measurable_const
      a b r hab.le hr
    simpa only [one_mul, lintegral_exp_neg_Icc (r * (b - a)) hL.le] using h
  have hsq := lintegral_mul_exp_neg_mul_Icc_eq
    (fun x => ENNReal.ofReal ((p.eval x) ^ 2)) (by fun_prop) a b r hab.le hr
  rw [hnorm, hmass] at hsq
  have hqnorm : (∫⁻ u in Icc (0 : ℝ) L,
      ENNReal.ofReal ((q.eval u) ^ 2) * ENNReal.ofReal (Real.exp (-u))) =
        ENNReal.ofReal (1 - Real.exp (-L)) := by
    simpa only [heval] using
      ((ENNReal.mul_right_inj (ne_of_gt (ENNReal.ofReal_pos.mpr hc))
        ENNReal.ofReal_ne_top).mp hsq).symm
  have hsmall := truncated_exp_smallBall_le_of_lintegral_sq_eq
    q d hq hd L hL hqnorm ε hε
  have hcut (g : ℝ → ℝ) (hg : Continuous g) (s : Set ℝ) (w : ℝ → ENNReal) :
      (∫⁻ x in s, ({x : ℝ | |g x| ≤ ε}.indicator (fun _ => (1 : ENNReal))) x * w x) =
        ∫⁻ x in {x : ℝ | x ∈ s ∧ |g x| ≤ ε}, w x := by
    simp_rw [← indicator_mul_left, one_mul]
    rw [lintegral_indicator (measurableSet_le hg.abs.measurable measurable_const),
      Measure.restrict_restrict (measurableSet_le hg.abs.measurable measurable_const)]
    have he : {x : ℝ | |g x| ≤ ε} ∩ s =
        {x : ℝ | x ∈ s ∧ |g x| ≤ ε} := by
      ext x
      exact and_comm
    rw [he]
  let S : Set ℝ := {x : ℝ | |p.eval x| ≤ ε}
  have hS : MeasurableSet S := measurableSet_le p.continuous.abs.measurable measurable_const
  have hsub := lintegral_mul_exp_neg_mul_Icc_eq
    (S.indicator (fun _ => 1)) (measurable_const.indicator hS) a b r hab.le hr
  have hcomp (u : ℝ) :
      S.indicator (fun _ => (1 : ENNReal)) (u / r + a) =
        {u : ℝ | |q.eval u| ≤ ε}.indicator (fun _ => 1) u := by
    by_cases h : |q.eval u| ≤ ε
    · rw [indicator_of_mem (show u ∈ {u : ℝ | |q.eval u| ≤ ε} from h),
        indicator_of_mem (show u / r + a ∈ S by
          change |p.eval (u / r + a)| ≤ ε
          rwa [← heval])]
    · rw [indicator_of_notMem (show u ∉ {u : ℝ | |q.eval u| ≤ ε} from h),
        indicator_of_notMem (show u / r + a ∉ S by
          change ¬ |p.eval (u / r + a)| ≤ ε
          rwa [← heval])]
  simp_rw [hcomp] at hsub
  rw [hcut (fun x => p.eval x) p.continuous,
    hcut (fun u => q.eval u) q.continuous] at hsub
  rw [hsub, hmass, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - Real.exp (-L) by
      have := Real.exp_le_one_iff.mpr (show -L ≤ 0 by linarith)
      linarith)]
  simpa only [mul_div_mul_left _ _ hc.ne'] using hsmall
)


/-- On a nondegenerate interval `[a, b]`, a polynomial of degree at most
`d ≥ 1`, whose square integral against the normalized density `exp (r * x)`
is one, has normalized sublevel mass at most
`128 * exp 3 * d * ε ^ (1 / d)` for every `r > 0` and `ε > 0`.

This is the reflected form of the decreasing exponential bound following
[CW01, §4], with the same coarse explicit constant.

**Proof sketch.** Reflect the interval by `x ↦ -x` and compose the polynomial
with `-X`. Its degree remains at most `d`. Reflection preserves Lebesgue
measure, sends `[a, b]` to `[-b, -a]`, and turns `exp (r * x)` into
`exp (-r * x)`. Transport the normalization and both masses, then apply
the decreasing exponential bound on the reflected interval. -/
theorem increasing_exp_smallBall_le_of_lintegral_sq_eq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a b r : ℝ) (hab : a < b) (hr : 0 < r)
    (hnorm :
      (∫⁻ x in Icc a b,
        ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (r * x)) ∂volume) =
        ∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (r * x)) ∂volume)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (r * x)) ∂volume).toReal /
        (∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (r * x)) ∂volume).toReal ≤
      128 * Real.exp 3 * (d : ℝ) * ε ^ (1 / (d : ℝ)) :=
  (by
  let q : Polynomial ℝ := p.comp (-Polynomial.X)
  have heval (x : ℝ) : q.eval x = p.eval (-x) := by
    simp only [q, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
  have hq : q.natDegree ≤ d := by
    have hdeg : (-Polynomial.X : Polynomial ℝ).natDegree = 1 := by
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
    exact Polynomial.natDegree_comp_le.trans (by simpa only [hdeg, mul_one] using hp)
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Icc a b = Icc (-b) (-a) := by
    ext x
    change (a ≤ -x ∧ -x ≤ b) ↔ -b ≤ x ∧ x ≤ -a
    constructor
    · rintro ⟨h₀, h₁⟩
      constructor <;> linarith
    · rintro ⟨h₀, h₁⟩
      constructor <;> linarith
  have hmass := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (s := Icc a b) measurableSet_Icc
    (f := fun x : ℝ => ENNReal.ofReal (Real.exp (r * x))) (by fun_prop)
  simp only [hpre, mul_neg] at hmass
  have hsq := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (s := Icc a b) measurableSet_Icc
    (f := fun x : ℝ => ENNReal.ofReal ((p.eval x) ^ 2) *
      ENNReal.ofReal (Real.exp (r * x))) (by fun_prop)
  simp only [hpre, mul_neg, ← heval] at hsq
  have hqnorm :
      (∫⁻ x in Icc (-b) (-a), ENNReal.ofReal ((q.eval x) ^ 2) *
        ENNReal.ofReal (Real.exp (-r * x))) =
      ∫⁻ x in Icc (-b) (-a), ENNReal.ofReal (Real.exp (-r * x)) := by
    simpa only [neg_mul] using hsq.trans (hnorm.trans hmass.symm)
  have hsmall := decreasing_exp_smallBall_le_of_lintegral_sq_eq q d hq hd
    (-b) (-a) r (by linarith) hr hqnorm ε hε
  have hS : MeasurableSet {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε} :=
    measurableSet_Icc.inter (measurableSet_le p.continuous.abs.measurable measurable_const)
  have hsubpre : (Neg.neg : ℝ → ℝ) ⁻¹'
      {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε} =
        {x : ℝ | x ∈ Icc (-b) (-a) ∧ |q.eval x| ≤ ε} := by
    ext x
    change ((a ≤ -x ∧ -x ≤ b) ∧ |p.eval (-x)| ≤ ε) ↔
      ((-b ≤ x ∧ x ≤ -a) ∧ |q.eval x| ≤ ε)
    rw [heval]
    constructor
    · rintro ⟨⟨h₀, h₁⟩, hx⟩
      exact ⟨⟨by linarith, by linarith⟩, hx⟩
    · rintro ⟨⟨h₀, h₁⟩, hx⟩
      exact ⟨⟨by linarith, by linarith⟩, hx⟩
  have hsub := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    hS (f := fun x : ℝ => ENNReal.ofReal (Real.exp (r * x))) (by fun_prop)
  simp only [hsubpre, mul_neg] at hsub
  simpa only [neg_mul, hsub, hmass] using hsmall
)


/-- On a nondegenerate interval `[a, b]`, a polynomial of degree at most
`d ≥ 1`, whose square integral against the normalized density `exp (s * x)`
is one, has normalized sublevel mass at most
`128 * exp 3 * d * ε ^ (1 / d)` for every real slope `s` and `ε > 0`.

This combines the uniform and exponential interval bounds following the
Remez method in [CW01, §4]. The normalization and coarse explicit constant
are the formulation used here.

**Proof sketch.** Split according to the sign of the slope. For negative
slope, apply the decreasing exponential estimate with rate `-s`; for
positive slope, apply the increasing exponential estimate with rate `s`.
At slope zero the density is one, so apply the uniform-interval estimate
and absorb its constant `4 * exp 2` into `128 * exp 3 * d` using `d ≥ 1`. -/
theorem exp_smallBall_le_of_lintegral_sq_eq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a b s : ℝ) (hab : a < b)
    (hnorm :
      (∫⁻ x in Icc a b,
        ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal (Real.exp (s * x)) ∂volume) =
        ∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (s * x)) ∂volume)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (s * x)) ∂volume).toReal /
        (∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (s * x)) ∂volume).toReal ≤
      128 * Real.exp 3 * (d : ℝ) * ε ^ (1 / (d : ℝ)) :=
  (by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · simpa only [neg_neg] using
      decreasing_exp_smallBall_le_of_lintegral_sq_eq p d hp hd a b (-s) hab
        (neg_pos.mpr hs) (by simpa only [neg_neg] using hnorm) ε hε
  · subst s
    simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one,
      lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at hnorm ⊢
    apply (uniform_smallBall_le_of_lintegral_sq_eq p d hp hd a b hab hnorm ε hε).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have he : Real.exp 2 ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
    calc
      _ ≤ 4 * Real.exp 3 := mul_le_mul_of_nonneg_left he (by norm_num)
      _ ≤ _ := by nlinarith [Real.exp_pos 3]
  · exact increasing_exp_smallBall_le_of_lintegral_sq_eq p d hp hd a b s hab hs hnorm ε hε
)


/-- For a polynomial of degree at most `d ≥ 1` on a nondegenerate interval
with density `exp (s * x)`, the `2 * d`-th power of its `ε`-sublevel mass,
times its square integral, is at most
`(128 * exp 3 * d) ^ (2 * d) * ε ^ 2` times the
`(2 * d + 1)`-st power of the total density mass.

This homogeneous formulation of the exponential-needle estimate follows
the Remez method in [CW01, §4]. The coarse explicit constant and
multiplicative formulation are those used here for localization.

**Proof sketch.** All relevant integrals are finite because the interval
is compact and the polynomial and density are continuous. Write `M` for
the total density mass, `Q` for the square integral, and `S` for the
sublevel mass. The mass `M` is positive. If `Q = 0`, the conclusion is
immediate. Otherwise multiply the polynomial by `sqrt (M / Q)`; its degree
does not increase and its square integral becomes `M`. Apply the
normalized exponential-needle estimate at threshold
`ε * sqrt (M / Q)`. Raise the resulting inequality to power `2 * d`,
simplify the positive powers and square root, and clear denominators. -/
theorem exp_smallBall_pow_mul_lintegral_sq_le
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a b s : ℝ) (hab : a < b)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε},
      ENNReal.ofReal (Real.exp (s * x)) ∂volume).toReal ^ (2 * d) *
        (∫⁻ x in Icc a b,
          ENNReal.ofReal ((p.eval x) ^ 2) *
            ENNReal.ofReal (Real.exp (s * x)) ∂volume).toReal ≤
      (128 * Real.exp 3 * (d : ℝ)) ^ (2 * d) * ε ^ 2 *
        (∫⁻ x in Icc a b,
          ENNReal.ofReal (Real.exp (s * x)) ∂volume).toReal ^ (2 * d + 1) :=
  (by
  let M : ℝ := (∫⁻ x in Icc a b, ENNReal.ofReal (Real.exp (s * x))).toReal
  let Q : ℝ := (∫⁻ x in Icc a b, ENNReal.ofReal ((p.eval x) ^ 2) *
    ENNReal.ofReal (Real.exp (s * x))).toReal
  let S : ℝ := (∫⁻ x in {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε},
    ENNReal.ofReal (Real.exp (s * x))).toReal
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  have hMfin : (∫⁻ x in Icc a b, ENNReal.ofReal (Real.exp (s * x))) ≠ ⊤ := by
    exact ne_of_lt (setLIntegral_lt_top_of_isCompact measure_Icc_lt_top.ne isCompact_Icc
      (f := fun x : ℝ => Real.toNNReal (Real.exp (s * x))) (by fun_prop))
  have hQfin : (∫⁻ x in Icc a b, ENNReal.ofReal ((p.eval x) ^ 2) *
      ENNReal.ofReal (Real.exp (s * x))) ≠ ⊤ := by
    simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ne_of_lt (setLIntegral_lt_top_of_isCompact measure_Icc_lt_top.ne isCompact_Icc
      (f := fun x : ℝ => Real.toNNReal ((p.eval x) ^ 2 * Real.exp (s * x))) (by fun_prop))
  have hMpos : 0 < M := by
    apply ENNReal.toReal_pos _ hMfin
    apply ne_of_gt
    rw [setLIntegral_pos_iff (by fun_prop)]
    have hsupp : Function.support (fun x : ℝ => ENNReal.ofReal (Real.exp (s * x))) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    rw [hsupp, univ_inter, Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  change S ^ (2 * d) * Q ≤
    (128 * Real.exp 3 * (d : ℝ)) ^ (2 * d) * ε ^ 2 * M ^ (2 * d + 1)
  by_cases hQzero : Q = 0
  · rw [hQzero, mul_zero]
    positivity
  · have hQpos : 0 < Q := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hQzero)
    let c : ℝ := Real.sqrt (M / Q)
    have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hMpos hQpos)
    have hc2 : c ^ 2 = M / Q := Real.sq_sqrt (div_nonneg hMpos.le hQpos.le)
    let q : Polynomial ℝ := Polynomial.C c * p
    have heval (x : ℝ) : q.eval x = c * p.eval x := Polynomial.eval_C_mul
    have hq : q.natDegree ≤ d := (Polynomial.natDegree_C_mul_le c p).trans hp
    have hMeq : ENNReal.ofReal M =
        ∫⁻ x in Icc a b, ENNReal.ofReal (Real.exp (s * x)) :=
      ENNReal.ofReal_toReal hMfin
    have hQeq : ENNReal.ofReal Q = ∫⁻ x in Icc a b,
        ENNReal.ofReal ((p.eval x) ^ 2) * ENNReal.ofReal (Real.exp (s * x)) :=
      ENNReal.ofReal_toReal hQfin
    have hqnorm : (∫⁻ x in Icc a b, ENNReal.ofReal ((q.eval x) ^ 2) *
        ENNReal.ofReal (Real.exp (s * x))) =
        ∫⁻ x in Icc a b, ENNReal.ofReal (Real.exp (s * x)) := by
      simp_rw [heval, mul_pow, ENNReal.ofReal_mul (sq_nonneg c), mul_assoc]
      rw [lintegral_const_mul _ (by fun_prop), ← hQeq, ← hMeq,
        ← ENNReal.ofReal_mul (sq_nonneg c), hc2, div_mul_cancel₀ _ hQpos.ne']
    have hsmall := exp_smallBall_le_of_lintegral_sq_eq q d hq hd a b s hab
      hqnorm (ε * c) (mul_pos hε hc)
    have hset : {x : ℝ | x ∈ Icc a b ∧ |q.eval x| ≤ ε * c} =
        {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε} := by
      ext x
      simp only [mem_setOf_eq, heval, abs_mul, abs_of_pos hc]
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, by nlinarith⟩
      · rintro ⟨hx, h⟩
        exact ⟨hx, by nlinarith⟩
    rw [hset] at hsmall
    have hd0 : d ≠ 0 := by omega
    have hroot : ((ε * c) ^ (1 / (d : ℝ))) ^ (2 * d) = (ε * c) ^ 2 := by
      rw [Nat.mul_comm 2 d, pow_mul, one_div,
        Real.rpow_inv_natCast_pow (mul_pos hε hc).le hd0]
    have hpow := pow_le_pow_left₀ (div_nonneg hS hMpos.le) hsmall (2 * d)
    have hspow : S ^ (2 * d) ≤
        (128 * Real.exp 3 * (d : ℝ)) ^ (2 * d) * (ε * c) ^ 2 * M ^ (2 * d) :=
      (div_le_iff₀ (pow_pos hMpos (2 * d))).mp (by
        simpa only [div_pow, mul_pow, hroot] using hpow)
    calc
      _ ≤ ((128 * Real.exp 3 * (d : ℝ)) ^ (2 * d) *
          (ε * c) ^ 2 * M ^ (2 * d)) * Q :=
        mul_le_mul_of_nonneg_right hspow hQpos.le
      _ = _ := by
        rw [mul_pow ε c, hc2, pow_succ]
        field_simp
        ring
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
