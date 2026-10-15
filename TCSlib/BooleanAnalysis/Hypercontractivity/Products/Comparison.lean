/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.General
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Norm comparison helpers for finite products

## Main definitions

No new definitions are introduced.

## Main results

* `ComparisonAux.norm_interpolation_bound`: weighted interpolation converts
  an exponential higher-norm bound into an `L¹`-to-`L²` comparison.
* `ComparisonAux.log_sinh_difference_hasDerivAt_two`: the logarithmic
  hyperbolic-sine ratio has an explicit derivative at exponent two.
* `ComparisonAux.log_odds_coth`: half the log odds has hyperbolic cotangent
  equal to the reciprocal bias.
* `ComparisonAux.sharp_radius_comparison_limit`: the sharp-radius comparison
  coefficient tends to the product norm-comparison constant.
* `ComparisonAux.constant_tendsto_half`: the comparison constant tends to
  `e` as the atom bound approaches one half from below.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Theorems 9.22 (proof) and 10.22.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity.ComparisonAux

universe u

/-- For positive variance and any positive rate, variance times the rate
raised to normalized total influence is at most the sum of component
second moments weighted by their degrees and the corresponding rate powers.
[OD14, §10.3, KKL Isoperimetric Theorem (proof)]
The estimate applies to arbitrary real-valued finite-product functions
and imposes no upper bound on the rate.

**Proof sketch.** The nonempty component energies sum to the variance,
and their degree-weighted sum is total influence. Apply weighted Jensen
to these energies and their degrees. Every nonempty component has degree
at least one, so inserting the degree factor increases the resulting sum. -/
lemma variance_rpow_ratio_le_noisy_total {n : ℕ}
    (P : FiniteProduct.{u} n) (f : P.Point → ℝ)
    (hvar : 0 < P.variance f) (ρ : ℝ) (hρ : 0 < ρ) :
    P.variance f * ρ ^ (P.totalInfluence f / P.variance f) ≤
      ∑ S : Finset (Fin n), (S.card : ℝ) * ρ ^ S.card *
        P.expect (fun x => P.component S f x ^ 2) :=
  (by
  classical
  let E : Finset (Fin n) → ℝ := fun S =>
    P.expect (fun x => P.component S f x ^ 2)
  let w : Finset (Fin n) → ℝ := fun S => if S = ∅ then 0 else E S
  have hE (S : Finset (Fin n)) : 0 ≤ E S := by
    unfold E FiniteProduct.expect
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
        (sq_nonneg _)
  have hw (S : Finset (Fin n)) : 0 ≤ w S := by
    dsimp [w]
    split_ifs
    · exact le_rfl
    · exact hE S
  have hsum : (∑ S, w S) = P.variance f :=
    (RandomizationAux.variance_eq_sum_components P f).symm
  have hdegree : (∑ S, w S * (S.card : ℝ)) = P.totalInfluence f := by
    rw [RandomizationAux.totalInfluence_eq_sum_card_components]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S = ∅ <;> simp [w, E, hS, mul_comm]
  have hJ := FiniteNorms.weighted_rpow_mean_le w hw
    (show 0 < ∑ S, w S by rw [hsum]; exact hvar)
    (fun S => (S.card : ℝ)) ρ hρ
  rw [hsum, hdegree] at hJ
  apply hJ.trans
  apply Finset.sum_le_sum
  intro S _
  rw [Real.rpow_natCast]
  by_cases hS : S = ∅
  · simp [w, hS]
  · have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    rw [show w S = E S by simp [w, hS]]
    calc
      _ = 1 * (ρ ^ S.card * E S) := by ring
      _ ≤ (S.card : ℝ) * (ρ ^ S.card * E S) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (pow_nonneg hρ.le _) (hE S))
      _ = _ := by ring
)

/-- For a finite-product function and `q > 2`, a bound
`‖f‖q ≤ exp(c) ‖f‖₂` implies
`‖f‖₂ ≤ exp(c q / (q - 2)) ‖f‖₁`.
[OD14, Thm. 9.22 (proof); Thm. 10.22]
This weighted formulation permits heterogeneous coordinate laws and arbitrary real `c`.

**Proof sketch.** Apply weighted Hölder with weight equal to the product mass
times the absolute value of the function, observable its absolute value,
and exponent `q - 1`. Rewrite the resulting first and higher moments as
powers of their norms. Substitute the assumed bound on the higher norm
and use scalar interpolation cancellation. If the second norm vanishes,
nonnegativity gives the conclusion directly. -/
lemma norm_interpolation_bound {n : ℕ} (P : FiniteProduct.{u} n)
    (q c : ℝ) (hq : 2 < q) (f : P.Point → ℝ)
    (hbound : P.norm q f ≤ Real.exp c * P.norm 2 f) :
    P.norm 2 f ≤ Real.exp (c * q / (q - 2)) * P.norm 1 f :=
  (by
  classical
  have hmass_nonneg (x : P.Point) : 0 ≤ P.mass x :=
    Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
  have hmoment_nonneg (r : ℝ) : 0 ≤ P.expect (fun x => |f x| ^ r) :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (hmass_nonneg x) (Real.rpow_nonneg (abs_nonneg _) _)
  have hnorm_nonneg (r : ℝ) : 0 ≤ P.norm r f :=
    Real.rpow_nonneg (hmoment_nonneg r) _
  by_cases hzero : P.norm 2 f = 0
  · rw [hzero]
    exact mul_nonneg (Real.exp_pos _).le (hnorm_nonneg 1)
  have hM : 0 < P.norm 2 f :=
    lt_of_le_of_ne (hnorm_nonneg 2) (Ne.symm hzero)
  have hq1 : 0 < q - 1 := by linarith
  let u : ℝ := (q - 2) / (q - 1)
  let v : ℝ := q / (q - 1)
  have hu : 0 < u := div_pos (sub_pos.mpr hq) hq1
  have hv : 0 ≤ v := div_nonneg (by linarith) hq1.le
  have huv : u + v = 2 := by
    dsimp [u, v]
    field_simp [hq1.ne']
    ring
  have hexponent : 1 - (q - 1)⁻¹ = u := by
    dsimp [u]
    field_simp [hq1.ne']
    ring
  have hprod (x : P.Point) :
      |f x| * |f x| ^ (q - 1) = |f x| ^ q := by
    calc
      _ = |f x| ^ (1 : ℝ) * |f x| ^ (q - 1) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add_of_nonneg (abs_nonneg _) zero_le_one hq1.le,
          show (1 : ℝ) + (q - 1) = q by ring]
  have hi := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ
    (p := q - 1) (by linarith)
    (fun x : P.Point => P.mass x * |f x|) (fun x => |f x|)
    (fun x => mul_nonneg (hmass_nonneg x) (abs_nonneg _))
    (fun x => abs_nonneg _)
  simp_rw [mul_assoc, hprod, ← pow_two, ← Real.rpow_two] at hi
  change P.expect (fun x => |f x| ^ (2 : ℝ)) ≤
    (P.expect (fun x => |f x|)) ^ (1 - (q - 1)⁻¹) *
      (P.expect (fun x => |f x| ^ q)) ^ (q - 1)⁻¹ at hi
  have hnorm_rpow (r : ℝ) (hr : r ≠ 0) :
      P.norm r f ^ r = P.expect (fun x => |f x| ^ r) := by
    unfold FiniteProduct.norm
    rw [← Real.rpow_mul (hmoment_nonneg r), one_div_mul_cancel hr,
      Real.rpow_one]
  have hnorm_one : P.norm 1 f = P.expect (fun x => |f x|) := by
    simp [FiniteProduct.norm]
  have hnorm_two : P.norm 2 f ^ 2 =
      P.expect (fun x => |f x| ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using hnorm_rpow 2 (by norm_num)
  rw [hexponent, ← hnorm_one, ← hnorm_two,
    ← hnorm_rpow q (by linarith),
    ← Real.rpow_mul (hnorm_nonneg q)] at hi
  change P.norm 2 f ^ 2 ≤ P.norm 1 f ^ u * P.norm q f ^ v at hi
  have hc := lp_interpolation_cancel (P.norm 1 f) (P.norm 2 f) u v c
    (hnorm_nonneg 1) hM hu huv
    (hi.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hnorm_nonneg q) hbound hv)
      (Real.rpow_nonneg (hnorm_nonneg 1) u)))
  have hexp : c * v / u = c * q / (q - 2) := by
    dsimp [u, v]
    field_simp [hq1.ne', (sub_pos.mpr hq).ne']
  simpa only [hexp] using hc
)

/-- For `u > 0`, the logarithmic hyperbolic-sine ratio underlying the sharp
discrete radius has derivative `-u coth(u/2) / 4` at exponent two.
[OD14, Thm. 10.22 (proof via Thm. 10.18)]
The difference of logarithms avoids differentiating a square root.

**Proof sketch.** Differentiate the two logarithmic hyperbolic sines.
At exponent two their arguments coincide at `u/2`, while their derivatives
are opposite. Subtract and divide by two. -/
lemma log_sinh_difference_hasDerivAt_two (u : ℝ) (hu : 0 < u) :
    HasDerivAt
      (fun q : ℝ =>
        (Real.log (Real.sinh (u / q)) -
          Real.log (Real.sinh (u - u / q))) / 2)
      (-u * Real.cosh (u / 2) / (4 * Real.sinh (u / 2))) 2 :=
  (by
  have hs : Real.sinh (u / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity : 0 < u / 2)).ne'
  have hhalf : u - u / 2 = u / 2 := by ring
  have hd : HasDerivAt (fun q : ℝ => u / q) (-u / 4) 2 := by
    convert (hasDerivAt_const (2 : ℝ) u).div
      (hasDerivAt_id (2 : ℝ)) (by norm_num) using 1
    norm_num
  have hleft := hd.sinh.log hs
  have hright := (hd.const_sub u).sinh.log
    (by simpa only [hhalf] using hs)
  convert (hleft.sub hright).div_const (2 : ℝ) using 1
  simp only [hhalf]
  field_simp [hs]
  ring
)

/-- For an atom bound strictly between zero and one half, the hyperbolic
cotangent of half its log odds equals the reciprocal bias.
[OD14, Thm. 10.22 (proof via Thm. 10.18)]

**Proof sketch.** Expand the hyperbolic functions into exponentials.
The exponential of half the log odds equals `(1-lam)/lam` times
the exponential of its negative. Multiplying by `lam` gives a linear
relation between these exponentials. Clear the nonzero denominators
and use that relation to simplify. -/
lemma log_odds_coth (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) :
    Real.cosh (Real.log ((1 - lam) / lam) / 2) /
        Real.sinh (Real.log ((1 - lam) / lam) / 2) =
      1 / (1 - 2 * lam) :=
  (by
  let v : ℝ := Real.log ((1 - lam) / lam) / 2
  have hodds : 1 < (1 - lam) / lam :=
    (lt_div_iff₀ hlam).mpr (by linarith)
  have hv : 0 < v := div_pos (Real.log_pos hodds) (by norm_num)
  have hs : Real.sinh v ≠ 0 := (Real.sinh_pos_iff.mpr hv).ne'
  have hbias : 1 - 2 * lam ≠ 0 := by linarith
  have hexp : Real.exp v =
      ((1 - lam) / lam) * Real.exp (-v) := by
    calc
      _ = Real.exp (Real.log ((1 - lam) / lam) + -v) := by
        congr 1
        dsimp [v]
        ring
      _ = Real.exp (Real.log ((1 - lam) / lam)) * Real.exp (-v) :=
        Real.exp_add _ _
      _ = _ := by rw [Real.exp_log (zero_lt_one.trans hodds)]
  have hlinear : lam * Real.exp v =
      (1 - lam) * Real.exp (-v) := by
    rw [hexp]
    field_simp [hlam.ne']
  change Real.cosh v / Real.sinh v = 1 / (1 - 2 * lam)
  apply (div_eq_div_iff hs hbias).mpr
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith only [hlinear]
)

/-- For `0 < lam < 1/2`, the sharp discrete radius gives a limiting
`L¹`-to-`L²` comparison coefficient equal to the explicit product
norm-comparison constant. [OD14, Thm. 10.22]

**Proof sketch.** Write the logarithm of the radius as half the difference
of two logarithmic hyperbolic sines. Its value at exponent two is zero.
The derivative gives the limit of its difference quotient. Express the
hyperbolic cotangent in terms of the atom bound, then exponentiate. -/
lemma sharp_radius_comparison_limit (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) :
    Filter.Tendsto
      (fun q : ℝ =>
        Real.exp (-Real.log (sharpDiscreteRadius q lam) * q / (q - 2)))
      (nhdsWithin 2 (Set.Ioi 2))
      (nhds (productNormComparisonConstant lam)) :=
  (by
  let u : ℝ := Real.log ((1 - lam) / lam)
  let L : ℝ → ℝ := fun q =>
    (Real.log (Real.sinh (u / q)) - Real.log (Real.sinh (u - u / q))) / 2
  have hodds : 1 < (1 - lam) / lam :=
    (lt_div_iff₀ hlam).mpr (by linarith)
  have hu : 0 < u := Real.log_pos hodds
  have hlog (q : ℝ) (hq : 2 < q) :
      Real.log (sharpDiscreteRadius q lam) = L q := by
    have hq0 : 0 < q := by linarith
    have hq1 : 0 < q - 1 := by linarith
    have harg : u / (q / (q - 1)) = u - u / q := by
      field_simp [hq0.ne', hq1.ne']
    have hnum : 0 < Real.sinh (u / q) :=
      Real.sinh_pos_iff.mpr (div_pos hu hq0)
    have hden : 0 < Real.sinh (u / (q / (q - 1))) :=
      Real.sinh_pos_iff.mpr (div_pos hu (div_pos hq0 hq1))
    change Real.log (Real.sqrt
      (Real.sinh (u / q) / Real.sinh (u / (q / (q - 1))))) = L q
    rw [Real.log_sqrt (div_pos hnum hden).le,
      Real.log_div hnum.ne' hden.ne', harg]
  have hLtwo : L 2 = 0 := by
    dsimp [L]
    rw [show u - u / 2 = u / 2 by ring]
    simp
  have hd : HasDerivAt L
      (-u * Real.cosh (u / 2) / (4 * Real.sinh (u / 2))) 2 :=
    log_sinh_difference_hasDerivAt_two u hu
  have hslope : Filter.Tendsto (fun q : ℝ => L q / (q - 2))
      (nhdsWithin 2 (Set.Ioi 2))
      (nhds (-u * Real.cosh (u / 2) / (4 * Real.sinh (u / 2)))) := by
    convert hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (2 : ℝ)) using 1
    funext q
    rw [slope_def_field, hLtwo, sub_zero]
  have hid : Filter.Tendsto (fun q : ℝ => q)
      (nhdsWithin 2 (Set.Ioi 2)) (nhds 2) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hc : Real.cosh (u / 2) / Real.sinh (u / 2) = 1 / (1 - 2 * lam) :=
    log_odds_coth lam hlam hlamhalf
  have hvalue :
      -(-u * Real.cosh (u / 2) / (4 * Real.sinh (u / 2))) * 2 =
        u / (2 * (1 - 2 * lam)) := by
    calc
      _ = u / 2 * (Real.cosh (u / 2) / Real.sinh (u / 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = u / 2 * (1 / (1 - 2 * lam)) := by rw [hc]
      _ = _ := by rw [div_mul_div_comm, mul_one]
  have hlimit := hslope.neg.mul hid
  rw [hvalue] at hlimit
  have hconstant :
      Real.exp (u / (2 * (1 - 2 * lam))) = productNormComparisonConstant lam := by
    rw [productNormComparisonConstant, if_neg (ne_of_lt hlamhalf),
      Real.rpow_def_of_pos (zero_lt_one.trans hodds)]
    congr 1
    dsimp [u]
    ring
  have he := hlimit.rexp
  rw [hconstant] at he
  apply he.congr'
  filter_upwards [eventually_mem_nhdsWithin] with q hq
  rw [hlog q hq]
  apply congrArg Real.exp
  ring
)

/-- The sharp comparison constant tends to `e` as the minimum atom mass tends to one half
from below. [OD14, Thm. 10.22]

**Proof sketch.** Take logarithms and evaluate the removable singularity of
`log((1-lam)/lam)/(2(1-2lam))` at one half by differentiation. Exponentiate its limit one. -/
lemma constant_tendsto_half :
    Filter.Tendsto productNormComparisonConstant
      (nhdsWithin (1 / 2) (Set.Ioo 0 (1 / 2))) (nhds (Real.exp 1)) := (by
    have hderiv : HasDerivAt
        (fun x : ℝ => Real.log ((1 - x) / x)) (-4) (1 / 2) := by
      convert (((hasDerivAt_id (1 / 2 : ℝ)).const_sub (1 : ℝ)).div
        (hasDerivAt_id (1 / 2 : ℝ)) (by norm_num)).log (by norm_num) using 1
      norm_num
    have hlimit : Filter.Tendsto
        (fun x : ℝ => slope (fun y : ℝ => Real.log ((1 - y) / y)) (1 / 2) x / (-4))
        (nhdsWithin (1 / 2) (Set.Ioo 0 (1 / 2))) (nhds 1) := by
      convert (hderiv.tendsto_slope.div_const (-4)).mono_left
        (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2)) =>
          hx.2.ne)) using 1
      norm_num
    refine hlimit.rexp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    have hnum : 0 < 1 - lam := by linarith [hlam.2]
    symm
    rw [productNormComparisonConstant, if_neg hlam.2.ne,
      Real.rpow_def_of_pos (div_pos hnum hlam.1), slope_def_field]
    congr 1
    norm_num
    rw [show 1 - 2 * lam = -2 * (lam - 1 / 2) by ring]
    norm_num [mul_inv_rev, div_eq_mul_inv]
    ring
)


/-- A mean-zero finite-product function with positive second moment and
second norm at most `C` times its first norm has positive-support
probability at least `1 / (4 * C²)`, for `C > 0`.
[OD14, Thm. 9.24 (proof); Thm. 10.23 (proof)]

**Proof sketch.** Square the norm comparison and identify the squared
second norm with the second moment. The centered weighted
Cauchy–Schwarz estimate bounds the squared first norm by four times
the second moment times the positive-support probability.
Cancel the positive second moment and rearrange. -/
lemma centered_probability_ge_of_norm_comparison {n : ℕ}
    (P : FiniteProduct.{u} n) (g : P.Point → ℝ)
    (hmean : P.expect g = 0)
    (hsecond : 0 < P.expect (fun x => g x ^ 2))
    (C : ℝ) (hC : 0 < C)
    (hnorm : P.norm 2 g ≤ C * P.norm 1 g) :
    (1 / 4 : ℝ) * (C ^ 2)⁻¹ ≤ P.prob (fun x => 0 < g x) :=
  (by
  classical
  have hmass (x : P.Point) : 0 ≤ P.mass x :=
    Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
  have htwo : P.norm 2 g = Real.sqrt (P.expect (fun x => g x ^ 2)) := by
    simp only [FiniteProduct.norm, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  have hCS :
      P.norm 1 g ^ 2 ≤
        4 * P.expect (fun x => g x ^ 2) * P.prob (fun x => 0 < g x) := by
    simpa [FiniteProduct.norm, FiniteProduct.expect, FiniteProduct.prob,
      FiniteProduct.indicator, Set.indicator] using
      FiniteNorms.centered_abs_sum_sq_le P.mass hmass g hmean
  have hnorm_sq := pow_le_pow_left₀
    (show 0 ≤ P.norm 2 g by rw [htwo]; exact Real.sqrt_nonneg _) hnorm 2
  rw [htwo, Real.sq_sqrt hsecond.le, mul_pow] at hnorm_sq
  have hbound := hnorm_sq.trans
    (mul_le_mul_of_nonneg_left hCS (sq_nonneg C))
  change (1 / 4 : ℝ) / C ^ 2 ≤ P.prob (fun x => 0 < g x)
  apply (div_le_iff₀ (sq_pos_of_pos hC)).2
  apply (mul_le_mul_iff_left₀ (by norm_num : (0 : ℝ) < 4)).mp
  norm_num
  apply (mul_le_mul_iff_left₀ hsecond).mp
  calc
    1 * P.expect (fun x => g x ^ 2) = P.expect (fun x => g x ^ 2) := one_mul _
    _ ≤ C ^ 2 * (4 * P.expect (fun x => g x ^ 2) *
        P.prob (fun x => 0 < g x)) := hbound
    _ = P.prob (fun x => 0 < g x) * C ^ 2 * 4 *
        P.expect (fun x => g x ^ 2) := by ring
)


/-- For every positive atom parameter and positive natural degree, the
coarse anticoncentration bound `(15 / lam)^(-k)` is at most one quarter
of `(exp 2 / (2 * lam))^(-k)`. [OD14, Thm. 10.23]
This numerical comparison requires no upper bound on `lam`.

**Proof sketch.** The estimate `exp 2 ≤ 15 / 2` bounds the ratio
`exp 2 / 30` by one quarter. Raising this nonnegative ratio to an
integer exponent at least one can only decrease it.
Rearrange the positive real powers to obtain the comparison. -/
lemma anticoncentration_coarse_lower_bound (lam : ℝ) (hlam : 0 < lam)
    (k : ℕ) (hk : 0 < k) :
    (15 / lam) ^ (-(k : ℝ)) ≤
      (1 / 4 : ℝ) * (Real.exp 2 / (2 * lam)) ^ (-(k : ℝ)) :=
  (by
  let A : ℝ := Real.exp 2 / (2 * lam)
  let B : ℝ := 15 / lam
  have hA : 0 < A := div_pos (Real.exp_pos _) (mul_pos (by norm_num) hlam)
  have hB : 0 < B := div_pos (by norm_num) hlam
  have hexp : Real.exp 2 ≤ 15 / 2 := by
    have hsquare := (sq_le_sq₀ (Real.exp_pos 1).le
      (by norm_num : (0 : ℝ) ≤ 2.7182818286)).2 Real.exp_one_lt_d9.le
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [hsquare]
  have hratio : A / B ≤ 1 / 4 := by
    have heq : A / B = Real.exp 2 / 30 := by
      dsimp [A, B]
      field_simp [hlam.ne']
      ring
    rw [heq]
    linarith
  have hpower : (A / B) ^ (k : ℝ) ≤ 1 / 4 :=
    (Real.rpow_le_self_of_le_one (div_nonneg hA.le hB.le)
      (hratio.trans (by norm_num))
      (by exact_mod_cast Nat.succ_le_of_lt hk)).trans hratio
  change B ^ (-(k : ℝ)) ≤ (1 / 4 : ℝ) * A ^ (-(k : ℝ))
  rw [Real.rpow_neg hB.le, Real.rpow_neg hA.le,
    ← one_div (B ^ (k : ℝ))]
  change 1 / B ^ (k : ℝ) ≤ (1 / 4 : ℝ) / A ^ (k : ℝ)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hB _)
    (Real.rpow_pos_of_pos hA _)).2
  rw [one_mul]
  rw [Real.div_rpow hA.le hB.le] at hpower
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hB _)).mp hpower
)


/-- Squaring the variance-normalized noisy coefficient at rate
`√lam / 3` gives the explicit KKL coefficient
`(I / V)⁻² * (9 / lam)^(-(I / V))`.
[OD14, §10.3, KKL Isoperimetric Theorem (proof)]
The identity permits arbitrary real `I`, including zero under Lean's
totalized division convention.

**Proof sketch.** Separate the squared ratio from the squared rate
power. The ratio equals the reciprocal of `I / V`; the rate squared
is `lam / 9`. Combine real exponents and invert the positive base
to obtain `9 / lam` with the negative normalized exponent. -/
lemma kkl_coefficient_eq (lam V I : ℝ) (hlam : 0 < lam) (hV : 0 < V) :
    ((V * (Real.sqrt lam / 3) ^ (I / V)) / I) ^ 2 =
      (I / V)⁻¹ ^ 2 * (9 / lam) ^ (-(I / V)) :=
  (by
  let ρ : ℝ := Real.sqrt lam / 3
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ_sq : ρ ^ 2 = (9 / lam)⁻¹ := by
    dsimp [ρ]
    rw [div_pow, Real.sq_sqrt hlam.le, inv_div]
    norm_num
  have hpower : (ρ ^ (I / V)) ^ 2 = (9 / lam) ^ (-(I / V)) := by
    calc
      _ = ρ ^ ((I / V) * 2) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hρ]
      _ = (ρ ^ 2) ^ (I / V) := by
        rw [mul_comm (I / V) (2 : ℝ)]
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast_mul hρ 2 (I / V)
      _ = _ := by
        rw [hρ_sq, Real.rpow_neg_eq_inv_rpow]
  change ((V * ρ ^ (I / V)) / I) ^ 2 =
    (I / V)⁻¹ ^ 2 * (9 / lam) ^ (-(I / V))
  rw [div_pow, mul_pow, hpower, inv_div, div_pow]
  ring
)


/-- For `0 < lam ≤ 1/2`, the logarithms used in the product KKL
consequence satisfy `1/2 ≤ log(1/lam) ≤ log(9/lam)` and
`log(9/lam) ≤ 5 * log(1/lam)`.
[OD14, §10.3, KKL Isoperimetric Theorem, consequence]
These explicit numerical bounds isolate the logarithmic parameter comparison.

**Proof sketch.** Since `1/lam ≥ 2`, logarithm monotonicity and
`1 - 1/2 ≤ log 2` give the first lower bound. Write
`log(9/lam) = log 9 + log(1/lam)`; nonnegativity of `log 9`
gives the middle inequality. Finally, `9 ≤ 2⁴` yields
`log 9 ≤ 4 * log 2 ≤ 4 * log(1/lam)`, giving the upper bound. -/
lemma kkl_log_parameters (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ Real.log (1 / lam) ∧
      Real.log (1 / lam) ≤ Real.log (9 / lam) ∧
      Real.log (9 / lam) ≤ 5 * Real.log (1 / lam) :=
  (by
  have hrecip : (2 : ℝ) ≤ 1 / lam :=
    (le_div_iff₀ hlam).2 (by linarith)
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htwo : Real.log 2 ≤ Real.log (1 / lam) :=
    Real.log_le_log (by norm_num) hrecip
  have hsplit : Real.log (9 / lam) =
      Real.log 9 + Real.log (1 / lam) := by
    rw [Real.log_div (by norm_num) hlam.ne',
      Real.log_div one_ne_zero hlam.ne', Real.log_one]
    ring
  have hnine_nonneg : 0 ≤ Real.log (9 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hnine : Real.log (9 : ℝ) ≤ 4 * Real.log 2 := by
    calc
      Real.log (9 : ℝ) ≤ Real.log ((2 : ℝ) ^ 4) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 4 * Real.log 2 := by
        simpa only [Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 4
  refine ⟨hlogtwo.trans htwo, ?_, ?_⟩
  · rw [hsplit]
    linarith
  · rw [hsplit]
    linarith
)

/-- For every positive real `t`, `exp(-2 * t)` is at most the square
of `t⁻¹`. This elementary estimate is used to make the constant in
the product KKL consequence explicit.
[OD14, §10.3, KKL Isoperimetric Theorem, consequence]

**Proof sketch.** The logarithm estimate `log t ≤ t - 1 ≤ t`
gives `-2 * t ≤ -2 * log t`. Exponentiate this inequality
and use `exp(log t) = t` to identify the upper bound with `t⁻²`. -/
lemma kkl_inverse_square_exp_lower (t : ℝ) (ht : 0 < t) :
    Real.exp (-2 * t) ≤ t⁻¹ ^ 2 :=
  (by
  calc
    Real.exp (-2 * t) ≤ Real.exp (2 * (-Real.log t)) :=
      Real.exp_le_exp.mpr (by linarith [Real.log_le_sub_one_of_pos ht])
    _ = Real.exp (-Real.log t) ^ 2 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (-Real.log t) 2
    _ = t⁻¹ ^ 2 := by
      rw [Real.exp_neg, Real.exp_log ht]
)

/-- If `2 ≤ 100 * L`, `2 * (D + 2) ≤ 100 * L`, `0 ≤ x`, and `0 < t`,
then `x / (100 * L * exp x)` is bounded either by `t / exp x`
or by `t⁻² * exp(-D * t)`.
[OD14, §10.3, KKL Isoperimetric Theorem, consequence]
This numerical dichotomy makes the universal choice `c = 1/100`
explicit, without requiring positivity of `D` or `t ≥ 1`.

**Proof sketch.** Split according to whether `x ≤ 100 * L * t`.
In that case, division by the positive denominator gives the first
alternative. Otherwise the parameter bounds imply `(D + 2) * t ≤ x/2`.
The inverse-square exponential estimate makes the second bound at least
`exp(-(D + 2) * t)`, hence at least `exp(-x/2)`. Finally,
`x/2 ≤ exp(x/2)` and `100 * L ≥ 2` bound the target by `exp(-x/2)`. -/
lemma kkl_scalar_dichotomy (L D x t : ℝ)
    (hL : 2 ≤ 100 * L) (hD : 2 * (D + 2) ≤ 100 * L)
    (hx : 0 ≤ x) (ht : 0 < t) :
    x / (100 * L * Real.exp x) ≤ t / Real.exp x ∨
      x / (100 * L * Real.exp x) ≤ t⁻¹ ^ 2 * Real.exp (-D * t) :=
  (by
  have hden : 0 < 100 * L := by linarith
  by_cases havg : x ≤ 100 * L * t
  · left
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right
      ((div_le_iff₀ hden).2 (by nlinarith)) (Real.exp_nonneg x)
  · right
    have hcut : (D + 2) * t ≤ x / 2 := by
      have hlarge : 100 * L * t < x := lt_of_not_ge havg
      nlinarith [mul_le_mul_of_nonneg_right hD ht.le]
    calc
      x / (100 * L * Real.exp x) ≤ Real.exp (-(x / 2)) := by
        rw [div_mul_eq_div_div]
        apply (div_le_iff₀ (Real.exp_pos x)).2
        calc
          x / (100 * L) ≤ x / 2 :=
            div_le_div_of_nonneg_left hx (by norm_num) hL
          _ ≤ Real.exp (x / 2) := by
            nlinarith [Real.two_mul_le_exp (x := x / 2)]
          _ = Real.exp (-(x / 2)) * Real.exp x := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (-(D + 2) * t) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (-2 * t) * Real.exp (-D * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ t⁻¹ ^ 2 * Real.exp (-D * t) :=
        mul_le_mul_of_nonneg_right (kkl_inverse_square_exp_lower t ht)
          (Real.exp_nonneg _)
)

/-- If coordinates outside `J` have influence at most `τ` and the
rate-weighted component energy at each coordinate is bounded by its
influence to the power `3/2`, then the omitted degree-at-most-`k` energy,
multiplied by `ρ^k`, is at most `√τ` times total influence.
[OD14, Thm. 9.28 (proof); §10.3, Friedgut's Junta Theorem]
This conditional formulation applies to heterogeneous finite products
and permits `ρ = 0`, `τ = 0`, and `k = 0`.

**Proof sketch.** Apply the weighted omission inequality to component
second moments. For every omitted coordinate, its influence is
nonnegative and at most `τ`; its three-halves power is its influence
times its square root, hence at most its influence times `√τ`.
Sum these bounds, include the remaining nonnegative coordinate
influences, and factor out `√τ`. -/
theorem lowDegree_omission_le_of_stable_bound {n : ℕ}
    (P : FiniteProduct.{u} n) (f : P.Point → ℝ)
    (J : Finset (Fin n)) (k : ℕ) (ρ τ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hτ : 0 ≤ τ)
    (houtside : ∀ i : Fin n, i ∉ J → P.influence i f ≤ τ)
    (hstable : ∀ i : Fin n,
      (∑ S : Finset (Fin n), if i ∈ S then
        ρ ^ S.card * P.expect (fun x => P.component S f x ^ 2) else 0) ≤
        P.influence i f ^ (3 / 2 : ℝ)) :
    ρ ^ k * (∑ S : Finset (Fin n),
      if S.card ≤ k ∧ ¬ S ⊆ J then
        P.expect (fun x => P.component S f x ^ 2) else 0) ≤
      Real.sqrt τ * P.totalInfluence f :=
  (by
  classical
  have hsquare (g : P.Point → ℝ) :
      0 ≤ P.expect (fun x => g x ^ 2) := by
    unfold FiniteProduct.expect
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
        (sq_nonneg _)
  have hinfluence (i : Fin n) : 0 ≤ P.influence i f :=
    hsquare (P.laplacian i f)
  calc
    ρ ^ k * (∑ S : Finset (Fin n),
        if S.card ≤ k ∧ ¬ S ⊆ J then
          P.expect (fun x => P.component S f x ^ 2) else 0) ≤
        ∑ i : Fin n, if i ∈ J then 0 else
          ∑ S : Finset (Fin n), if i ∈ S then
            ρ ^ S.card * P.expect (fun x => P.component S f x ^ 2) else 0 :=
      FiniteNorms.weighted_lowDegree_omission_le
        (fun S => P.expect (fun x => P.component S f x ^ 2))
        (fun S => hsquare (P.component S f)) J k ρ hρ hρ1
    _ ≤ ∑ i : Fin n, Real.sqrt τ * P.influence i f := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ J
      · rw [if_pos hi]
        exact mul_nonneg (Real.sqrt_nonneg τ) (hinfluence i)
      · rw [if_neg hi]
        calc
          _ ≤ P.influence i f ^ (3 / 2 : ℝ) := hstable i
          _ = P.influence i f * Real.sqrt (P.influence i f) := by
            rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
              Real.rpow_add_of_nonneg (hinfluence i) zero_le_one (by norm_num),
              Real.rpow_one, ← Real.sqrt_eq_rpow]
          _ ≤ P.influence i f * Real.sqrt τ :=
            mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (houtside i hi)) (hinfluence i)
          _ = Real.sqrt τ * P.influence i f := mul_comm _ _
    _ = Real.sqrt τ * P.totalInfluence f := by
      rw [FiniteProduct.totalInfluence, Finset.mul_sum]
)

/-- For positive `lam`, `I`, and `ε` with `lam ≤ 1/2`, the rate
`ρ = √lam / 3` lies in `(0, 1]`, and the threshold
`τ = (ε / (2 * I))² * ρ^(2 * k)` is positive. These parameters satisfy
`√τ * I = (ε/2) * ρ^k` and
`I/τ = (4 * I³ / ε²) * (9/lam)^k`.
[OD14, Thm. 9.28 (proof); §10.3, Friedgut's Junta Theorem]
This explicit bookkeeping formulation uses natural powers and imposes
no further restrictions on `ε`, `I`, or `k`.

**Proof sketch.** Positivity follows from the positive parameters,
and the bound on `lam` bounds the rate by one. The identity
`ρ² = lam/9` rewrites the even power. Taking square roots of the
nonnegative squares gives the error identity. Invert the threshold
and cancel the positive factors to obtain the coordinate-count identity. -/
theorem junta_threshold_parameters (lam I ε : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hI : 0 < I) (hε : 0 < ε) (k : ℕ) :
    let ρ : ℝ := Real.sqrt lam / 3
    let τ : ℝ := (ε / (2 * I)) ^ 2 * ρ ^ (2 * k)
    0 < ρ ∧ ρ ≤ 1 ∧ 0 < τ ∧
      Real.sqrt τ * I = (ε / 2) * ρ ^ k ∧
      I / τ = (4 * I ^ 3 / ε ^ 2) * (9 / lam) ^ k :=
  (by
  let ρ : ℝ := Real.sqrt lam / 3
  let τ : ℝ := (ε / (2 * I)) ^ 2 * ρ ^ (2 * k)
  change 0 < ρ ∧ ρ ≤ 1 ∧ 0 < τ ∧
    Real.sqrt τ * I = (ε / 2) * ρ ^ k ∧
    I / τ = (4 * I ^ 3 / ε ^ 2) * (9 / lam) ^ k
  have hρ : 0 < ρ :=
    div_pos (Real.sqrt_pos.mpr hlam) (by norm_num)
  have hρ1 : ρ ≤ 1 := by
    have hsqrt : Real.sqrt lam ≤ 1 :=
      Real.sqrt_le_one.mpr (hlamhalf.trans (by norm_num))
    dsimp only [ρ]
    linarith
  have hτ : 0 < τ := by
    dsimp only [τ]
    positivity
  have hρsq : ρ ^ 2 = lam / 9 := by
    dsimp only [ρ]
    rw [div_pow, Real.sq_sqrt hlam.le]
    norm_num
  have hτsquare : τ = ((ε / (2 * I)) * ρ ^ k) ^ 2 := by
    dsimp only [τ]
    rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
  refine ⟨hρ, hρ1, hτ, ?_, ?_⟩
  · rw [hτsquare, Real.sqrt_sq
      (show 0 ≤ (ε / (2 * I)) * ρ ^ k by positivity)]
    field_simp [hI.ne']
  · dsimp only [τ]
    rw [pow_mul, hρsq]
    simp only [div_pow, mul_pow]
    field_simp [hI.ne', hε.ne', hlam.ne']
    ring
)

/-- If `0 < lam ≤ 1/2`, `0 < ε ≤ 1`, `ε ≤ I`, and
`k ≤ 3 * I/ε`, then the junta-size expression
`(4 * I³ / ε²) * (9/lam)^k` is at most `(1/lam)^(100 * I/ε)`.
[OD14, Thm. 9.28 (proof); §9.6 and §10.3, Friedgut's Junta Theorem]
This formulation uses the deliberately generous explicit constant `100`
in place of the source's asymptotic constant. The left power is natural
and the right exponent is real.

**Proof sketch.** Set `t = I/ε ≥ 1` and `L = log(1/lam)`.
The logarithm bounds give `L ≥ 1/2` and `log(9/lam) ≤ 5 * L`.
Since `ε ≤ 1`, the polynomial factor is at most `4 * t³`.
The elementary bounds `2 * t ≤ exp t` and `t ≤ exp t` bound
this by `exp(3 * t)`. The degree factor is at most `exp(15 * t * L)`.
Their product is bounded by `exp(100 * t * L)` using `L ≥ 1/2`.
Rewrite this exponential as the asserted real power. -/
theorem junta_polynomial_absorption (lam I ε : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεI : ε ≤ I)
    (k : ℕ) (hk : (k : ℝ) ≤ 3 * (I / ε)) :
    (4 * I ^ 3 / ε ^ 2) * (9 / lam) ^ k ≤
      (1 / lam) ^ (100 * I / ε) :=
  (by
  let t : ℝ := I / ε
  let L : ℝ := Real.log (1 / lam)
  have ht : 1 ≤ t := (one_le_div hε).2 hεI
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  change (k : ℝ) ≤ 3 * t at hk
  obtain ⟨hLhalf, hLD, hD⟩ := kkl_log_parameters lam hlam hlamhalf
  change (1 / 2 : ℝ) ≤ L at hLhalf
  change L ≤ Real.log (9 / lam) at hLD
  change Real.log (9 / lam) ≤ 5 * L at hD
  have hD0 : 0 ≤ Real.log (9 / lam) := by linarith
  have hpoly : 4 * I ^ 3 / ε ^ 2 ≤ Real.exp (3 * t) := by
    calc
      4 * I ^ 3 / ε ^ 2 = 4 * ε * t ^ 3 := by
        dsimp only [t]
        field_simp [hε.ne']
      _ ≤ 4 * t ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_right hε1 (pow_nonneg ht0 3)]
      _ ≤ (2 * t) ^ 3 := by
        nlinarith [pow_nonneg ht0 3]
      _ ≤ Real.exp t ^ 3 :=
        pow_le_pow_left₀ (mul_nonneg (by norm_num) ht0)
          (Real.two_mul_le_exp (x := t)) 3
      _ = Real.exp (3 * t) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul t 3).symm
  have hdegree : (9 / lam) ^ k ≤ Real.exp (15 * t * L) := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (div_pos (by norm_num : (0 : ℝ) < 9) hlam)]
    apply Real.exp_le_exp.mpr
    calc
      Real.log (9 / lam) * (k : ℝ) ≤ Real.log (9 / lam) * (3 * t) :=
        mul_le_mul_of_nonneg_left hk hD0
      _ ≤ (5 * L) * (3 * t) :=
        mul_le_mul_of_nonneg_right hD (mul_nonneg (by norm_num) ht0)
      _ = 15 * t * L := by ring
  calc
    (4 * I ^ 3 / ε ^ 2) * (9 / lam) ^ k ≤
        Real.exp (3 * t) * Real.exp (15 * t * L) :=
      mul_le_mul hpoly hdegree
        (pow_nonneg (div_nonneg (by norm_num) hlam.le) _)
        (Real.exp_nonneg _)
    _ = Real.exp (3 * t + 15 * t * L) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (100 * t * L) :=
      Real.exp_le_exp.mpr
        (by nlinarith [mul_le_mul_of_nonneg_right hLhalf ht0])
    _ = (1 / lam) ^ (100 * I / ε) := by
      rw [Real.rpow_def_of_pos (div_pos zero_lt_one hlam)]
      congr 1
      dsimp only [t, L]
      ring
)

end BooleanAnalysis.Hypercontractivity.ComparisonAux
