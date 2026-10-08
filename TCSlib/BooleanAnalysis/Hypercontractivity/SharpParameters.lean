/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.Deriv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Parameter identities and bounds for sharp discrete hypercontractivity

## Main definitions

The scalar radius `sharpDiscreteRadius` is defined in
`TCSlib.BooleanAnalysis.Hypercontractivity.Parameters`.

## Main results

* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`:
  the sharp discrete radius lies strictly between zero and one when
  `q > 2` and `0 < lam < 1 / 2`.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_sinh`:
  the homogeneous two-point coefficient equals a hyperbolic sine ratio.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_pos_lt_one`:
  that coefficient lies strictly between zero and one for `1 < p < 2`.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_radius_sq`:
  the normalized coefficient equals the square of the sharp radius.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.concaveOn_tanh_nonneg`:
  the hyperbolic tangent is concave on the nonnegative half-line.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.sinh_ratio_antitoneOn`:
  hyperbolic sine ratios decrease with their positive argument.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_mono_bias`:
  the sharp radius increases with the lower atom mass below one half.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.sinh_scale_le`:
  hyperbolic sine contracts under scalar multiplication between zero and one.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_sq_le_balanced`:
  the squared sharp radius is at most the balanced one-bit constant.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*,
  Cambridge University Press, 2014, Theorem 10.18, equation (10.5),
  Exercise 10.18(a)–(b), Remark 10.19, and Exercise 10.20(a)–(c), equation (10.34).
-/

namespace BooleanAnalysis.Hypercontractivity

namespace SharpDiscrete

/-- For `q > 2` and `0 < lam < 1 / 2`, the sharp discrete hypercontractive
radius is strictly positive and strictly less than one.
[OD14, Theorem 10.18, equation (10.5)].

**Proof sketch.** The logarithm `u = log ((1 - lam) / lam)` is positive
because its argument exceeds one. The conjugate exponent `q / (q - 1)`
is positive and smaller than `q`, so
`0 < u / q < u / (q / (q - 1))`. Strict monotonicity of `sinh` shows that
the numerator and denominator in the squared radius are positive, with
the numerator smaller than the denominator. Their ratio, and hence its
square root, lies strictly between zero and one. -/
theorem radius_pos_lt_one (q lam : ℝ) (hq : 2 < q)
    (hlam0 : 0 < lam) (hlamhalf : lam < 1 / 2) :
    0 < sharpDiscreteRadius q lam ∧ sharpDiscreteRadius q lam < 1 := by
  let u := Real.log ((1 - lam) / lam)
  have hu : 0 < u := by
    apply Real.log_pos
    apply (lt_div_iff₀ hlam0).2
    linarith
  have hq0 : 0 < q := by linarith
  have hqsub : 0 < q - 1 := by linarith
  have hconj0 : 0 < q / (q - 1) := div_pos hq0 hqsub
  have hconj : q / (q - 1) < q := by
    apply (div_lt_iff₀ hqsub).2
    nlinarith
  have hnum : 0 < Real.sinh (u / q) :=
    Real.sinh_pos_iff.2 (div_pos hu hq0)
  have hden : 0 < Real.sinh (u / (q / (q - 1))) :=
    Real.sinh_pos_iff.2 (div_pos hu hconj0)
  have hlt : Real.sinh (u / q) < Real.sinh (u / (q / (q - 1))) :=
    Real.sinh_lt_sinh.2 (div_lt_div_of_pos_left hu hconj0 hconj)
  have hr0 := div_pos hnum hden
  have hr1 : Real.sinh (u / q) / Real.sinh (u / (q / (q - 1))) < 1 :=
    (div_lt_one hden).2 hlt
  change 0 < Real.sqrt (Real.sinh (u / q) / Real.sinh (u / (q / (q - 1)))) ∧
    Real.sqrt (Real.sinh (u / q) / Real.sinh (u / (q / (q - 1)))) < 1
  constructor
  · exact Real.sqrt_pos.2 hr0
  · apply (Real.sqrt_lt hr0.le (by norm_num : (0 : ℝ) ≤ 1)).2
    simpa using hr1

/--
For positive real numbers `α < β`, the homogeneous biased sharp coefficient equals
`sinh ((p - 1) * log (β / α)) / sinh (log (β / α))`.

Source: [OD14, Exercise 10.20(a), equation (10.34), Theorem 10.18].

Deviation from the source: this algebraic identity holds for arbitrary real `p`
and does not require the normalization `α ^ p + β ^ p = 1`. It asserts no
positivity or contraction bound for arbitrary `p`.

**Proof sketch.** Set `T = β / α > 1`. Expand each hyperbolic sine as
`(exp x - exp (-x)) / 2`. Since `exp (log T) = T`, the numerator becomes
`(T ^ (p - 1) - (T ^ (p - 1))⁻¹) / 2`, and the denominator becomes
`(T - T⁻¹) / 2`. The laws of real powers on positive bases give
`T ^ (p - 1) = (β ^ p / α ^ p) / T`,
`α ^ (2 - p) = α² / α ^ p`, and
`β ^ (2 - p) = β² / β ^ p`.
Substitute these identities into the two ratios. Positivity and `α < β`
ensure that the powers, square difference, and hyperbolic sine denominator
are nonzero. Clearing denominators leaves a polynomial identity.
-/
theorem bias_coefficient_eq_sinh {p α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
        (α ^ (2 : ℕ) - β ^ (2 : ℕ)) =
      Real.sinh ((p - 1) * Real.log (β / α)) /
        Real.sinh (Real.log (β / α)) := by
  have hβ : 0 < β := lt_trans hα hαβ
  have hratio : 1 < β / α := by
    simpa only [div_self hα.ne'] using div_lt_div_of_pos_right hαβ hα
  have hsinh : Real.sinh (Real.log (β / α)) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (Real.log_pos hratio))
  have hsq : α ^ (2 : ℕ) - β ^ (2 : ℕ) ≠ 0 :=
    ne_of_lt (sub_neg.mpr ((sq_lt_sq₀ hα.le hβ.le).2 hαβ))
  have ha : α ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hα p)
  have hb : β ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hβ p)
  have hexp : Real.exp ((p - 1) * Real.log (β / α)) =
      (β / α) ^ (p - 1) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (div_pos hβ hα)]
  apply (div_eq_div_iff hsq hsinh).2
  simp only [Real.sinh_eq, Real.exp_neg, hexp,
    Real.exp_log (div_pos hβ hα),
    Real.rpow_sub_one (div_ne_zero hβ.ne' hα.ne') p,
    Real.div_rpow hβ.le hα.le p,
    Real.rpow_sub hα 2 p, Real.rpow_sub hβ 2 p, Real.rpow_two]
  field_simp [hα.ne', hβ.ne', ha, hb] <;> ring

/-- The homogeneous bias coefficient lies strictly between zero and one when
`1 < p < 2` and `0 < α < β`.

[OD14, Exercise 10.20(a)–(c), equation (10.34), Theorem 10.18].

**Source extension.** The source takes `α = λ^(1/p)` and
`β = (1 - λ)^(1/p)`, with `α^p + β^p = 1`. This declaration removes that
normalization and proves the homogeneous coefficient bound for arbitrary
positive `α < β`. It retains the source's range of `p` and asserts no norm
inequality.

**Proof sketch.** Use `bias_coefficient_eq_sinh` to express the coefficient as
`sinh ((p - 1) * u) / sinh u`, where `u = log (β / α) > 0`.
The assumptions imply `0 < (p - 1) * u < u`. Positivity and strict
monotonicity of `sinh` therefore place the numerator strictly between zero
and the positive denominator, proving both quotient bounds. -/
theorem bias_coefficient_pos_lt_one {p α β : ℝ}
    (hp₁ : 1 < p) (hp₂ : p < 2) (hα : 0 < α) (hαβ : α < β) :
    0 < (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
          (α ^ (2 : ℕ) - β ^ (2 : ℕ)) ∧
    (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
          (α ^ (2 : ℕ) - β ^ (2 : ℕ)) < 1 := by
  rw [bias_coefficient_eq_sinh hα hαβ]
  have hu : 0 < Real.log (β / α) :=
    Real.log_pos ((lt_div_iff₀ hα).2 (by simpa using hαβ))
  have hpu : 0 < (p - 1) * Real.log (β / α) :=
    mul_pos (sub_pos.mpr hp₁) hu
  have hlt : (p - 1) * Real.log (β / α) < Real.log (β / α) := by
    nlinarith [mul_pos (sub_pos.mpr hp₂) hu]
  have hs : 0 < Real.sinh (Real.log (β / α)) :=
    Real.sinh_pos_iff.mpr hu
  constructor
  · exact div_pos (Real.sinh_pos_iff.mpr hpu) hs
  · exact (div_lt_one hs).mpr (Real.sinh_lt_sinh.mpr hlt)

/--
For normalized positive parameters `α < β` and `1 < p < 2`, the coefficient in
O'Donnell's two-point inequality equals the square of the sharp discrete radius
at `q = p / (p - 1)` and `λ = α ^ p`.

[OD14, Exercise 10.20(a), equation (10.34); Theorem 10.18, equation (10.5)]

**Proof sketch.** Normalization gives `1 - α ^ p = β ^ p`, so the logarithmic
odds equal `p * log (β / α)`. The conjugate exponent of `p / (p - 1)` is `p`;
hence the two hyperbolic-sine arguments in the radius formula become
`(p - 1) * log (β / α)` and `log (β / α)`. The previously established
hyperbolic-sine identity identifies their ratio with the coefficient. This
ratio is positive by the coefficient bounds, so squaring its square root
recovers the coefficient.
-/
theorem bias_coefficient_eq_radius_sq {p α β : ℝ}
    (hp₁ : 1 < p) (hp₂ : p < 2) (hα : 0 < α) (hαβ : α < β)
    (hnorm : α ^ p + β ^ p = 1) :
    (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
        (α ^ (2 : ℕ) - β ^ (2 : ℕ)) =
      sharpDiscreteRadius (p / (p - 1)) (α ^ p) ^ (2 : ℕ) := by
  have hp : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₁)
  have hpm : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp₁)
  -- Normalization expresses the log odds through the bias ratio.
  have hlog : Real.log ((1 - α ^ p) / α ^ p) = p * Real.log (β / α) := by
    rw [show 1 - α ^ p = β ^ p by linarith]
    rw [← Real.div_rpow (le_of_lt (lt_trans hα hαβ)) (le_of_lt hα) p,
      Real.log_rpow (div_pos (lt_trans hα hαβ) hα) p]
  have hq : p / (p - 1) / (p / (p - 1) - 1) = p := by
    field_simp [hpm] <;> ring
  have hargs :
      p * Real.log (β / α) / (p / (p - 1)) =
        (p - 1) * Real.log (β / α) ∧
      p * Real.log (β / α) / p = Real.log (β / α) := by
    constructor <;> field_simp [hp, hpm] <;> ring
  have hpos := (bias_coefficient_pos_lt_one hp₁ hp₂ hα hαβ).1
  rw [bias_coefficient_eq_sinh hα hαβ] at hpos ⊢
  -- Positivity allows us to remove the squared square root.
  rw [sharpDiscreteRadius, hlog, hq, hargs.1, hargs.2,
    Real.sq_sqrt (le_of_lt hpos)]

/-- The hyperbolic tangent is concave on the nonnegative half-line, including
the endpoint zero.

This is a technical calculus ingredient for the sharp-radius monotonicity
argument in [OD14, Exercise 10.18(a)]. The source does not separately state
this concavity lemma.

**Proof sketch.** Differentiate the quotient of hyperbolic sine by hyperbolic
cosine. Positivity of hyperbolic cosine and the identity
`cosh x ^ 2 - sinh x ^ 2 = 1` give derivative `1 / cosh x ^ 2` at every real
point, hence continuity and differentiability. Hyperbolic cosine is positive
and increasing on the nonnegative half-line, so this derivative is antitone
there. The calculus criterion for an antitone derivative yields concavity
on the closed convex half-line. -/
theorem concaveOn_tanh_nonneg :
    ConcaveOn ℝ (Set.Ici 0) Real.tanh := by
  have hderiv (x : ℝ) :
      HasDerivAt Real.tanh (1 / Real.cosh x ^ (2 : ℕ)) x := by
    simpa only [← Real.tanh_eq_sinh_div_cosh, ← pow_two,
      Real.cosh_sq_sub_sinh_sq] using
      (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x)
        (Real.cosh_pos x).ne'
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici _)
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
    (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
  intro x hx y hy hxy
  rw [(hderiv x).deriv, (hderiv y).deriv]
  exact one_div_le_one_div_of_le (pow_pos (Real.cosh_pos x) 2)
    ((sq_le_sq₀ (Real.cosh_pos x).le (Real.cosh_pos y).le).2
      (Real.cosh_strictMonoOn.monotoneOn
        (interior_subset hx) (interior_subset hy) hxy))
/-- For `0 ≤ a ≤ 1`, the ratio `sinh (a * u) / sinh u` is antitone for `u > 0`.

This is a technical scalar ingredient for sharp-radius bias monotonicity in
[OD14, Exercise 10.18(a)]. The parameter range includes the endpoints:
`a = 0` gives the zero function and `a = 1` gives the constant-one function.

**Proof sketch.** Concavity of hyperbolic tangent on the nonnegative half-line,
applied to the convex combination of `u` and zero with weights `a` and `1 - a`,
gives `a * tanh u ≤ tanh (a * u)`. Multiplying by the positive hyperbolic cosine
denominators shows that the numerator of the derivative of the hyperbolic sine
ratio is nonpositive. Its denominator is the positive square of `sinh u` for
`u > 0`. Apply the calculus criterion for a nonpositive derivative on this
convex interval to obtain antitonicity. -/
theorem sinh_ratio_antitoneOn (a : ℝ) (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1) :
    AntitoneOn (fun u : ℝ => Real.sinh (a * u) / Real.sinh u) (Set.Ioi 0) := by
  have hderiv (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun t => Real.sinh (a * t) / Real.sinh t)
        ((a * Real.cosh (a * u) * Real.sinh u -
          Real.sinh (a * u) * Real.cosh u) / Real.sinh u ^ (2 : ℕ)) u := by
    simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id u).const_mul a).sinh).fun_div
        (Real.hasDerivAt_sinh u) (Real.sinh_pos_iff.mpr hu).ne'
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0 : ℝ))
    (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hderiv u (interior_subset hu)).hasDerivWithinAt) ?_
  intro u hu
  have hbound : a * Real.tanh u ≤ Real.tanh (a * u) := by
    simpa only [smul_eq_mul, Real.tanh_zero, mul_zero, add_zero] using
      concaveOn_tanh_nonneg.2
        (show u ∈ Set.Ici 0 from le_of_lt (interior_subset hu))
        (show (0 : ℝ) ∈ Set.Ici 0 from by simp)
        ha_nonneg (sub_nonneg.mpr ha_le_one) (show a + (1 - a) = 1 by ring)
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    ← mul_div_assoc] at hbound
  apply div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  nlinarith only
    [(div_le_div_iff₀ (Real.cosh_pos u) (Real.cosh_pos (a * u))).mp hbound]

/-- For `q > 2` and `0 < lam ≤ gam < 1 / 2`, the sharp discrete
hypercontractive radius at `lam` is at most its value at `gam`.

[OD14, Exercise 10.18(a); Theorem 10.18, equation (10.5)]. The strict upper
bound `gam < 1 / 2` is retained because the current totalized radius formula
evaluates to zero at `1 / 2`.

**Proof sketch.** Set `a = 1 / (q - 1)`, which lies between zero and one,
and divide the logarithmic odds at each bias by the positive conjugate
exponent `q / (q - 1)`. These positive arguments decrease as the bias
increases. The expression under the square root in the radius formula is
the ratio `sinh (a * t) / sinh t`. Its antitonicity therefore makes the
expression nondecreasing in the bias. Monotonicity of the square root gives
the stated radius inequality. -/
theorem radius_mono_bias (q lam gam : ℝ) (hq : 2 < q)
    (hlam_pos : 0 < lam) (hlam_le_gam : lam ≤ gam)
    (hgam_lt_half : gam < 1 / 2) :
    sharpDiscreteRadius q lam ≤ sharpDiscreteRadius q gam := by
  have hqsub : 0 < q - 1 := by linarith
  have hconj : 0 < q / (q - 1) := div_pos (by linarith) hqsub
  let a : ℝ := 1 / (q - 1)
  let t : ℝ → ℝ := fun x => Real.log ((1 - x) / x) / (q / (q - 1))
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    constructor
    · exact (div_pos zero_lt_one hqsub).le
    · exact (div_le_iff₀ hqsub).2 (by linarith)
  have htpos (x : ℝ) (hx : 0 < x) (hxhalf : x < 1 / 2) : 0 < t x := by
    exact div_pos (Real.log_pos ((lt_div_iff₀ hx).2 (by linarith))) hconj
  have horder : t gam ≤ t lam := by
    have hgampos : 0 < gam := lt_of_lt_of_le hlam_pos hlam_le_gam
    refine div_le_div_of_nonneg_right (Real.log_le_log ?_ ?_) hconj.le
    · exact div_pos (by linarith) hgampos
    · exact (div_le_div_iff₀ hgampos hlam_pos).2 (by nlinarith)
  have hargs (z : ℝ) : a * (z / (q / (q - 1))) = z / q := by
    dsimp only [a]
    field_simp [hqsub.ne', (show q ≠ 0 by linarith)] <;> ring
  simpa only [sharpDiscreteRadius, t, hargs] using
    Real.sqrt_le_sqrt
      (sinh_ratio_antitoneOn a ha.1 ha.2
        (htpos gam (lt_of_lt_of_le hlam_pos hlam_le_gam) hgam_lt_half)
        (htpos lam hlam_pos (lt_of_le_of_lt hlam_le_gam hgam_lt_half)) horder)

/-- For `0 ≤ a ≤ 1` and `0 ≤ u`, hyperbolic sine satisfies
`sinh (a * u) ≤ a * sinh u`, including both parameter endpoints and zero input.

This is a technical convexity ingredient for the balanced sharp-radius
comparison in [OD14, Exercise 10.18(b); Remark 10.19], supporting
[OD14, Theorem 10.18]. It is formulated as a scalar inequality; the source
does not separately state this helper.

**Proof sketch.** Hyperbolic sine is continuous and differentiable, with
derivative equal to hyperbolic cosine. Monotonicity of hyperbolic cosine on
the nonnegative half-line gives convexity of hyperbolic sine there by the
derivative criterion. Apply convexity to `u` and zero with weights `a` and
`1 - a`, then simplify using `sinh 0 = 0`. -/
theorem sinh_scale_le (a u : ℝ) (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1)
    (hu_nonneg : 0 ≤ u) :
    Real.sinh (a * u) ≤ a * Real.sinh u := by
  have hconvex : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
    refine MonotoneOn.convexOn_of_deriv (convex_Ici _)
      Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn ?_
    intro x hx y hy hxy
    simpa only [Real.deriv_sinh] using
      Real.cosh_strictMonoOn.monotoneOn (interior_subset hx) (interior_subset hy) hxy
  simpa only [smul_eq_mul, Real.sinh_zero, mul_zero, add_zero] using
    hconvex.2 (show u ∈ Set.Ici 0 from hu_nonneg)
      (show (0 : ℝ) ∈ Set.Ici 0 from by simp)
      ha_nonneg (sub_nonneg.mpr ha_le_one) (show a + (1 - a) = 1 by ring)

/-- For `q > 2` and `0 < lam < 1 / 2`, the square of the sharp discrete
hypercontractive radius is at most the balanced constant `1 / (q - 1)`.

This is the squared-radius formulation of the balanced comparison in
[OD14, Remark 10.19; Exercise 10.18(b)], using the radius formula from
[OD14, Theorem 10.18, equation (10.5)]. The bias remains strictly below
`1 / 2`, and the right-hand side is the balanced comparison constant.

**Proof sketch.** The logarithmic odds `u` are positive. Set
`t = u / (q / (q - 1))` and `a = 1 / (q - 1)`, so `t > 0`, `0 < a < 1`,
and `u / q = a * t`. The hyperbolic sine scaling bound gives
`sinh (a * t) ≤ a * sinh t`. Divide by the positive denominator `sinh t`
to bound the ratio by `1 / (q - 1)`. Its nonnegativity allows squaring
the square root in the radius formula, identifying this ratio with the
squared radius. -/
theorem radius_sq_le_balanced (q lam : ℝ) (hq : 2 < q)
    (hlam_pos : 0 < lam) (hlam_lt_half : lam < 1 / 2) :
    sharpDiscreteRadius q lam ^ (2 : ℕ) ≤ 1 / (q - 1) := by
  let u : ℝ := Real.log ((1 - lam) / lam)
  let t : ℝ := u / (q / (q - 1))
  let a : ℝ := 1 / (q - 1)
  have hqsub : 0 < q - 1 := by linarith
  have hu : 0 < u :=
    Real.log_pos ((lt_div_iff₀ hlam_pos).2 (by linarith))
  have ht : 0 < t := div_pos hu (div_pos (by linarith) hqsub)
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    constructor
    · exact (div_pos zero_lt_one hqsub).le
    · exact (div_le_iff₀ hqsub).2 (by linarith)
  have hargs : a * t = u / q := by
    dsimp only [a, t]
    field_simp [hqsub.ne', (show q ≠ 0 by linarith)] <;> ring
  have hratio : 0 < Real.sinh (u / q) / Real.sinh t :=
    Real.sqrt_pos.1 (radius_pos_lt_one q lam hq hlam_pos hlam_lt_half).1
  change Real.sqrt (Real.sinh (u / q) / Real.sinh t) ^ (2 : ℕ) ≤ a
  rw [Real.sq_sqrt hratio.le, ← hargs]
  exact (div_le_iff₀ (Real.sinh_pos_iff.mpr ht)).2
    (sinh_scale_le a t ha.1 ha.2 ht.le)

end SharpDiscrete

end BooleanAnalysis.Hypercontractivity
