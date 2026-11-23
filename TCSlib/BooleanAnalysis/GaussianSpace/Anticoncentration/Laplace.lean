/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.WeightedRemez
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial estimates for the Laplace probability density

## Main definitions

No new definitions.

## Main results

* `lintegral_mul_laplace_eq_half_mul_add`: split a nonnegative weighted
  Laplace integral into two positive-half-line exponential integrals.
* `lintegral_laplace_eq_one`: the Laplace density has total mass one.
* `lintegral_sq_eval_laplace_le_of_bound_on_set_of_exp_mass`: a half-line
  sublevel mass controls the square moment on the whole real line.
* `laplace_mass_smallBall_le_of_le_lintegral_sq`: a squared-norm lower bound
  gives a whole-line polynomial small-ball estimate.
* `lintegral_mul_scaled_laplace_eq`: affine substitution for Laplace integrals.

## References

* [CW01] A. Carbery and J. Wright, *Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn*, Mathematical Research Letters
  8 (2001), 233–248, §4. The result below is technical integration glue
  for the Laplace specialization of the Remez method.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- The integral of a measurable nonnegative extended-real function
against the Laplace probability density equals one half the sum of its
positive-half-line exponential integral and that of its reflection.

This is technical splitting and reflection bookkeeping for the
Laplace specialization of the method in [CW01, §4], rather than a
separately numbered result there. Infinite integrals are permitted;
no integrability or finiteness hypothesis is needed.

**Proof sketch.** Split the real line into the nonnegative and negative
half-lines. Negation preserves volume and carries the negative part
to the positive half-line, with the endpoint difference negligible.
Simplify the absolute values on that half-line and factor out one half. -/
theorem lintegral_mul_laplace_eq_half_mul_add
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ x : ℝ, f x * ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))) =
      ENNReal.ofReal (1 / 2 : ℝ) *
        ((∫⁻ t in Ici (0 : ℝ), f t * ENNReal.ofReal (Real.exp (-t))) +
          ∫⁻ t in Ici (0 : ℝ), f (-t) * ENNReal.ofReal (Real.exp (-t))) :=
  (by
  have hsplit (f : ℝ → ENNReal) (hf : Measurable f) :
      (∫⁻ x : ℝ, f x * ENNReal.ofReal (Real.exp (-|x|))) =
        (∫⁻ t in Ici (0 : ℝ), f t * ENNReal.ofReal (Real.exp (-t))) +
        ∫⁻ t in Ici (0 : ℝ), f (-t) * ENNReal.ofReal (Real.exp (-t)) := by
    rw [← lintegral_add_compl (fun x => f x * ENNReal.ofReal (Real.exp (-|x|))) measurableSet_Ici]
    congr 1
    · apply setLIntegral_congr_fun measurableSet_Ici
      intro x hx
      change f x * ENNReal.ofReal (Real.exp (-|x|)) = _
      rw [abs_of_nonneg (show 0 ≤ x from hx)]
    · rw [compl_Ici]
      have href := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
        (s := Iio (0 : ℝ)) measurableSet_Iio
        (f := fun x => f x * ENNReal.ofReal (Real.exp (-|x|))) (by fun_prop)
      have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by
        ext x
        simp
      rw [hpre] at href
      rw [← href, setLIntegral_congr (Ioi_ae_eq_Ici : Ioi (0 : ℝ) =ᵐ[volume] Ici (0 : ℝ))]
      apply setLIntegral_congr_fun measurableSet_Ici
      intro t ht
      change f (-t) * ENNReal.ofReal (Real.exp (-|-t|)) = _
      rw [abs_neg, abs_of_nonneg (show 0 ≤ t from ht)]
  calc
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        ∫⁻ x : ℝ, f x * ENNReal.ofReal (Real.exp (-|x|)) := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    _ = _ := by rw [hsplit f hf]
)

/-- The Laplace probability density `exp(-|x|)/2` has total mass one
on the real line.

This is shared normalization glue for the whole-line Laplace estimates.

**Proof sketch.** Apply the Laplace split identity to the constant
function one. Each positive-half-line exponential integral is one
by the shared raw exponential mass formula, so the result is
one half times two. -/
theorem lintegral_laplace_eq_one :
    (∫⁻ x : ℝ, ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) ∂volume) = 1 :=
  (by
    have h := lintegral_mul_laplace_eq_half_mul_add (fun _ => 1) measurable_const
    calc
      _ = ENNReal.ofReal (1 / 2 : ℝ) * (1 + 1) := by
        simpa only [one_mul, lintegral_exp_neg_Ici_eq_one] using h
      _ = 1 := by
        rw [mul_add, mul_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num
)


/-- A polynomial bounded by `M` on a measurable set of positive
raw exponential mass in the nonnegative half-line has its full
Laplace probability square integral bounded by
`M² * (16 * exp 2 / m)^(2d) * exp 1 * (2d)!`.

This is cross-half moment bookkeeping for the Remez method in
[CW01, §4], with the explicit coarse constant used here. The set
controlling the polynomial lies on one half-line, while the square
integral is over the whole real line. No positive-degree or
moment-finiteness hypothesis is needed.

**Proof sketch.** The whole-line weighted Remez envelope bounds the
square of the polynomial by a constant times `(1 + |x|)^(2d)`.
Integrate against the Laplace probability density. The Laplace split
identity makes the even envelope moment equal to its positive-half-line
exponential moment, since the two equal contributions cancel the
factor one half. Apply the existing shifted exponential moment bound. -/
theorem lintegral_sq_eval_laplace_le_of_bound_on_set_of_exp_mass
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d)
    (E : Set ℝ) (hE : MeasurableSet E) (hnonneg : E ⊆ Ici 0)
    (M m : ℝ) (hM : 0 ≤ M) (hm : 0 < m)
    (hvalue : ∀ y ∈ E, |p.eval y| ≤ M)
    (hmass : ENNReal.ofReal m ≤
      ∫⁻ y in E, ENNReal.ofReal (Real.exp (-y)) ∂volume) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((p.eval x) ^ 2) *
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) ∂volume) ≤
      ENNReal.ofReal (M ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d) *
        Real.exp 1 * ((2 * d).factorial : ℝ)) :=
  (by
  let C : ℝ := M ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsquare (x : ℝ) : (p.eval x) ^ 2 ≤ C * (1 + |x|) ^ (2 * d) := by
    have h := abs_eval_le_of_bound_on_set_of_exp_mass_all_real
      p d hp E hE hnonneg M m hM hm hvalue hmass x
    rw [show 16 * Real.exp 2 * (1 + |x|) / m =
      (16 * Real.exp 2 / m) * (1 + |x|) by ring] at h
    have hsq := pow_le_pow_left₀ (abs_nonneg (p.eval x)) h 2
    simpa only [C, sq_abs, mul_pow, ← pow_mul, Nat.mul_comm d 2, mul_assoc] using hsq
  have hmoment :
      (∫⁻ x : ℝ, ENNReal.ofReal ((1 + |x|) ^ (2 * d)) *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))) ≤
      ENNReal.ofReal (Real.exp 1 * ((2 * d).factorial : ℝ)) := by
    rw [lintegral_mul_laplace_eq_half_mul_add _ (by fun_prop)]
    simp only [abs_neg]
    have hhalf :
        (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal ((1 + |t|) ^ (2 * d)) *
          ENNReal.ofReal (Real.exp (-t))) =
        ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal ((1 + t) ^ (2 * d)) *
          ENNReal.ofReal (Real.exp (-t)) := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro t ht
      dsimp only
      rw [abs_of_nonneg ht]
    rw [hhalf]
    calc
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) *
          (ENNReal.ofReal (Real.exp 1 * ((2 * d).factorial : ℝ)) +
            ENNReal.ofReal (Real.exp 1 * ((2 * d).factorial : ℝ))) :=
        mul_le_mul_left' (add_le_add (lintegral_one_add_pow_mul_exp_neg_le (2 * d))
          (lintegral_one_add_pow_mul_exp_neg_le (2 * d))) _
      _ = _ := by
        rw [mul_add, ← add_mul, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal C *
        (ENNReal.ofReal ((1 + |x|) ^ (2 * d)) *
          ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))) := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ ENNReal.ofReal (C * (1 + |x|) ^ (2 * d)) *
            ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) :=
          mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hsquare x)) _
        _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]
    _ = ENNReal.ofReal C * ∫⁻ x : ℝ,
        ENNReal.ofReal ((1 + |x|) ^ (2 * d)) *
          ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.exp 1 * ((2 * d).factorial : ℝ)) :=
      mul_le_mul_left' hmoment _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      dsimp only [C]
      ring
)


/-- A real polynomial of degree at most `d ≥ 1`, whose squared integral
under the Laplace probability density `exp(-|x|)/2` is at least
`a² > 0`, has small-ball probability at most
`32 * exp 3 * d * (ε / a)^(1/d)` for every `ε > 0`.

This is a coarse explicit consequence of the Remez method in
[CW01, §4], specialized to the standard Laplace density. No separate
finiteness or equality normalization of the square integral is required.

**Proof sketch.** If the small-ball probability is positive, one of the
two half-lines has unnormalized exponential small-ball mass at least
that probability. Reflect the polynomial when needed. The whole-line
weighted Remez envelope from this one half-line controls the polynomial
at every real point. Square it and integrate against the Laplace
density. Reflection and the one-sided exponential moment estimate
bound the moment of `(1 + |x|)^(2d)`; its two equal half-line
contributions cancel the density factor one half. Combine the resulting
upper bound with `a²`, bound `(2d)!` by `(2d)^(2d)`, and take the
positive degree root. This gives the stated constant without requiring
the small-ball mass and the squared norm to be large on the same half. -/
theorem laplace_mass_smallBall_le_of_le_lintegral_sq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a : ℝ) (ha : 0 < a)
    (hlower :
      ENNReal.ofReal (a ^ 2) ≤
        ∫⁻ x : ℝ,
          ENNReal.ofReal ((p.eval x) ^ 2) *
            ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) ∂volume)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | |p.eval x| ≤ ε},
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) ∂volume).toReal ≤
      32 * Real.exp 3 * (d : ℝ) * (ε / a) ^ (1 / (d : ℝ)) :=
  (by
  classical
  let E : Set ℝ := {x : ℝ | |p.eval x| ≤ ε}
  have hE : MeasurableSet E := measurableSet_le p.continuous.abs.measurable measurable_const
  let Eneg := (Neg.neg : ℝ → ℝ) ⁻¹' E
  have hEneg : MeasurableSet Eneg := hE.preimage measurable_neg
  let mplus := ∫⁻ x in E ∩ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-x))
  let mminus := ∫⁻ x in Eneg ∩ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-x))
  let S := ∫⁻ x in E, ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))
  have hsplit : S = ENNReal.ofReal (1 / 2 : ℝ) * (mplus + mminus) := by
    have h := lintegral_mul_laplace_eq_half_mul_add
      (E.indicator (fun _ => 1)) (measurable_const.indicator hE)
    have hi : (fun x : ℝ => E.indicator (fun _ => (1 : ENNReal)) (-x)) =
        Eneg.indicator (fun _ => 1) := by
      funext x
      exact (Set.indicator_comp_right Neg.neg).symm
    simp_rw [show ∀ x : ℝ, E.indicator (fun _ => (1 : ENNReal)) (-x) =
      Eneg.indicator (fun _ => 1) x from fun x => congrFun hi x] at h
    have hprod (U : Set ℝ) (g : ℝ → ENNReal) (x : ℝ) :
        U.indicator (fun _ => 1) x * g x = U.indicator g x := by
      simpa only [one_mul] using
        (Set.indicator_mul_left U (fun _ => (1 : ENNReal)) g (i := x)).symm
    simp_rw [hprod E (fun x => ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))),
      hprod E (fun x => ENNReal.ofReal (Real.exp (-x))),
      hprod Eneg (fun x => ENNReal.ofReal (Real.exp (-x)))] at h
    rw [setLIntegral_indicator hE, setLIntegral_indicator hEneg, lintegral_indicator hE] at h
    exact h
  have hexp : (∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-x))) = 1 :=
    lintegral_exp_neg_Ici_eq_one
  have hplus : mplus ≤ 1 := by
    rw [← hexp]
    exact lintegral_mono_set Set.inter_subset_right
  have hminus : mminus ≤ 1 := by
    rw [← hexp]
    exact lintegral_mono_set Set.inter_subset_right
  have hplusfin : mplus ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hplus
  have hminusfin : mminus ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hminus
  let m := S.toReal
  change m ≤ _
  by_cases hm : 0 < m
  · have hmean : m = (mplus.toReal + mminus.toReal) / 2 := by
      dsimp [m]
      rw [hsplit, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
        ENNReal.toReal_add hplusfin hminusfin]
      ring
    have hchoice : m ≤ mplus.toReal ∨ m ≤ mminus.toReal := by
      by_contra! h
      linarith
    have hupper :
        (∫⁻ x : ℝ, ENNReal.ofReal ((p.eval x) ^ 2) *
          ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))) ≤
        ENNReal.ofReal (ε ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d) *
          Real.exp 1 * ((2 * d).factorial : ℝ)) := by
      rcases hchoice with hlarge | hlarge
      · apply lintegral_sq_eval_laplace_le_of_bound_on_set_of_exp_mass
          p d hp (E ∩ Ici 0) (hE.inter measurableSet_Ici)
          (fun y hy => hy.2) ε m hε.le hm (fun y hy => hy.1)
        exact (ENNReal.ofReal_le_ofReal hlarge).trans_eq (ENNReal.ofReal_toReal hplusfin)
      · let q : Polynomial ℝ := p.comp (-Polynomial.X)
        have heval (x : ℝ) : q.eval x = p.eval (-x) := by
          simp only [q, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
        have hq : q.natDegree ≤ d := by
          have hdeg : (-Polynomial.X : Polynomial ℝ).natDegree = 1 := by
            rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
          exact Polynomial.natDegree_comp_le.trans (by simpa only [hdeg, mul_one] using hp)
        have hbound := lintegral_sq_eval_laplace_le_of_bound_on_set_of_exp_mass
          q d hq (Eneg ∩ Ici 0) (hEneg.inter measurableSet_Ici)
          (fun y hy => hy.2) ε m hε.le hm
          (fun y hy => by rw [heval]; exact hy.1)
          ((ENNReal.ofReal_le_ofReal hlarge).trans_eq (ENNReal.ofReal_toReal hminusfin))
        have href := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp
          (f := fun x => ENNReal.ofReal ((p.eval x) ^ 2) *
            ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))) (by fun_prop)
        have hsq :
            (∫⁻ x : ℝ, ENNReal.ofReal ((q.eval x) ^ 2) *
              ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))) =
            ∫⁻ x : ℝ, ENNReal.ofReal ((p.eval x) ^ 2) *
              ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|)) := by
          simpa only [heval, abs_neg] using href
        exact hsq ▸ hbound
    apply le_exp_mul_degree_mul_rpow_of_sq_le_factorial_bound d hd a ε m ha hε hm
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlower.trans hupper)
  · exact (le_of_not_gt hm).trans (by positivity)
)


/-- An integral against a shifted Laplace probability density of
positive scale `k` equals the corresponding standard Laplace integral
after the substitution `x = t / k + c`.

This is technical affine change-of-variables glue for the Laplace
specialization of the Remez method in [CW01, §4]. The function may take
infinite values and no finiteness or integrability assumption is needed.

**Proof sketch.** The affine map `x ↦ k * (x-c)` pushes Lebesgue volume
forward to `k⁻¹` times volume. Apply the nonnegative integral map
formula and simplify the absolute value using `k > 0`. The Jacobian
factor cancels the factor `k` in the scaled probability density.
All cancelled factors are finite and strictly positive, so the
identity also holds when the remaining integral is infinite. -/
theorem lintegral_mul_scaled_laplace_eq
    (f : ℝ → ENNReal) (hf : Measurable f) (c k : ℝ) (hk : 0 < k) :
    (∫⁻ x : ℝ, f x * ENNReal.ofReal ((k / 2) * Real.exp (-k * |x - c|))) =
      ∫⁻ t : ℝ, f (t / k + c) *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|)) :=
  (by
    let G : ℝ → ENNReal := fun t =>
      f (t / k + c) * ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|))
    have hG : Measurable G := (hf.comp (by fun_prop)).mul (by fun_prop)
    have hmap : Measure.map (fun x : ℝ => k * (x - c)) volume =
        ENNReal.ofReal |k⁻¹| • volume := by
      calc
        _ = Measure.map (fun x : ℝ => k * x)
            (Measure.map (fun x : ℝ => x - c) volume) :=
          (Measure.map_map (by fun_prop) (by fun_prop)).symm
        _ = _ := by rw [map_sub_right_eq_self, Real.map_volume_mul_left hk.ne']
    have hs := lintegral_map (μ := volume) hG (show Measurable (fun x : ℝ => k * (x - c)) by fun_prop)
    rw [hmap, lintegral_smul_measure, smul_eq_mul,
      abs_of_pos (inv_pos.mpr hk)] at hs
    calc
      _ = ENNReal.ofReal k * ∫⁻ x : ℝ, G (k * (x - c)) := by
        rw [← lintegral_const_mul _
          (show Measurable (fun x : ℝ => G (k * (x - c))) from hG.comp (by fun_prop))]
        apply lintegral_congr
        intro x
        dsimp only [G]
        rw [mul_div_cancel_left₀ _ hk.ne', sub_add_cancel,
          abs_mul, abs_of_pos hk]
        rw [mul_left_comm (ENNReal.ofReal k) (f x), ← ENNReal.ofReal_mul hk.le]
        congr 1
        ring_nf
      _ = _ := by
        rw [← hs, ← mul_assoc, ← ENNReal.ofReal_mul hk.le,
          mul_inv_cancel₀ hk.ne', ENNReal.ofReal_one, one_mul]

)


end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
