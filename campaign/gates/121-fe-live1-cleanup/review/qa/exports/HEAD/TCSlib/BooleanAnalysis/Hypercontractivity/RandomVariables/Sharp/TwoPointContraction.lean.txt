/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.TwoPointCalculus
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.Parameters
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseDuality
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.OneBit
import Mathlib.Data.Real.ConjExponents

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp biased two-point inequalities

## Main definitions

This module introduces no new definitions.

## Main results

* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_two_point_le`:
  the sharp biased two-point inequality for arbitrary real inputs.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_two_point_le`:
  the same inequality expressed in the atom weight and sharp radius.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_two_point_extremizer`:
  an explicit nonconstant pair attaining equality with unit `p` moment.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_radius_le`:
  the universal scalar contraction forces the radius to be at most the sharp radius.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_forward_le`:
  the sharp forward two-to-q inequality for the same weighted pair.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_two_point_le_of_atom_bound`:
  the sharp conjugate bound from a lower bound on both atom masses, including equal masses.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.18(a)–(b) and 10.20(a)–(c), equations (10.34)–(10.35),
  and Theorem 10.18.
-/

namespace BooleanAnalysis.Hypercontractivity

namespace SharpDiscrete

/-- For `1 < p < 2` and positive `α < β` satisfying `α ^ p + β ^ p = 1`,
the sharp biased two-point inequality holds for arbitrary real inputs `u` and `v`,
with the coefficient from Exercise 10.20(a).
[OD14, Exercise 10.20(a)–(c), equations (10.34)–(10.35), Theorem 10.18]

**Proof sketch.** Apply the nonnegative two-point inequality to `|u|` and `|v|`.
The difference between its quadratic left-hand side and the signed quadratic
left-hand side is
`2 * α ^ p * β ^ p * (1 - r) * (|u| * |v| - u * v)`.
This is nonnegative because the bias coefficient satisfies `r < 1` and
`u * v ≤ |u * v| = |u| * |v|`. The right-hand sides agree, so the signed
inequality follows by transitivity. -/
theorem biased_two_point_le (p α β u v : ℝ)
    (hp_one : 1 < p) (hp_two : p < 2)
    (hα_pos : 0 < α) (hαβ : α < β)
    (hnorm : α ^ p + β ^ p = 1) :
    let r :=
      (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) / (α ^ 2 - β ^ 2)
    (α ^ p * u + β ^ p * v) ^ 2 +
        r * α ^ p * β ^ p * (u - v) ^ 2 ≤
      (α ^ p * |u| ^ p + β ^ p * |v| ^ p) ^ (2 / p) := by
  let r : ℝ :=
    (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) / (α ^ 2 - β ^ 2)
  have hr : r < 1 :=
    (bias_coefficient_pos_lt_one hp_one hp_two hα_pos hαβ).2
  have hβ_pos : 0 < β := lt_trans hα_pos hαβ
  have hdiff :
      0 ≤ 2 * α ^ p * β ^ p * (1 - r) * (|u| * |v| - u * v) := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact sub_nonneg.mpr hr.le
    · exact sub_nonneg.mpr (by simpa only [abs_mul] using le_abs_self (u * v))
  change
    (α ^ p * u + β ^ p * v) ^ 2 +
      r * α ^ p * β ^ p * (u - v) ^ 2 ≤ _
  calc
    (α ^ p * u + β ^ p * v) ^ 2 + r * α ^ p * β ^ p * (u - v) ^ 2 =
        (α ^ p * |u| + β ^ p * |v|) ^ 2 +
          r * α ^ p * β ^ p * (|u| - |v|) ^ 2 -
          2 * α ^ p * β ^ p * (1 - r) * (|u| * |v| - u * v) := by
      ring_nf
      simp only [sq_abs] <;> ring
    _ ≤ (α ^ p * |u| + β ^ p * |v|) ^ 2 +
        r * α ^ p * β ^ p * (|u| - |v|) ^ 2 :=
      sub_le_self _ hdiff
    _ ≤ (α ^ p * |u| ^ p + β ^ p * |v| ^ p) ^ (2 / p) :=
      nonnegative_biased_two_point_le p α β |u| |v|
        hp_one hp_two hα_pos hαβ hnorm (abs_nonneg u) (abs_nonneg v)

/-- The signed, weighted two-point inequality from `Lᵖ` to `L²`, with the sharp
discrete radius at the conjugate exponent `p / (p - 1)`.
[OD14, Exercise 10.20(a)-(c), equations (10.34)-(10.35), Theorem 10.18]

**Proof sketch.** Set `α = lambda ^ (1 / p)` and
`β = (1 - lambda) ^ (1 / p)`. Positivity and strict monotonicity of positive
powers give `0 < α < β`, while exponent cancellation gives
`α ^ p = lambda` and `β ^ p = 1 - lambda`. Apply `biased_two_point_le` to
these normalized parameters, then use `bias_coefficient_eq_radius_sq` to
identify its coefficient with the square of the sharp discrete radius. -/
theorem weighted_biased_two_point_le (p lambda u v : ℝ)
    (hp : 1 < p) (hp2 : p < 2)
    (hlambda : 0 < lambda) (hlambda_half : lambda < 1 / 2) :
    (lambda * u + (1 - lambda) * v) ^ (2 : ℕ) +
        (sharpDiscreteRadius (p / (p - 1)) lambda) ^ (2 : ℕ) *
          lambda * (1 - lambda) * (u - v) ^ (2 : ℕ) ≤
      (lambda * |u| ^ p + (1 - lambda) * |v| ^ p) ^ (2 / p) := by
  -- Express the bias weights as p-th powers.
  let α : ℝ := lambda ^ (1 / p)
  let β : ℝ := (1 - lambda) ^ (1 / p)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hβ0 : 0 < 1 - lambda := by linarith
  have hα : 0 < α := Real.rpow_pos_of_pos hlambda _
  have hαβ : α < β :=
    Real.rpow_lt_rpow (le_of_lt hlambda)
      (show lambda < 1 - lambda by linarith)
      (div_pos zero_lt_one hp0)
  have hαpow : α ^ p = lambda := by
    dsimp only [α]
    rw [one_div]
    exact Real.rpow_inv_rpow (le_of_lt hlambda) (ne_of_gt hp0)
  have hβpow : β ^ p = 1 - lambda := by
    dsimp only [β]
    rw [one_div]
    exact Real.rpow_inv_rpow (le_of_lt hβ0) (ne_of_gt hp0)
  have hnorm : α ^ p + β ^ p = 1 := by
    rw [hαpow, hβpow]
    ring
  have h := biased_two_point_le p α β u v hp hp2 hα hαβ hnorm
  have hr := bias_coefficient_eq_radius_sq hp hp2 hα hαβ hnorm
  dsimp only at h
  rw [hr] at h
  simpa only [hαpow, hβpow] using h

/--
For `1 < p < 2` and positive `α < β` with `α ^ p + β ^ p = 1`, the reciprocal
ratios are distinct, have weighted `p`-moment one, and attain equality in the
weighted quadratic expression at the sharp squared noise parameter.

[OD14, Exercise 10.20(g)–(h), equation (10.35), Theorem 10.18 (optimality)]

**Proof sketch.** Positivity and strict order distinguish the reciprocal ratios.
Division of positive real powers reduces the weighted `p`-moment to
`β ^ p + α ^ p`, which equals one by normalization. For the quadratic equality,
substitute the coefficient, rewrite `α ^ (2 - p)` and `β ^ (2 - p)` as squares
divided by their respective `p`-th powers, and clear the nonzero denominators.
Normalization then completes a polynomial identity.
-/
theorem biased_two_point_extremizer
    (p α β : ℝ)
    (hp_one : 1 < p) (hp_two : p < 2)
    (hα_pos : 0 < α) (hαβ : α < β)
    (hnorm : α ^ p + β ^ p = 1) :
    let u : ℝ := β / α
    let v : ℝ := α / β
    let r : ℝ :=
      (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
        (α ^ (2 : ℕ) - β ^ (2 : ℕ))
    u ≠ v ∧
      α ^ p * u ^ p + β ^ p * v ^ p = 1 ∧
      (α ^ p * u + β ^ p * v) ^ (2 : ℕ) +
        r * α ^ p * β ^ p * (u - v) ^ (2 : ℕ) = 1 := by
  dsimp only
  have hβ_pos : 0 < β := lt_trans hα_pos hαβ
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  have hαp_ne : α ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hα_pos p)
  have hβp_ne : β ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hβ_pos p)
  have hsq_ne : α ^ (2 : ℕ) - β ^ (2 : ℕ) ≠ 0 :=
    ne_of_lt (sub_neg.mpr ((sq_lt_sq₀ hα_pos.le hβ_pos.le).2 hαβ))
  refine ⟨?_, ?_, ?_⟩
  · exact ne_of_gt (lt_trans ((div_lt_one hβ_pos).2 hαβ)
      ((one_lt_div hα_pos).2 hαβ))
  · calc
      _ = β ^ p + α ^ p := by
        rw [Real.div_rpow hβ_pos.le hα_pos.le p,
          Real.div_rpow hα_pos.le hβ_pos.le p]
        field_simp [hαp_ne, hβp_ne] <;> ring
      _ = 1 := by linarith [hnorm]
  · -- Clearing denominators reduces the equality case to the square of the total mass.
    calc
      _ = (α ^ p + β ^ p) ^ (2 : ℕ) := by
        rw [Real.rpow_sub hβ_pos 2 p, Real.rpow_sub hα_pos 2 p]
        simp only [Real.rpow_two]
        field_simp [hα_ne, hβ_ne, hαp_ne, hβp_ne, hsq_ne] <;> ring
      _ = 1 := by rw [hnorm]; norm_num

/-- For `1 < p < 2` and `0 < lam < 1 / 2`, any nonnegative radius whose
weighted two-point quadratic contraction holds for every real pair `u, v`
is at most the sharp discrete radius at the conjugate exponent
`p / (p - 1)`.
[OD14, Theorem 10.18 (optimality), Exercise 10.20(g)-(h), equation (10.35)]

This states necessity for the scalar two-point inequality; no upper-bound
hypothesis on the candidate radius is required.

**Proof sketch.** Set `α = lam ^ (1 / p)` and
`β = (1 - lam) ^ (1 / p)`. Positive powers give `0 < α < β`,
`α ^ p = lam`, and `β ^ p = 1 - lam`. The established extremizer
`u = β / α`, `v = α / β` is positive and nonconstant, has weighted
`p`-moment one, and attains equality at the sharp coefficient. Identify
that coefficient with the squared sharp radius, and compare its equality
with the assumed inequality on this pair. Cancel the strictly positive
variance factor `lam * (1 - lam) * (u - v) ^ 2` to bound the candidate
radius squared. Nonnegativity of both radii yields the radius bound. -/
theorem weighted_biased_radius_le (p lam rho : ℝ)
    (hp_one : 1 < p) (hp_two : p < 2)
    (hlam : 0 < lam) (hlam_half : lam < 1 / 2)
    (hrho : 0 ≤ rho)
    (hcontraction : ∀ u v : ℝ,
      (lam * u + (1 - lam) * v) ^ (2 : ℕ) +
          rho ^ (2 : ℕ) * lam * (1 - lam) * (u - v) ^ (2 : ℕ) ≤
        (lam * |u| ^ p + (1 - lam) * |v| ^ p) ^ (2 / p)) :
    rho ≤ sharpDiscreteRadius (p / (p - 1)) lam := by
  -- Express the bias weights as normalized p-th powers.
  let α : ℝ := lam ^ (1 / p)
  let β : ℝ := (1 - lam) ^ (1 / p)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp_one
  have hlam_compl : 0 < 1 - lam := by linarith
  have hα_pos : 0 < α := Real.rpow_pos_of_pos hlam _
  have hβ_pos : 0 < β := Real.rpow_pos_of_pos hlam_compl _
  have hαβ : α < β :=
    Real.rpow_lt_rpow hlam.le
      (show lam < 1 - lam by linarith)
      (div_pos zero_lt_one hp_pos)
  have hαpow : α ^ p = lam := by
    dsimp only [α]
    rw [one_div]
    exact Real.rpow_inv_rpow hlam.le hp_pos.ne'
  have hβpow : β ^ p = 1 - lam := by
    dsimp only [β]
    rw [one_div]
    exact Real.rpow_inv_rpow hlam_compl.le hp_pos.ne'
  have hnorm : α ^ p + β ^ p = 1 := by
    rw [hαpow, hβpow]
    ring
  -- The established extremizer has unit moment and sharp quadratic equality.
  let u : ℝ := β / α
  let v : ℝ := α / β
  have hu_pos : 0 < u := div_pos hβ_pos hα_pos
  have hv_pos : 0 < v := div_pos hα_pos hβ_pos
  have hext := biased_two_point_extremizer p α β
    hp_one hp_two hα_pos hαβ hnorm
  dsimp only at hext
  have hcoefficient := bias_coefficient_eq_radius_sq
    hp_one hp_two hα_pos hαβ hnorm
  rw [hcoefficient, hαpow, hβpow] at hext
  have hmoment : lam * u ^ p + (1 - lam) * v ^ p = 1 := hext.2.1
  have hsharp :
      (lam * u + (1 - lam) * v) ^ (2 : ℕ) +
        sharpDiscreteRadius (p / (p - 1)) lam ^ (2 : ℕ) *
          lam * (1 - lam) * (u - v) ^ (2 : ℕ) = 1 := hext.2.2
  have hcandidate :
      (lam * u + (1 - lam) * v) ^ (2 : ℕ) +
        rho ^ (2 : ℕ) * lam * (1 - lam) * (u - v) ^ (2 : ℕ) ≤ 1 := by
    simpa only [abs_of_pos hu_pos, abs_of_pos hv_pos, hmoment, Real.one_rpow]
      using hcontraction u v
  -- Cancel the common mean square and the strictly positive variance.
  have hvariance : 0 < lam * (1 - lam) * (u - v) ^ (2 : ℕ) :=
    mul_pos (mul_pos hlam hlam_compl)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hext.1))
  have hcomparison :
      rho ^ (2 : ℕ) * (lam * (1 - lam) * (u - v) ^ (2 : ℕ)) ≤
        sharpDiscreteRadius (p / (p - 1)) lam ^ (2 : ℕ) *
          (lam * (1 - lam) * (u - v) ^ (2 : ℕ)) := by
    apply (add_le_add_iff_left ((lam * u + (1 - lam) * v) ^ (2 : ℕ))).mp
    simpa only [mul_assoc] using hcandidate.trans_eq hsharp.symm
  have hsquares :
      rho ^ (2 : ℕ) ≤ sharpDiscreteRadius (p / (p - 1)) lam ^ (2 : ℕ) :=
    (mul_le_mul_iff_left₀ hvariance).mp hcomparison
  have hradius : 0 ≤ sharpDiscreteRadius (p / (p - 1)) lam := by
    unfold sharpDiscreteRadius
    exact Real.sqrt_nonneg _
  exact (sq_le_sq₀ hrho hradius).mp hsquares

/-- For every real `q > 2`, bias `0 < lam < 1 / 2`, and real inputs `u, v`,
the affine noise transform at the sharp discrete radius has squared weighted
`Lᑫ` norm at most the squared weighted `L²` norm of the original pair.
[OD14, Proposition 9.19, Exercise 10.20(b), equation (10.35), Theorem 10.18]

**Proof sketch.** Put `p = q / (q - 1)`. Conjugacy gives `1 < p < 2`
and `p / (p - 1) = q`. On the finite space `Bool`, assign weights
`lam` and `1 - lam`. Apply the established weighted two-point inequality
to every real dual test function. The mean-square-plus-variance expression
equals its noisy second moment by the quadratic identity
`rho² * E[g²] + (1 - rho²) * E[g]²`.
Finite weighted noise duality therefore gives the squared `Lᑫ` bound
for the input pair. Evaluate both finite sums to obtain the displayed
inequality. -/
theorem weighted_biased_forward_le (q lam u v : ℝ)
    (hq : 2 < q) (hlam : 0 < lam) (hlam_half : lam < 1 / 2) :
    let rho : ℝ := sharpDiscreteRadius q lam
    let m : ℝ := lam * u + (1 - lam) * v
    (lam * |rho * u + (1 - rho) * m| ^ q +
        (1 - lam) * |rho * v + (1 - rho) * m| ^ q) ^ (2 / q) ≤
      lam * u ^ (2 : ℕ) + (1 - lam) * v ^ (2 : ℕ) := by
  dsimp only
  let p : ℝ := q / (q - 1)
  let w : Bool → ℝ := fun b => if b then lam else 1 - lam
  let f : Bool → ℝ := fun b => if b then u else v
  have hconj : Real.HolderConjugate q p :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith : 1 < q)).2 rfl
  have hp_two : p < 2 := by
    dsimp only [p]
    apply (div_lt_iff₀ (by linarith : 0 < q - 1)).2
    linarith
  have hw_nonneg : ∀ b : Bool, 0 ≤ w b := by
    intro b
    cases b <;> simp [w] <;> linarith
  have hw : Finset.univ.sum w = 1 := by
    simp [w, Fintype.sum_bool] <;> ring
  have hbound := finite_noise_duality w hw_nonneg hw q hq
    (sharpDiscreteRadius q lam) (by
      intro g
      simp [w, Fintype.sum_bool]
      have hscalar := weighted_biased_two_point_le p lam (g true) (g false)
        hconj.symm.lt hp_two hlam hlam_half
      rw [← hconj.symm.conjugate_eq] at hscalar
      calc
        _ = (lam * g true + (1 - lam) * g false) ^ (2 : ℕ) +
            sharpDiscreteRadius q lam ^ (2 : ℕ) *
              lam * (1 - lam) * (g true - g false) ^ (2 : ℕ) := by ring
        _ ≤ _ := hscalar) f
  simpa [w, f, Fintype.sum_bool] using hbound

/-- For `q > 2`, `0 < lam < 1 / 2`, and two atom masses `gamma` and
`1 - gamma` each at least `lam`, the sharp radius at `lam` gives the
weighted `Lᵖ` to `L²` two-point inequality for arbitrary real inputs,
where `p = q / (q - 1)`. The squared output is the squared weighted mean
plus the squared radius times the weighted variance.

This is the lower-atom-bound formulation of [OD14, Theorem 10.18],
using [OD14, Exercise 10.18(a)] and [OD14, Exercise 10.20(a)–(c)].
Radius monotonicity allows `lam` to be a lower bound for the smaller mass.
The balanced case `gamma = 1 / 2` is included using the balanced radius
comparison. The inputs may be signed or equal.

**Proof sketch.** The conjugate exponent lies strictly between one and two.
When `gamma < 1 / 2`, apply the sharp biased two-point inequality at
`gamma`. Radius monotonicity and the nonnegative variance factor allow
decreasing its radius to the radius at `lam`. When `gamma = 1 / 2`,
apply the one-bit two-point inequality to the half-sum and half-difference
of the inputs, using the balanced squared-radius bound. Square the
inequality between nonnegative quantities and combine real-power exponents.
When `gamma > 1 / 2`, exchange the inputs and replace the mass by
`1 - gamma`, reducing to the first case. -/
theorem weighted_two_point_le_of_atom_bound (q lam gamma u v : ℝ)
    (hq : 2 < q) (hlam_pos : 0 < lam) (hlam_lt_half : lam < 1 / 2)
    (hlam_le_gamma : lam ≤ gamma) (hgamma_le : gamma ≤ 1 - lam) :
    let p : ℝ := q / (q - 1)
    let rho : ℝ := sharpDiscreteRadius q lam
    (gamma * u + (1 - gamma) * v) ^ (2 : ℕ) +
        rho ^ (2 : ℕ) * gamma * (1 - gamma) * (u - v) ^ (2 : ℕ) ≤
      (gamma * |u| ^ p + (1 - gamma) * |v| ^ p) ^ (2 / p) := by
  intro p rho
  have hconj : Real.HolderConjugate q p :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith : 1 < q)).2 rfl
  have hp_two : p < 2 := by
    dsimp only [p]
    apply (div_lt_iff₀ (by linarith : 0 < q - 1)).2
    linarith
  have hrho_pos : 0 < rho :=
    (radius_pos_lt_one q lam hq hlam_pos hlam_lt_half).1
  have hrho_balanced : rho ^ (2 : ℕ) ≤ p - 1 := by
    convert radius_sq_le_balanced q lam hq hlam_pos hlam_lt_half using 1
    dsimp only [p]
    field_simp [(show q - 1 ≠ 0 by linarith)] <;> ring
  have hhalf (d x y : ℝ) (hd : lam ≤ d) (hdhalf : d ≤ 1 / 2) :
      (d * x + (1 - d) * y) ^ (2 : ℕ) +
          rho ^ (2 : ℕ) * d * (1 - d) * (x - y) ^ (2 : ℕ) ≤
        (d * |x| ^ p + (1 - d) * |y| ^ p) ^ (2 / p) := by
    have hdpos : 0 < d := lt_of_lt_of_le hlam_pos hd
    rcases lt_or_eq_of_le hdhalf with hdlt | rfl
    · -- Below one half, decrease the sharp radius using bias monotonicity.
      have hscalar := weighted_biased_two_point_le p d x y
        hconj.symm.lt hp_two hdpos hdlt
      rw [← hconj.symm.conjugate_eq] at hscalar
      have hradius :=
        (sq_le_sq₀ hrho_pos.le
          (radius_pos_lt_one q d hq hdpos hdlt).1.le).2
          (radius_mono_bias q lam d hq hlam_pos hd hdlt)
      refine le_trans ?_ hscalar
      simpa only [mul_assoc] using
        add_le_add_left
          (mul_le_mul_of_nonneg_right hradius
            (mul_nonneg (mul_nonneg hdpos.le (by linarith)) (sq_nonneg (x - y))))
          ((d * x + (1 - d) * y) ^ (2 : ℕ))
    · -- At one half, square the balanced one-bit inequality.
      let Q : ℝ := ((x + y) / 2) ^ (2 : ℕ) +
        rho ^ (2 : ℕ) * ((x - y) / 2) ^ (2 : ℕ)
      let M : ℝ := (|x| ^ p + |y| ^ p) / 2
      have hQ : 0 ≤ Q := by
        dsimp only [Q]
        positivity
      have hM : 0 ≤ M := by
        dsimp only [M]
        positivity
      have hbit : Q ^ ((1 : ℝ) / 2) ≤ M ^ ((1 : ℝ) / p) := by
        simpa only [Q, M,
          show (x + y) / 2 + (x - y) / 2 = x by ring,
          show (x + y) / 2 - (x - y) / 2 = y by ring] using
          _root_.BooleanAnalysis.Hypercontractivity.two_point_ineq ((x + y) / 2) ((x - y) / 2)
            p rho hconj.symm.lt.le hp_two.le hrho_pos.le hrho_balanced
      have hsq :=
        (sq_le_sq₀ (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hM _)).2 hbit
      rw [show (1 : ℝ) / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.rpow_inv_natCast_pow hQ (by decide : (2 : ℕ) ≠ 0),
        ← Real.rpow_mul_natCast hM (1 / p) 2] at hsq
      norm_num only [Nat.cast_ofNat] at hsq
      rw [show (1 / p) * (2 : ℝ) = 2 / p by ring] at hsq
      convert hsq using 1
      · dsimp only [Q]
        ring
      · congr 1
        dsimp only [M]
        ring
  by_cases hgamma_half : gamma ≤ 1 / 2
  · exact hhalf gamma u v hlam_le_gamma hgamma_half
  · -- Above one half, exchange the two atoms.
    have hswap := hhalf (1 - gamma) v u (by linarith) (by linarith)
    convert hswap using 1
    · ring
    · congr 1
      ring

end SharpDiscrete

end BooleanAnalysis.Hypercontractivity
